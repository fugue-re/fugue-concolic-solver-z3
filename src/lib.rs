pub use z3;

use z3::ast::{Ast, BV, Int};
use z3::{Context, Model, SatResult, Solver};

use fugue::bv::BitVec;
use fugue::ir::Translator;
use fugue::ir::il::ecode::{BinOp, BinRel, Cast, UnOp, UnRel, Var};
use fugue::ir::il::traits::*;

use fugue_concolic::backend::ValueSolver;
use fugue_concolic::expr::{Expr, SymExpr, IVar, VisitRef};

use fxhash::FxHashMap as HashMap;

use std::sync::Arc;

const SOLVER_LIMIT: usize = 100;

#[derive(Clone)]
pub struct SolverContext<'ctx> {
    context: &'ctx Context,
    solver: Arc<Solver<'ctx>>,
    vars: HashMap<Var, BV<'ctx>>,
    ivars: HashMap<IVar, BV<'ctx>>,
    translator: Arc<Translator>,
    limit: usize,
}

impl<'ctx> SolverContext<'ctx> {
    pub fn new(context: &'ctx Context, translator: Arc<Translator>) -> Self {
        Self::new_with(context, translator, SOLVER_LIMIT)
    }

    pub(crate) fn context(&self) -> &'ctx Context {
        self.context
    }

    pub fn new_with(context: &'ctx Context, translator: Arc<Translator>, limit: usize) -> Self {
        Self {
            context,
            solver: Arc::new(Solver::new(&context)),
            vars: HashMap::default(),
            ivars: HashMap::default(),
            translator,
            limit,
        }
    }

    pub fn var(&mut self, var: &Var) -> BV<'ctx> {
        if let Some(bv) = self.vars.get(var).cloned() {
            bv
        } else {
            let bv = BV::fresh_const(self.context, "var", var.bits() as u32);
            self.vars.insert(var.to_owned(), bv.clone());
            bv
        }
    }

    pub fn ivar(&mut self, var: &IVar) -> BV<'ctx> {
        if let Some(bv) = self.ivars.get(var).cloned() {
            bv
        } else {
            let bv = BV::fresh_const(self.context, "ivar", var.bits() as u32);
            self.ivars.insert(var.to_owned(), bv.clone());
            bv
        }
    }

    pub fn solver(&self) -> &Solver {
        &*self.solver
    }

    pub fn translator(&self) -> &Translator {
        &*self.translator
    }

    pub fn is_sat(&mut self, constraints: &[SymExpr]) -> bool {
        constraints.is_empty() || {
            self.solver.push();

            for constraint in constraints.iter() {
                let c = &constraint.ast(self).extract(0, 0)._eq(&BV::from_u64(self.context, 1, 1));
                self.solver.assert(&c);
            }

            let is_sat = self.solver.check() == SatResult::Sat;

            self.solver.pop(1);

            is_sat
        }
    }

    pub fn limit(&self) -> usize {
        self.limit
    }
}

struct ToAst<'a, 'c> {
    value: Option<BV<'c>>,
    ctxt: &'a mut SolverContext<'c>,
}

impl<'a, 'c> ToAst<'a, 'c> {
    fn new(ctxt: &'a mut SolverContext<'c>) -> Self {
        Self {
            value: None,
            ctxt,
        }
    }

    fn var(&mut self, var: &Var) -> BV<'c> {
        self.ctxt.var(var)
    }

    fn ivar(&mut self, ivar: &IVar) -> BV<'c> {
        self.ctxt.ivar(ivar)
    }

    fn context(&self) -> &'c Context {
        self.ctxt.context()
    }

    fn value(&mut self) -> BV<'c> {
        self.value.take().unwrap()
    }
}

impl<'a, 'c, 'ecode> VisitRef<'ecode> for ToAst<'a, 'c> {
    fn visit_val_ref(&mut self, bv: &'ecode BitVec) {
        self.value = Some(if bv.bits() <= 64 {
            BV::from_u64(self.context(), bv.to_u64().unwrap(), bv.bits() as u32)
        } else { // less than ideal...
            let s = format!("{}", bv);
            let s1 = s.rsplit_once(':')
                .map(|(s1, _)| s1)
                .unwrap_or(&s);

            let bvi = Int::from_str(self.context(), s1).unwrap();
            BV::from_int(&bvi, bv.bits() as u32)
        });
    }

    fn visit_var_ref(&mut self, var: &'ecode Var) {
        self.value = Some(self.var(var));
    }

    fn visit_ivar_ref(&mut self, ivar: &'ecode IVar) {
        self.value = Some(self.ivar(ivar));
    }

    fn visit_unrel_ref(&mut self, op: UnRel, _expr: &'ecode SymExpr) {
        panic!("unsupported operator: {:?}", op)
    }

    fn visit_unop_ref(&mut self, op: UnOp, expr: &'ecode SymExpr) {
        self.visit_expr_ref(expr);

        let value = self.value();
        self.value = Some(match op {
            UnOp::NOT => if expr.is_bool() {
                value.extract(0, 0).bvnot().zero_ext(7)
            } else {
                value.bvnot()
            },
            UnOp::NEG => value.bvneg(),
            UnOp::ABS => {
                let c = value.bvsge(&BV::from_u64(self.context(), 0, value.get_size()));
                c.ite(&value, &value.bvneg())
            },
            UnOp::POPCOUNT => {
                let bv0 = BV::from_u64(self.context(), 0, value.get_size());
                let bv1 = BV::from_u64(self.context(), 1, value.get_size());

                let mut cnt = BV::from_u64(self.context(), 0, value.get_size());

                // This is horrible.
                // TODO(slt): rewrite... Hacker's Delight
                for i in 0..value.get_size() {
                    let m = value.bvand(&bv1.bvshl(&BV::from_u64(self.context(), i as u64, value.get_size())));
                    cnt =  m._eq(&bv0).ite(&cnt, &cnt.bvadd(&bv1));
                }

                cnt
            },
            UnOp::SQRT |
            UnOp::FLOOR |
            UnOp::ROUND |
            UnOp::CEILING => panic!("unsupported operator: {:?}", op)
        })
    }

    fn visit_binrel_ref(&mut self, op: BinRel, lexpr: &'ecode SymExpr, rexpr: &'ecode SymExpr) {
        self.visit_expr_ref(lexpr);
        let lvalue = self.value();

        self.visit_expr_ref(rexpr);
        let rvalue = self.value();

        let bv0 = BV::from_u64(self.context(), 0, 8);
        let bv1 = BV::from_u64(self.context(), 1, 8);

        // NOTE: we uext by 7 to get byte-sized bools
        self.value = Some(match op {
            BinRel::EQ => lvalue._eq(&rvalue).ite(&bv1, &bv0),
            BinRel::NEQ => lvalue._eq(&rvalue).not().ite(&bv1, &bv0),
            BinRel::LT => lvalue.bvult(&rvalue).ite(&bv1, &bv0),
            BinRel::SLT => lvalue.bvslt(&rvalue).ite(&bv1, &bv0),
            BinRel::LE => lvalue.bvule(&rvalue).ite(&bv1, &bv0),
            BinRel::SLE => lvalue.bvsle(&rvalue).ite(&bv1, &bv0),
            BinRel::CARRY => lvalue.bvadd_no_overflow(&rvalue, false).ite(&bv1, &bv0),
            BinRel::SCARRY => lvalue.bvadd_no_overflow(&rvalue, true).ite(&bv1, &bv0),
            BinRel::SBORROW => lvalue.bvsub_no_underflow(&rvalue, true).ite(&bv1, &bv0),
        })
    }

    fn visit_binop_ref(&mut self, op: BinOp, lexpr: &'ecode SymExpr, rexpr: &'ecode SymExpr) {
        self.visit_expr_ref(lexpr);
        let lvalue = self.value();

        self.visit_expr_ref(rexpr);
        let rvalue = self.value();

        let is_bool = lexpr.is_bool() || rexpr.is_bool();

        self.value = Some(match op {
            BinOp::ADD => lvalue.bvadd(&rvalue),
            BinOp::SUB => lvalue.bvsub(&rvalue),
            BinOp::DIV => lvalue.bvudiv(&rvalue),
            BinOp::SDIV => lvalue.bvsdiv(&rvalue),
            BinOp::MUL => lvalue.bvmul(&rvalue),
            BinOp::REM => lvalue.bvurem(&rvalue),
            BinOp::SREM => lvalue.bvsrem(&rvalue),
            BinOp::AND => if is_bool { lvalue.extract(0, 0).bvand(&rvalue.extract(0, 0)).zero_ext(7) } else { lvalue.bvand(&rvalue) },
            BinOp::OR => if is_bool { lvalue.extract(0, 0).bvor(&rvalue.extract(0, 0)).zero_ext(7) } else { lvalue.bvor(&rvalue) },
            BinOp::XOR => if is_bool { lvalue.extract(0, 0).bvxor(&rvalue.extract(0, 0)).zero_ext(7) } else { lvalue.bvxor(&rvalue) },
            BinOp::SHL => lvalue.bvshl(&rvalue),
            BinOp::SHR => lvalue.bvlshr(&rvalue),
            BinOp::SAR => lvalue.bvashr(&rvalue),
        })
    }

    fn visit_ite_ref(&mut self, cond: &'ecode SymExpr, texpr: &'ecode SymExpr, fexpr: &'ecode SymExpr) {
        self.visit_expr_ref(cond);
        let cvalue = self.value();

        self.visit_expr_ref(texpr);
        let lvalue = self.value();

        self.visit_expr_ref(fexpr);
        let rvalue = self.value();

        let bv1 = BV::from_u64(self.context(), 1, 1);
        self.value = Some(cvalue.extract(0, 0)._eq(&bv1).ite(&lvalue, &rvalue))
    }

    fn visit_concat_ref(&mut self, lexpr: &'ecode SymExpr, rexpr: &'ecode SymExpr) {
        self.visit_expr_ref(lexpr);
        let lvalue = self.value();

        self.visit_expr_ref(rexpr);
        let rvalue = self.value();

        self.value = Some(lvalue.concat(&rvalue))
    }

    fn visit_extract_low_ref(&mut self, expr: &'ecode SymExpr, bits: u32) {
        self.visit_expr_ref(&expr);
        let value = self.value();

        self.value = Some(value.extract(bits - 1, 0))
    }

    fn visit_extract_high_ref(&mut self, expr: &'ecode SymExpr, bits: u32) {
        self.visit_expr_ref(&expr);
        let value = self.value();

        let hbit = expr.bits() as u32;
        self.value = Some(value.extract(hbit - 1, hbit - bits))
    }

    fn visit_extract_ref(&mut self, expr: &'ecode SymExpr, lsb: u32, msb: u32) {
        self.visit_expr_ref(&expr);
        let value = self.value();

        self.value = Some(value.extract(msb - 1, lsb))
    }

    fn visit_cast_ref(&mut self, expr: &'ecode SymExpr, cast: &'ecode Cast) {
        self.visit_expr_ref(&expr);
        let value = self.value();

        self.value = Some(match cast {
            Cast::Bool => value.extract(0, 0).zero_ext(7),
            Cast::Signed(bits) => if expr.bits() < *bits as u32 {
                value.sign_ext((*bits as u32 - expr.bits()) as u32)
            } else if expr.bits() > *bits as u32 {
                value.extract(*bits as u32 - 1, 0)
            } else {
                value
            },
            Cast::Unsigned(bits) | Cast::Pointer(_, bits) => if expr.bits() < *bits as u32 {
                value.zero_ext((*bits as u32 - expr.bits()) as u32)
            } else if expr.bits() > *bits as u32 {
                value.extract(*bits as u32 - 1, 0)
            } else {
                value
            },
            _ => panic!("unsupported cast: {:?}", cast)
        })
    }
}

impl<'ctx> ValueSolver<'ctx> for SolverContext<'ctx> {
    type Value = BV<'ctx>;

    fn ast(&mut self, expr: &SymExpr) -> BV<'ctx> {
        let mut visitor = ToAst::new(self);
        visitor.visit_expr_ref(expr);
        visitor.value()
    }

    fn solve(&mut self, expr: &SymExpr, constraints: &[SymExpr]) -> Option<BitVec> {
        let nx = expr.simplify();
        if let Expr::Val(nx) = &*nx {
            Some(nx.clone())
        } else {
            self.solver().push();

            let bv1 = BV::from_u64(self.context(), 1, 1);

            for constraint in constraints.iter() {
                let c = &constraint.ast(self).extract(0, 0)._eq(&bv1);
                self.solver().assert(&c);
            }

            let ast = nx.ast(self);
            let var = BV::fresh_const(self.context(), "soln", ast.get_size());

            self.solver().assert(&var._eq(&ast));

            let nx = if self.solver().check() == SatResult::Sat {
                Some(bv_from_solution(
                        &self.solver().get_model().unwrap(),
                        &var,
                        nx.bits()).1)
            } else {
                None
            };

            self.solver().pop(1);

            nx
        }
    }

    fn solve_many(&mut self, expr: &SymExpr, constraints: &[SymExpr]) -> Vec<BitVec> {
        let nx = expr.simplify();
        if let Expr::Val(nx) = &*nx {
            vec![nx.clone()]
        } else {
            self.solver().push();

            let bv1 = BV::from_u64(self.context(), 1, 1);

            for constraint in constraints.iter() {
                let c = &constraint.ast(self).extract(0, 0)._eq(&bv1);
                self.solver().assert(&c);
            }

            let ast = nx.ast(self);
            let var = BV::fresh_const(self.context(), "ivar", ast.get_size());

            self.solver().assert(&var._eq(&ast));

            let mut acc = Vec::with_capacity(self.limit());
            while self.solver().check() == SatResult::Sat && acc.len() < self.limit() {
                let (bv, bvv) = bv_from_solution(
                    &self.solver().get_model().unwrap(),
                    &var,
                    nx.bits(),
                );
                acc.push(bvv);

                self.solver().assert(&var._eq(&bv).not());
            }

            self.solver().pop(1);
            acc
        }
    }

    fn minimise(&mut self, expr: &SymExpr, constraints: &[SymExpr]) -> Option<BitVec> {
        let nx = expr.simplify();
        if let Expr::Val(nx) = &*nx {
            Some(nx.clone())
        } else {
            self.solver().push();

            let bv1 = BV::from_u64(self.context(), 1, 1);

            for constraint in constraints.iter() {
                let c = &constraint.ast(self).extract(0, 0)._eq(&bv1);
                self.solver().assert(&c);
            }

            let ast = nx.ast(self);
            let var = BV::fresh_const(self.context(), "ivar", ast.get_size());

            self.solver().assert(&var._eq(&ast));

            let bits = expr.bits();

            let mut low = BitVec::zero(bits as usize);
            let mut high = BitVec::one(bits as usize) << (bits - 1);
            let two = BitVec::from_u32(2, bits as usize);

            while high != low {
                let mut assumption = var.bvult(&SymExpr::val(high.clone()).ast(self));
                while self.solver().check_assumptions(&[assumption]) == SatResult::Sat && high != low {
                    high = &low + &(&(&high - &low) / &two);
                    assumption = var.bvult(&SymExpr::val(high.clone()).ast(self));
                }

                let tmp = high.clone();
                high = &high + &(&(&high - &low) / &two);
                low = tmp;
            }

            self.solver().pop(1);

            Some(low)
        }
    }

    fn maximise(&mut self, expr: &SymExpr, constraints: &[SymExpr]) -> Option<BitVec> {
        let nx = expr.simplify();
        if let Expr::Val(nx) = &*nx {
            Some(nx.clone())
        } else {
            self.solver().push();

            let bv1 = BV::from_u64(self.context(), 1, 1);

            for constraint in constraints.iter() {
                let c = &constraint.ast(self).extract(0, 0)._eq(&bv1);
                self.solver().assert(&c);
            }

            let ast = nx.ast(self);
            let var = BV::fresh_const(self.context(), "ivar", ast.get_size());

            self.solver().assert(&var._eq(&ast));

            let bits = expr.bits();

            let mut low = BitVec::zero(bits as usize);
            let mut high = BitVec::one(bits as usize) << (bits - 1);
            let two = BitVec::from_u32(2, bits as usize);

            while high != low {
                let mut assumption = var.bvuge(&SymExpr::val(high.clone()).ast(self));
                while self.solver().check_assumptions(&[assumption]) == SatResult::Sat && high != low {
                    high = &low + &(&(&high - &low) / &two);
                    assumption = var.bvuge(&SymExpr::val(high.clone()).ast(self));
                }

                let tmp = high.clone();
                high = &high + &(&(&high - &low) / &two);
                low = tmp;
            }

            self.solver().pop(1);

            Some(low)
        }
    }

    fn is_sat(&mut self, constraints: &[SymExpr]) -> bool {
        constraints.is_empty() || {
            self.solver().push();

            for constraint in constraints.iter() {
                let c = &constraint.ast(self).extract(0, 0)._eq(&BV::from_u64(self.context(), 1, 1));
                self.solver().assert(&c);
            }

            let is_sat = self.solver().check() == SatResult::Sat;

            self.solver().pop(1);

            is_sat
        }
    }
}

fn bv_from_solution<'ctx>(soln: &Model<'ctx>, t: &BV<'ctx>, bits: u32) -> (BV<'ctx>, BitVec) {
    let value = soln.eval(t, false).expect("eval");
    let bits = bits as usize;
    let bvv = if let Some(v) = value.as_u64() {
        BitVec::from_u64(v, bits)
    } else {
        // fml
        let s = format!("{}:{}", value, bits);
        let s1 = s.strip_prefix("#x").unwrap_or(&s);
        BitVec::from_str_radix(s1, 16).unwrap()
    };
    (value, bvv)
}
