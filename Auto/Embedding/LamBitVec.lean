import Auto.Embedding.LamConv
import Std.Data.Int.Lemmas
import Std.Data.Fin.Lemmas

namespace Auto.Embedding.Lam

namespace BitVec

  open Std.BitVec
  
  theorem ofNat_add (n a b : Nat) : (a + b)#n = a#n + b#n := by
    apply congrArg (f:=Std.BitVec.ofFin); apply Fin.eq_of_val_eq
    dsimp [Fin.ofNat']; rw [Nat.add_mod]; rfl
  
  theorem ofNat_mod_pow2 (n a : Nat) : (a % (2 ^ n))#n = a#n := by
    apply congrArg (f:=Std.BitVec.ofFin); apply Fin.eq_of_val_eq
    dsimp [Fin.ofNat']; apply Nat.mod_mod
  
  theorem ofNat_mul (n a b : Nat) : (a * b)#n = a#n * b#n := by
    apply congrArg (f:=Std.BitVec.ofFin); apply Fin.eq_of_val_eq
    dsimp [Fin.ofNat']; rw [Nat.mul_mod]; rfl

end BitVec

theorem LamEquiv.bvofNat :
  LamEquiv lval lctx (.base (.bv n)) (.mkBvofNat n (.mkNatVal i)) (.base (.bvVal' n i)) :=
  ⟨.mkBvofNat (.ofBase (.ofNatVal' i)), .ofBase (.ofBvVal' n i), fun _ => rfl⟩

theorem LamEquiv.bvofNat_bvtoNat
  (wft : LamWF lval.toLamTyVal ⟨lctx, t, .base (.bv n)⟩) :
  LamEquiv lval lctx (.base (.bv m))
    (.mkBvofNat m (.mkBvUOp n (.bvtoNat n) t))
    (.app (.base (.bv n)) (.base (.bvzeroExtend' n m)) t) :=
  ⟨.mkBvofNat (.mkBvUOp (.ofBvtoNat n) wft),
   .ofApp _ (.ofBase (.ofBvzeroExtend' n m)) wft, fun lctxTerm => rfl⟩

theorem LamEquiv.bvofNat_nadd
  (wfa : LamWF lval.toLamTyVal ⟨lctx, a, .base .nat⟩)
  (wfb : LamWF lval.toLamTyVal ⟨lctx, b, .base .nat⟩) :
  LamEquiv lval lctx (.base (.bv n))
    (.mkBvofNat n (.mkNatBinOp .nadd a b))
    (.mkBvBinOp n (.bvadd n) (.mkBvofNat n a) (.mkBvofNat n b)) :=
  ⟨.mkBvofNat (.mkNatBinOp .ofNadd wfa wfb),
   .mkBvBinOp (.ofBvadd _) (.mkBvofNat wfa) (.mkBvofNat wfb), fun lctxTerm => by
      apply GLift.down.inj; apply BitVec.ofNat_add⟩

theorem LamEquiv.bvofNat_nmul
  (wfa : LamWF lval.toLamTyVal ⟨lctx, a, .base .nat⟩)
  (wfb : LamWF lval.toLamTyVal ⟨lctx, b, .base .nat⟩) :
  LamEquiv lval lctx (.base (.bv n))
    (.mkBvofNat n (.mkNatBinOp .nmul a b))
    (.mkBvBinOp n (.bvmul n) (.mkBvofNat n a) (.mkBvofNat n b)) :=
  ⟨.mkBvofNat (.mkNatBinOp .ofNmul wfa wfb),
   .mkBvBinOp (.ofBvmul _) (.mkBvofNat wfa) (.mkBvofNat wfb), fun lctxTerm => by
      apply GLift.down.inj; apply BitVec.ofNat_mul⟩

inductive BVCastType where
  | ofNat : Nat → BVCastType
  | ofInt : Nat → BVCastType
  | none

def LamTerm.applyBVCast (ct : BVCastType) (t : LamTerm) : LamTerm :=
  match ct with
  | .ofNat n => mkBvofNat n t
  | .ofInt n => mkBvofInt n t
  | .none    => t

def LamTerm.pushBVCast (ct : BVCastType) (t : LamTerm) : LamTerm :=
  match ct with
  | .ofNat n =>
    match t with
    | .base (.ncst (.natVal i)) => .base (.bvcst (.bvVal n i))
    | .app _ (.base (.bvcst (.bvtoNat m))) arg =>
      .app (.base (.bv m)) (.base (.bvzeroExtend' m n)) (pushBVCast .none arg)
    | .app _ (.app _ (.base (.ncst .nadd)) lhs) rhs =>
      mkBvBinOp n (.bvadd n) (pushBVCast (.ofNat n) lhs) (pushBVCast (.ofNat n) rhs)
    | .app _ (.app _ (.base (.ncst .nmul)) lhs) rhs =>
      mkBvBinOp n (.bvmul n) (pushBVCast (.ofNat n) lhs) (pushBVCast (.ofNat n) rhs)
    | _ => mkBvofNat n t
  -- Not implemented
  | .ofInt n => mkBvofInt n t
  | .none =>
    match t with
    | .lam s body => .lam s (pushBVCast .none body)
    | .app _ (.base (.bvcst (.bvofNat n))) t' => pushBVCast (.ofNat n) t'
    | .app _ (.base (.bvcst (.bvofInt n))) t' => pushBVCast (.ofInt n) t'
    | .app s fn arg => .app s (pushBVCast .none fn) (pushBVCast .none arg)
    | _ => t

theorem LamTerm.maxEVarSucc_pushBVCast : maxEVarSucc (pushBVCast ct t) = maxEVarSucc t := by
  generalize tl' : t.size = l; have tl : t.size ≤ l := by cases tl'; exact .refl
  clear tl'
  induction l generalizing t ct <;>
    try apply False.elim (LamTerm.size_ne_zero (Nat.le_zero.mp tl))
  case succ l IH =>
    cases t <;> try (cases ct <;> rfl)
    case base b =>
      cases b <;> try (cases ct <;> rfl)
      case ncst nc =>
        cases nc <;> cases ct <;> rfl
    case lam s body =>
      cases ct <;> try apply Nat.max_zero_left
      case none =>
        dsimp [pushBVCast, maxEVarSucc]; apply IH
        apply Nat.le_of_succ_le_succ tl
    case app s fn arg =>
      cases ct
      case ofNat m =>
        cases fn <;> try apply Nat.max_zero_left
        case base b =>
          cases b <;> try apply Nat.max_zero_left
          case bvcst bvc =>
            cases bvc <;> try apply Nat.max_zero_left
            case bvtoNat =>
              dsimp [pushBVCast, maxEVarSucc]; rw [IH (t:=arg)]
              apply Nat.le_of_succ_le_succ (Nat.le_trans LamTerm.size_app_gt_size_arg tl)
        case app s fn arg₁ =>
          cases fn <;> try apply Nat.max_zero_left
          case base b =>
            cases b <;> try apply Nat.max_zero_left
            case ncst nc =>
              cases nc <;> (try apply Nat.max_zero_left) <;> (
                dsimp [pushBVCast, maxEVarSucc]
                rw [IH (t:=arg₁) (Nat.le_of_succ_le_succ (Nat.le_trans (Nat.le_trans
                  LamTerm.size_app_gt_size_arg LamTerm.size_app_ge_size_fn) tl))]
                rw [IH (t:=arg) (Nat.le_of_succ_le_succ (Nat.le_trans
                  LamTerm.size_app_gt_size_arg tl))])              
      case ofInt m => apply Nat.max_zero_left
      case none =>
        cases fn <;> try (
          dsimp [maxEVarSucc, pushBVCast]; rw [IH (t:=arg) (Nat.le_of_succ_le_succ (
            Nat.le_trans LamTerm.size_app_gt_size_arg tl))])
        case base b =>
          cases b <;> try (
            dsimp [maxEVarSucc, pushBVCast]; rw [IH (t:=arg) (Nat.le_of_succ_le_succ (
              Nat.le_trans LamTerm.size_app_gt_size_arg tl))])
          case bvcst bvc =>
            cases bvc <;> dsimp [maxEVarSucc, pushBVCast] <;> rw [IH (t:=arg) (Nat.le_of_succ_le_succ (
                Nat.le_trans LamTerm.size_app_gt_size_arg tl))]
            case bvofNat => rw [Nat.max, Nat.max_zero_left]
            case bvofInt => rw [Nat.max, Nat.max_zero_left]
        case lam s body =>
          rw [IH (t:=body)]; apply Nat.le_of_succ_le_succ (Nat.le_trans _ tl)
          apply LamTerm.size_app_ge_size_fn (fn:=.lam s body)
        case app s fn arg =>
          rw [IH (t:=.app s fn arg)]; rfl
          apply Nat.le_of_succ_le_succ (Nat.le_trans _ tl)
          apply LamTerm.size_app_gt_size_fn (fn:=.app s fn arg)

theorem LamTerm.evarEquiv_pushBVCast : evarEquiv (fun t => pushBVCast ct t) := by
  intro t t' heq; cases heq; apply maxEVarSucc_pushBVCast

theorem LamEquiv.pushBVCast
  (wft : LamWF lval.toLamTyVal ⟨lctx, LamTerm.applyBVCast ct t, s⟩) :
  LamEquiv lval lctx s (t.applyBVCast ct) (t.pushBVCast ct) := by
  generalize tl' : t.size = l; have tl : t.size ≤ l := by cases tl'; exact .refl
  clear tl'
  induction l generalizing t s ct lctx <;>
    try apply False.elim (LamTerm.size_ne_zero (Nat.le_zero.mp tl))
  case succ l IH =>
    cases t
    case atom n =>
      cases ct <;> dsimp [LamTerm.pushBVCast] <;> apply LamEquiv.refl wft
    case etom n =>
      cases ct <;> dsimp [LamTerm.pushBVCast] <;> apply LamEquiv.refl wft
    case base b =>
      cases ct <;> try (dsimp [LamTerm.pushBVCast]; apply LamEquiv.refl wft)
      case ofNat m =>
        cases b <;> try (dsimp [LamTerm.pushBVCast]; apply LamEquiv.refl wft)
        case ncst nc =>
          cases nc <;> dsimp [LamTerm.pushBVCast, LamTerm.applyBVCast] <;> try apply LamEquiv.refl wft
          cases wft.getFn.getBase.getBvcst; apply LamEquiv.bvofNat
    case bvar n =>
      cases ct <;> dsimp [LamTerm.pushBVCast] <;> apply LamEquiv.refl wft
    case lam s' body =>
      cases ct <;> try (dsimp [LamTerm.pushBVCast]; apply LamEquiv.refl wft)
      case none =>
        dsimp [LamTerm.pushBVCast, LamTerm.applyBVCast]
        cases wft
        case ofLam s'' wfBody =>
          apply LamEquiv.ofLam; apply IH (ct:=.none) (t:=body) wfBody
          apply Nat.le_of_succ_le_succ tl
    case app s' fn arg =>
      cases ct
      case ofNat m =>
        cases fn <;> try (dsimp [LamTerm.pushBVCast]; apply LamEquiv.refl wft)
        case base b =>
          cases b <;> try (dsimp [LamTerm.pushBVCast]; apply LamEquiv.refl wft)
          case bvcst bvc =>
            cases bvc <;> try (dsimp [LamTerm.pushBVCast]; apply LamEquiv.refl wft)
            case bvtoNat =>
              cases wft.getFn.getBase.getBvcst
              have wfn := wft.getArg
              cases wfn.getFn.getBase.getBvcst
              have wfbv := wfn.getArg
              dsimp [LamTerm.applyBVCast, LamTerm.pushBVCast]
              apply LamEquiv.trans (LamEquiv.bvofNat_bvtoNat wfbv)
              apply LamEquiv.congrArg (.ofBase (.ofBvzeroExtend' _ _))
              apply IH (ct:=.none) (t:=arg) wfbv
              apply Nat.le_of_succ_le_succ (Nat.le_trans LamTerm.size_app_gt_size_arg tl)
        case app s'' fn arg₁ =>
          cases fn <;> try (dsimp [LamTerm.pushBVCast]; apply LamEquiv.refl wft)
          case base b =>
            cases b <;> try (dsimp [LamTerm.pushBVCast]; apply LamEquiv.refl wft)
            case ncst nc =>
              cases nc <;> dsimp [LamTerm.pushBVCast] <;> try apply LamEquiv.refl wft
              case nadd =>
                cases wft.getFn.getBase.getBvcst
                have wfnadd := wft.getArg
                cases wfnadd.getFn.getFn.getBase.getNcst
                have wfl := wfnadd.getFn.getArg; have wfr := wfnadd.getArg
                dsimp [LamTerm.applyBVCast]
                apply LamEquiv.trans (LamEquiv.bvofNat_nadd wfl wfr)
                apply LamEquiv.congr (LamEquiv.congrArg (.ofBase (.ofBvadd' _)) ?eql) ?eqr
                case eql =>
                  apply IH (ct:=.ofNat m) (t:=arg₁) (.mkBvofNat wfl)
                  apply Nat.le_of_succ_le_succ (Nat.le_trans (Nat.le_trans
                    LamTerm.size_app_gt_size_arg LamTerm.size_app_ge_size_fn) tl)
                case eqr =>
                  apply IH (ct:=.ofNat m) (t:=arg) (.mkBvofNat wfr)
                  apply Nat.le_of_succ_le_succ (Nat.le_trans LamTerm.size_app_gt_size_arg tl)
              case nmul =>
                cases wft.getFn.getBase.getBvcst
                have wfnadd := wft.getArg
                cases wfnadd.getFn.getFn.getBase.getNcst
                have wfl := wfnadd.getFn.getArg; have wfr := wfnadd.getArg
                dsimp [LamTerm.applyBVCast]
                apply LamEquiv.trans (LamEquiv.bvofNat_nmul wfl wfr)
                apply LamEquiv.congr (LamEquiv.congrArg (.ofBase (.ofBvmul' _)) ?eql) ?eqr
                case eql =>
                  apply IH (ct:=.ofNat m) (t:=arg₁) (.mkBvofNat wfl)
                  apply Nat.le_of_succ_le_succ (Nat.le_trans (Nat.le_trans
                    LamTerm.size_app_gt_size_arg LamTerm.size_app_ge_size_fn) tl)
                case eqr =>
                  apply IH (ct:=.ofNat m) (t:=arg) (.mkBvofNat wfr)
                  apply Nat.le_of_succ_le_succ (Nat.le_trans LamTerm.size_app_gt_size_arg tl)
      case ofInt m => dsimp [LamTerm.pushBVCast]; apply LamEquiv.refl wft
      case none =>
        cases fn <;> try (
          dsimp [LamTerm.pushBVCast]; apply LamEquiv.congrArg wft.getFn
          apply IH (ct:=.none) wft.getArg; apply Nat.le_of_succ_le_succ (Nat.le_trans
            LamTerm.size_app_gt_size_arg tl))
        case base b =>
          cases b <;> try (
            apply LamEquiv.congrArg wft.getFn (IH (ct:=.none) wft.getArg _)
            apply Nat.le_of_succ_le_succ (Nat.le_trans LamTerm.size_app_gt_size_arg tl))
          case bvcst bvc =>
            cases bvc <;> try (
              apply LamEquiv.congrArg wft.getFn (IH (ct:=.none) wft.getArg _)
              apply Nat.le_of_succ_le_succ (Nat.le_trans LamTerm.size_app_gt_size_arg tl))
            case bvofNat m =>
              cases wft.getFn.getBase.getBvcst
              apply IH (ct:=.ofNat m) (t:=arg) wft
              apply Nat.le_of_succ_le_succ (Nat.le_trans LamTerm.size_app_gt_size_arg tl)
            case bvofInt m =>
              cases wft.getFn.getBase.getBvcst
              apply IH (ct:=.ofInt m) (t:=arg) wft
              apply Nat.le_of_succ_le_succ (Nat.le_trans LamTerm.size_app_gt_size_arg tl)
        case lam s' body =>
          dsimp [LamTerm.applyBVCast]; apply LamEquiv.congr
          case eFn =>
            apply IH (ct:=.none) (t:=.lam s' body) wft.getFn
            apply Nat.le_of_succ_le_succ (Nat.le_trans LamTerm.size_app_gt_size_fn tl)
          case eArg =>
            apply IH (ct:=.none) (t:=arg) wft.getArg
            apply Nat.le_of_succ_le_succ (Nat.le_trans LamTerm.size_app_gt_size_arg tl)
        case app s'' fn arg₁ =>
          dsimp [LamTerm.applyBVCast]; apply LamEquiv.congr
          case eFn =>
            apply IH (ct:=.none) (t:=.app s'' fn arg₁) wft.getFn
            apply Nat.le_of_succ_le_succ (Nat.le_trans LamTerm.size_app_gt_size_fn tl)
          case eArg =>
            apply IH (ct:=.none) (t:=arg) wft.getArg
            apply Nat.le_of_succ_le_succ (Nat.le_trans LamTerm.size_app_gt_size_arg tl)

theorem LamGenConv.pushBVCast : LamGenConv lval (fun t => LamTerm.pushBVCast .none t) := by
  intros t₁ t₂ heq lctx rty wf; cases heq
  apply LamEquiv.pushBVCast (ct:=.none) wf

end Auto.Embedding.Lam