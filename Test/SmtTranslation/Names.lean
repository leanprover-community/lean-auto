import Auto.Tactic

set_option auto.smt true
set_option auto.smt.trust true

set_option trace.auto.printLemmas true
set_option trace.auto.lamReif.printValuation true
set_option trace.auto.lamReif.printResult true

set_option trace.auto.smt.printCommands true
set_option trace.auto.smt.result true
set_option trace.auto.smt.unsatCore.smtTerms true
set_option trace.auto.smt.model true

example : forall (n : Nat), n = n := by
 intro n
 auto

class TotalOrder (t : Type) :=
  -- relation: total order
  le (x y : t) : Bool
  none : t
  -- axioms
  le_refl       (x : t) : le x x
  le_trans  (x y z : t) : le x y → le y z → le x z
  le_antisymm (x y : t) : le x y → le y x → x = y
  le_total    (x y : t) : le x y ∨ le y x

class Quorum (node : Type) (quorum : outParam Type):=
  -- relation
  member (a : node) (q : quorum) : Bool
  -- axioms
  quorum_intersection :
    ∀ (q1 q2 : quorum), ∃ (a : node), member a q1 ∧ member a q2

theorem extracted_paxos_goal {node : Type} [inst : DecidableEq node] {value : Type} [inst_1 : DecidableEq value]
  {quorum : Type} [inst_2 : Quorum node quorum] {round : Type} [inst_3 : DecidableEq round] [inst_4 : TotalOrder round]
  (st_one_a : round → Bool) (st_one_b_max_vote : node → round → round → value → Bool)
  (st_one_b st_leftRound : node → round → Bool) (st_proposal : round → value → Bool)
  (st_vote st_decision : node → round → value → Bool)
  (hinv :
    (∀ (n1 n2 : node) (r1 r2 : round) (v1 v2 : value),
        st_decision n1 r1 v1 = true ∧ st_decision n2 r2 v2 = true → r1 = r2 ∧ v1 = v2) ∧
      (∀ (r : round) (v1 v2 : value), st_proposal r v1 = true ∧ st_proposal r v2 = true → v1 = v2) ∧
        (∀ (n : node) (r : round) (v : value), st_vote n r v = true → st_proposal r v = true) ∧
          (∀ (r : round) (v : value),
              (∃ n, st_decision n r v = true) → ∃ q, ∀ (n : node), Quorum.member n q = true → st_vote n r v = true) ∧
            (∀ (n : node) (v : value), ¬st_vote n TotalOrder.none v = true) ∧
              (∀ (r1 r2 : round) (v1 v2 : value) (q : quorum),
                  ¬TotalOrder.le r2 r1 = true ∧ st_proposal r2 v2 = true ∧ v1 ≠ v2 →
                    ∃ n r3 rmax v,
                      Quorum.member n q = true ∧
                        ¬TotalOrder.le r3 r1 = true ∧ st_one_b_max_vote n r3 rmax v = true ∧ ¬st_vote n r1 v1 = true) ∧
                ∀ (n : node) (r1 r2 : round),
                  st_one_b n r2 = true ∧ ¬TotalOrder.le r2 r1 = true → st_leftRound n r1 = true)
  (st'_one_a : round → Bool) (st'_one_b_max_vote : node → round → round → value → Bool)
  (st'_one_b st'_leftRound : node → round → Bool) (st'_proposal : round → value → Bool)
  (st'_vote st'_decision : node → round → value → Bool)
  (hnext :
    ∃ n r max_round max_val,
      r ≠ TotalOrder.none ∧
        st_one_a r = true ∧
          ¬st_leftRound n r = true ∧
            ((max_round = TotalOrder.none ∧
                  ∀ (MAXR : round) (V : value), ¬(¬TotalOrder.le r MAXR = true ∧ st_vote n MAXR V = true)) ∨
                max_round ≠ TotalOrder.none ∧
                  ¬TotalOrder.le r max_round = true ∧
                    st_vote n max_round max_val = true ∧
                      ∀ (MAXR : round) (V : value),
                        ¬TotalOrder.le r MAXR = true ∧ st_vote n MAXR V = true → TotalOrder.le MAXR max_round = true) ∧
              st'_one_a = st_one_a ∧
                (st'_one_b_max_vote = fun x x_1 x_2 x_3 =>
                    if (x, x_1, x_2, x_3, ()) = (n, r, max_round, max_val, ()) then true
                    else st_one_b_max_vote x x_1 x_2 x_3) ∧
                  (st'_one_b = fun x x_1 => if (x, x_1, ()) = (n, r, ()) then true else st_one_b x x_1) ∧
                    (st'_leftRound = fun N R => decide (st_leftRound N R = true ∨ N = n ∧ ¬TotalOrder.le r R = true)) ∧
                      st'_proposal = st_proposal ∧ st'_vote = st_vote ∧ st'_decision = st_decision)
  (r1 r2 : round) (v1 v2 : value) (q : quorum)
  (h : ¬TotalOrder.le r2 r1 = true ∧ st'_proposal r2 v2 = true ∧ v1 ≠ v2) :
  ∃ n r3 rmax v,
    Quorum.member n q = true ∧
      ¬TotalOrder.le r3 r1 = true ∧ st'_one_b_max_vote n r3 rmax v = true ∧ ¬st'_vote n r1 v1 = true := by
      auto [hnext, hinv, h]
