module
public import Theory.GroupTheory.Commutator.CentralizerQuotient
/-!
# Equality in the transverse centralizer-index bound

Two subgroups of index q displacing H into disjoint layers bound the full
centralizer index by q². If that bound is attained, both subgroups are the
entire commutator preimages of their layers. This follows by equality in
the intersection-index bound and the index multiplication formula.

The source application identifies the centralizer's position inside the
actual local Sylow preimages in DGS85, Groups and Graphs, pp.188–189.
-/
public noncomputable section
open Subgroup
namespace Subgroup
variable {G : Type*} [Group G]
/-- At the sharp transverse index bound, each displacement subgroup is the
full preimage of its displacement layer. -/
theorem commutatorPreimage_eq_of_sharp_transverse_index
    (Q H U V D E : Subgroup G) [Finite Q]
    (hQU : Q ≤ normalizer (U : Set G)) (hQV : Q ≤ normalizer (V : Set G))
    (hUV : U ⊓ V = ⊥) (hDQ : D ≤ Q) (hEQ : E ≤ Q)
    (hD : ⁅D,H⁆ ≤ U) (hE : ⁅E,H⁆ ≤ V) {q : ℕ} (hq : 0 < q)
    (hd : D.relIndex Q = q) (he : E.relIndex Q = q)
    (hc : (centralizer (H : Set G)).relIndex Q = q^2) :
    commutatorPreimage Q H U = D ∧ commutatorPreimage Q H V = E := by
  let P := commutatorPreimage Q H U
  let R := commutatorPreimage Q H V
  have hP : P ≤ Q := commutatorPreimage_le Q H U
  have hR : R ≤ Q := commutatorPreimage_le Q H V
  have hDP : D ≤ P := le_commutatorPreimage hDQ hD
  have hER : E ≤ R := le_commutatorPreimage hEQ hE
  have hPR : P ⊓ R ≤ centralizer (H : Set G) := by
    apply commutator_eq_bot_iff_le_centralizer.mp
    apply bot_unique
    rw [←hUV]
    exact le_inf ((commutator_mono inf_le_left le_rfl).trans
      (commutator_commutatorPreimage_le Q H U hQU))
      ((commutator_mono inf_le_right le_rfl).trans
        (commutator_commutatorPreimage_le Q H V hQV))
  have hp : P.relIndex Q ≤ q :=
    (relIndex_le_of_le_left hDP index_ne_zero_of_finite).trans_eq hd
  have hr : R.relIndex Q ≤ q :=
    (relIndex_le_of_le_left hER index_ne_zero_of_finite).trans_eq he
  have hi : q^2 ≤ P.relIndex Q * R.relIndex Q := by
    rw [←hc]
    exact (relIndex_le_of_le_left hPR index_ne_zero_of_finite).trans relIndex_inf_le
  have hp' : P.relIndex Q = q := by
    have hh := Nat.mul_le_mul_left (P.relIndex Q) hr
    nlinarith
  have hr' : R.relIndex Q = q := by
    have hh := Nat.mul_le_mul_right (R.relIndex Q) hp
    nlinarith
  have eq_of_index (A B : Subgroup G) (hAB : A ≤ B) (hBQ : B ≤ Q)
      (hi : A.relIndex Q = B.relIndex Q) : B = A := by
    have hh := relIndex_mul_relIndex A B Q hAB hBQ
    rw [hi] at hh
    have hp : 0 < B.relIndex Q := Nat.pos_of_ne_zero index_ne_zero_of_finite
    have heq : A.relIndex B = 1 := by nlinarith
    exact le_antisymm (relIndex_eq_one.mp heq) hAB
  exact ⟨eq_of_index D P hDP hP (hd.trans hp'.symm),
    eq_of_index E R hER hR (he.trans hr'.symm)⟩
end Subgroup
