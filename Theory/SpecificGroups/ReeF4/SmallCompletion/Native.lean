module
public import Theory.SpecificGroups.ReeF4.SourceCompletion.LocalGeometry
public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.Geometry
public import Theory.SpecificGroups.ReeF4.SectionGeometry.CoreFree.LinearRadical
public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.OuterLocal.BinaryAutomorphisms.FullDerivedAction.Center
public import Theory.SpecificGroups.ReeF4.CentralCovers.OddPrimary.Order
public import Theory.GroupTheory.NormalizedSupCard
public import Mathlib.GroupTheory.Subgroup.Center

/-!
# Faithful inner action and native counts for positive-parameter Ree groups

A central element normalizes the positive subgroup, so lies in the Borel.
Self-centralization of the linear radical then places it in the positive
subgroup, where opposition eliminates it. This proves faithful conjugation
without assuming simplicity. The fixed torus and unipotent orders give the
Borel order; cancellation in the existing Bruhat order and the two Borel
indices gives both exact parabolic coset counts.

These model facts supply the full-extension transport and counting step in
Aschbacher–Smith F.4.3–6 and F.4.24, printed pp.274–277,287–288.
All positive parameters, including q=8, are retained.
-/

public noncomputable section
namespace ReeF4.SmallCompletion
open Subgroup Parabolics LargeLocalSeeds

/-- The positive-parameter native Ree carrier has trivial center. -/
theorem center_eq_bot (m : ℕ) (hm : 0 < m) : center (Model m) = ⊥ := by
  apply le_bot_iff.mp
  intro z hz
  have hzB : z ∈ borel m := by
    rw [← unipotent_normalizer_eq_borel]
    exact center_le_normalizer _ hz
  let zP : parabolic m .linear := ⟨z, borel_le_parabolic m .linear hzB⟩
  have hc : zP ∈ centralizer ((radical m .linear).subgroupOf (parabolic m .linear) :
      Set (parabolic m .linear)) := by
    rw [mem_centralizer_iff]
    intro x _
    apply Subtype.ext
    exact (mem_center_iff.mp hz) x.val
  have hr := SectionGeometry.LinearRadical.centralizer_le_radical m hm hc
  have hu : z ∈ unipotent m := radical_le_unipotent m .linear hr
  have hh : z ∈ center (Model m) ⊓ unipotent m := ⟨hz, hu⟩
  rwa [OuterLocal.center_inf_unipotent_eq_bot] at hh

/-- The inner action of the actual native carrier is faithful. -/
theorem conj_injective (m : ℕ) (hm : 0 < m) :
    Function.Injective (MulAut.conj : Model m →* MulAut (Model m)) := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply bot_unique
  intro z hz
  have hc : z ∈ center (Model m) := by
    rw [mem_center_iff]
    intro x
    have he := congrArg (fun a : MulAut (Model m) => a x) hz
    change z*x*z⁻¹ = x at he
    exact (mul_inv_eq_iff_eq_mul.mp he).symm
  rwa [center_eq_bot m hm] at hc

open CentralCovers.OddPrimary.Order

/-- The whole Borel, including the fixed torus, has its native order. -/
theorem card_borel (m : ℕ) :
    Nat.card (borel m) = (2^(2*m+1))^12 * (2^(2*m+1)-1)^2 := by
  rw [borel_eq_unipotent_sup_fixedTorus]
  rw [card_sup_eq_mul_of_normalizes_of_disjoint _ _
    ((fixedTorus_le_borel m).trans (borel_le_unipotent_normalizer m)) ?_,
    card_unipotent, card_fixedTorus]
  apply disjoint_of_coprime_natCard
  rw [card_unipotent, ← pow_mul]
  exact (Nat.coprime_two_left.mpr (fixedTorus_odd_card m (splitTorus_odd_card m))).pow_left _

/-- Native coset counts, in the linear/Suzuki orientation. -/
@[expose] def cosetCount (m : ℕ) (i : Bool) : ℕ :=
  (if i then 2^(2*m+1)+1 else (2^(2*m+1))^2+1) *
    ((2^(2*m+1))^3+1) * ((2^(2*m+1))^6+1)

/-- Exact coset counts for the two full native parabolics. -/
theorem card_coset (m : ℕ) (hm : 0 < m) (i : Bool) :
    Nat.card (Model m ⧸ SourceCompletion.family m i) = cosetCount m i := by
  let q := 2^(2*m+1)
  have hB : 0 < Nat.card (borel m) := Nat.card_pos
  have hG : Nat.card (Model m) = Nat.card (borel m) * cellPolynomial q := by
    rw [card_borel, card_model_torus_weyl_sum, card_fixedTorus, sum_card_fixedRightUnipotent]
    rfl
  have hb := relIndex_mul_index (borel_le_parabolic m (if i then .suzuki else .linear))
  have hbi : (borel m).index = cellPolynomial q := by
    apply Nat.eq_of_mul_eq_mul_right hB
    rw [index_mul_card, hG, mul_comm]
  rw [hbi, SourceCompletion.borel_relIndex m hm] at hb
  cases i
  · change (parabolic m .linear).index = _
    simp only [Bool.false_eq_true, ↓reduceIte] at hb
    apply Nat.eq_of_mul_eq_mul_left (by positivity : 0 < q+1)
    exact hb.trans (by simp only [cellPolynomial, cosetCount, Bool.false_eq_true, ↓reduceIte]; ring)
  · change (parabolic m .suzuki).index = _
    simp only [↓reduceIte, reduceCtorEq] at hb
    apply Nat.eq_of_mul_eq_mul_left (by positivity : 0 < q^2+1)
    exact hb.trans (by simp only [cellPolynomial, cosetCount, ↓reduceIte]; ring)

end ReeF4.SmallCompletion
