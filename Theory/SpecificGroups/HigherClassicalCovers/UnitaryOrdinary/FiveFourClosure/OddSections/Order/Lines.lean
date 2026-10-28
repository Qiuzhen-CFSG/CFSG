module

public import Theory.SpecificGroups.HigherClassicalCovers.UnitaryOrdinary.FiveFourClosure.OddSections.Order.Counting
public import Theory.SpecificGroups.ClassicalUnitary.FiveIsotropicTransitivity
import Mathlib.Tactic.Ring

/-!
# The isotropic-line index in SU₅(4)

Every nonzero isotropic vector generates a unique totally isotropic line,
and each such line contains fifteen nonzero vectors. The structural vector
count therefore gives 17425 lines. The actual special-unitary adapted-basis
construction identifies these lines with the cosets of the literal line
stabilizer, giving its index without an assumed group order.

Source: GLS3, Lemmas 2.7.1--2 (Witt extension), printed pp.89--90 of
`refs/KGroup/GLS3/chapter2.tex`. This supplies the orbit factor in the order
calculation supporting Aschbacher--Smith I.1.4(4), printed p.408.
-/

@[expose] public section

open BenderSuzuki.MatrixGroups
open Theory.SpecificGroups.UnitaryFive
open Theory.SpecificGroups.UnitaryFive.IsotropicGeometry
open scoped Pointwise
namespace Theory.SpecificGroups.HigherClassicalCovers.UnitaryOrdinary.FiveFourClosure.OddSections.Order
variable {F : Type*} [Field F] [Finite F] (J : HermitianForm 5 F)

/-- The actual one-dimensional totally isotropic subspaces. -/
def IsotropicLines := {W : Submodule F (Fin 5 → F) //
  Module.finrank F W = 1 ∧ W ≤ orthogonal J W}

instance : Finite (IsotropicLines J) := by
  have : Finite (Submodule F (Fin 5 → F)) :=
    Finite.of_injective SetLike.coe SetLike.coe_injective
  unfold IsotropicLines
  infer_instance

omit [Finite F] in
private theorem span_isotropic (v : Fin 5 → F) (hv : pairing J v v = 0) :
    Submodule.span F {v} ≤ orthogonal J (Submodule.span F {v}) := by
  intro x hx y hy
  obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hx
  obtain ⟨b, rfl⟩ := Submodule.mem_span_singleton.mp hy
  change (∑ i, J.conj (b * v i) * (a * v i)) = 0
  simp only [map_mul]
  calc
    _ = (J.conj b * a) * ∑ i, J.conj (v i) * v i := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = 0 := by change (J.conj b * a) * pairing J v v = 0; rw [hv, mul_zero]

private def pointedToVector : (Σ W : IsotropicLines J, {v : W.1 // v ≠ 0}) →
    {v : Fin 5 → F // pairing J v v = 0 ∧ v ≠ 0} := fun p =>
  ⟨p.2.1.1, p.1.2.2 p.2.1.2 _ p.2.1.2,
    fun h => p.2.2 (Subtype.ext h)⟩

omit [Finite F] in
private theorem pointedToVector_bijective : Function.Bijective (pointedToVector J) := by
  constructor
  · rintro ⟨W, v⟩ ⟨U, w⟩ h
    have he : v.1.1 = w.1.1 := congrArg Subtype.val h
    have hv : v.1.1 ≠ 0 := fun h => v.2 (Subtype.ext h)
    have hw : w.1.1 ≠ 0 := fun h => w.2 (Subtype.ext h)
    have hWU : W = U := by
      apply Subtype.ext
      rw [eq_span_singleton_of_mem_of_finrank_eq_one W.2.1 v.1.2 hv,
        eq_span_singleton_of_mem_of_finrank_eq_one U.2.1 w.1.2 hw, he]
    subst U
    have hvw : v = w := Subtype.ext (Subtype.ext he)
    subst w
    rfl
  · intro v
    refine ⟨⟨⟨Submodule.span F {v.1}, finrank_span_singleton v.2.2,
      span_isotropic J v.1 v.2.1⟩,
      ⟨⟨v.1, Submodule.mem_span_singleton_self v.1⟩, ?_⟩⟩, rfl⟩
    intro h
    exact v.2.2 (congrArg Subtype.val h)

/-- Every isotropic line has fifteen nonzero vectors. -/
theorem card_pointed_lines (hcard : Nat.card F = 16) :
    Nat.card {v : Fin 5 → F // pairing J v v = 0 ∧ v ≠ 0} =
      Nat.card (IsotropicLines J) * 15 := by
  classical
  let : Fintype F := Fintype.ofFinite F
  let : Fintype (IsotropicLines J) := Fintype.ofFinite _
  rw [← Nat.card_congr (Equiv.ofBijective (pointedToVector J) (pointedToVector_bijective J)),
    Nat.card_sigma]
  have hc (W : IsotropicLines J) : Nat.card {v : W.1 // v ≠ 0} = 15 := by
    let : Fintype W.1 := Fintype.ofFinite _
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype_compl,
      Fintype.card_subtype_eq, Module.card_eq_pow_finrank (K := F) (V := W.1), W.2.1, pow_one,
      ← Nat.card_eq_fintype_card, hcard]
  simp only [hc, Finset.sum_const, Finset.card_univ, smul_eq_mul,
    Nat.card_eq_fintype_card]

variable [CharP F 2]

/-- The cosets of the literal SU line stabilizer parametrize the isotropic lines. -/
theorem index_line_stabilizer (hcard : Nat.card F = 16)
    (hconj : ∀ x, J.conj x = x ^ 4) (hJ : J.form = 1) :
    (specialStabilizer J (line F)).index = Nat.card (IsotropicLines J) := by
  let := MulAction.compHom (Submodule F (Fin 5 → F)) (linearAction J)
  have he (W : Submodule F (Fin 5 → F)) :
      W ∈ MulAction.orbit J.specialSubgroup (line F) ↔
      Module.finrank F W = 1 ∧ W ≤ orthogonal J W := by
    constructor
    · rintro ⟨g, rfl⟩
      change Module.finrank F ((line F).map (linearAction J g).toLinearMap) = 1 ∧ _
      constructor
      · rw [LinearEquiv.finrank_map_eq, finrank_line]
      · rintro x ⟨v, hv, rfl⟩ y ⟨w, hw, rfl⟩
        change pairing J (linearAction J g w) (linearAction J g v) = 0
        rw [pairing_action J hJ]
        exact plane_isotropic F J.conj
          ⟨w, line_le_plane F hw⟩ ⟨v, line_le_plane F hv⟩
    · rintro ⟨hd, hi⟩
      obtain ⟨P, hP, hPW⟩ := IsotropicTransitivity.hasAdaptedBasis_line
        J hcard hconj hJ W hd hi
      obtain ⟨g, hg⟩ := IsotropicTransitivity.special_image_of_adapted_basis
        J hJ false W P hP hPW
      exact ⟨g, hg.symm⟩
  have hc := Nat.card_congr (MulAction.orbitEquivQuotientStabilizer
    J.specialSubgroup (line F))
  have hec := Nat.card_congr (Equiv.subtypeEquivRight he)
  exact hc.symm.trans hec

/-- Remove the zero vector from the structural five-dimensional count. -/
theorem card_nonzero_isotropic_vectors (hcard : Nat.card F = 16)
    (hconj : ∀ x, J.conj x = x ^ 4) :
    Nat.card {v : Fin 5 → F // pairing J v v = 0 ∧ v ≠ 0} = 261375 := by
  classical
  let Z := {v : Fin 5 → F // normSum J v = 0}
  let z : Z := ⟨0, by simp [normSum]⟩
  let : Fintype Z := Fintype.ofFinite Z
  have he (v : Z) : v.1 ≠ 0 ↔ v ≠ z := by
    constructor
    · intro h he
      exact h (congrArg Subtype.val he)
    · intro h he
      exact h (Subtype.ext he)
  have e : {v : Fin 5 → F // pairing J v v = 0 ∧ v ≠ 0} ≃ {v : Z // v ≠ z} :=
    (Equiv.subtypeSubtypeEquivSubtypeInter (fun v => normSum J v = 0)
      (fun v => v ≠ 0)).symm.trans (Equiv.subtypeEquivRight he)
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_subtype_compl,
    Fintype.card_subtype_eq, ← Nat.card_eq_fintype_card]
  change Nat.card {v : Fin 5 → F // normSum J v = 0} - 1 = 261375
  rw [card_normSum_zero_five J hcard hconj]

/-- The five-space has exactly 17425 isotropic lines. -/
theorem card_isotropic_lines (hcard : Nat.card F = 16)
    (hconj : ∀ x, J.conj x = x ^ 4) : Nat.card (IsotropicLines J) = 17425 := by
  have h := card_pointed_lines J hcard
  rw [card_nonzero_isotropic_vectors J hcard hconj] at h
  omega
end Theory.SpecificGroups.HigherClassicalCovers.UnitaryOrdinary.FiveFourClosure.OddSections.Order
