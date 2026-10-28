module
public import Theory.Mathieu.M22.Properties.HexadSplitCoordinates.Coordinates
public import Mathlib.GroupTheory.Complement

/-!
# Split native hexads with their natural-module marking

For every actual hexad in the degree-22 M22 design, fixing a complementary
point supplies a section of its literal six-point quotient. The native
embedding into M24 transports the proved hexad natural action to this kernel.
Composing the section with the explicitly displayed comparison automorphism
gives exactly the natural A6 action in the constructed kernel coordinates.

The final theorem supplies the section, its complement property, the original
six-point quotient formula, and the natural conjugation formulas for both
section elements and arbitrary stabilizer elements. These are the native
inputs used when lifting the hexad through a central cover in I.2.2(6).

Source: Aschbacher--Smith, I.2.2(6), printed p.412 (PDF p.423), and the native
natural hexad action H.14.3(3), printed p.397 (PDF p.408).
-/

@[expose] public section
namespace Sporadic.Mathieu
open scoped Pointwise
noncomputable section

/-- The automorphism comparing the natural-module marking with the original six hexad labels. -/
def m22HexadMarking {B : Finset (Fin 22)} (hB : B ∈ m22Blocks) :
    alternatingGroup (Fin 6) ≃* alternatingGroup (Fin 6) :=
  M22HexadCoordinates.comparison hB

/-- Natural-module coordinates on the actual pointwise hexad kernel. -/
def m22HexadNaturalCoordinates {B : Finset (Fin 22)} (hB : B ∈ m22Blocks) :
    (m22SetAction B).ker ≃* Multiplicative (BinaryPermutation.natural (Fin 6)) :=
  M22HexadCoordinates.coordinates hB

/-- Every hexad has a point outside it in the native degree-22 action. -/
theorem exists_m22Hexad_complementary_point {B : Finset (Fin 22)} (hB : B ∈ m22Blocks) :
    ∃ a : Fin 22, a ∉ B := by
  by_contra! h
  have he : B = Finset.univ := Finset.eq_univ_iff_forall.mpr h
  have hc := m22Block_card B hB
  rw [he, Finset.card_univ, Fintype.card_fin] at hc
  omega

/-- A genuine native section, parametrized so that its action on the kernel is natural. -/
def m22HexadSection {B : Finset (Fin 22)} (hB : B ∈ m22Blocks) :
    alternatingGroup (Fin 6) →* MulAction.stabilizer M22 B :=
  (m22HexadPointSection hB (Classical.choose_spec (exists_m22Hexad_complementary_point hB))).comp
    (m22HexadMarking hB).toMonoidHom

/-- The literal six-point quotient retains the explicit comparison automorphism. -/
@[simp] theorem m22HexadSixMap_section {B : Finset (Fin 22)} (hB : B ∈ m22Blocks)
    (a : alternatingGroup (Fin 6)) :
    m22HexadSixMap hB (m22HexadSection hB a) = m22HexadMarking hB a :=
  m22HexadSixMap_pointSection hB
    (Classical.choose_spec (exists_m22Hexad_complementary_point hB)) (m22HexadMarking hB a)

/-- The section acts on the actual six hexad labels by the displayed marking. -/
theorem m22HexadSection_action {B : Finset (Fin 22)} (hB : B ∈ m22Blocks)
    (a : alternatingGroup (Fin 6)) (b : B) :
    m22HexadLabels hB (m22SetAction B (m22HexadSection hB a) b) =
      (m22HexadMarking hB a).val (m22HexadLabels hB b) := by
  rw [← m22HexadAction_apply, ← m22HexadSixMap_coe, m22HexadSixMap_section]

/-- Conjugation by any member of the native hexad stabilizer, in natural coordinates. -/
theorem m22HexadNaturalCoordinates_conjugation {B : Finset (Fin 22)}
    (hB : B ∈ m22Blocks) (g : MulAction.stabilizer M22 B) (u : (m22SetAction B).ker) :
    (m22HexadNaturalCoordinates hB (MulAut.conjNormal g u)).toAdd =
      BinaryPermutation.naturalRepresentation (Fin 6)
        ((m22HexadMarking hB).symm (m22HexadSixMap hB g)).val
        (m22HexadNaturalCoordinates hB u).toAdd := by
  exact (M22HexadCoordinates.coordinates_conjugation hB g u).trans
    (congrArg (fun a : alternatingGroup (Fin 6) =>
      BinaryPermutation.naturalRepresentation (Fin 6) a.val
        (m22HexadNaturalCoordinates hB u).toAdd) (M22HexadCoordinates.naturalMap_eq hB g))

/-- The lifted alternating section has exactly the natural action, with no residual twist. -/
theorem m22HexadNaturalCoordinates_section {B : Finset (Fin 22)} (hB : B ∈ m22Blocks)
    (a : alternatingGroup (Fin 6)) (u : (m22SetAction B).ker) :
    (m22HexadNaturalCoordinates hB (MulAut.conjNormal (m22HexadSection hB a) u)).toAdd =
      BinaryPermutation.naturalRepresentation (Fin 6) a.val
        (m22HexadNaturalCoordinates hB u).toAdd := by
  rw [m22HexadNaturalCoordinates_conjugation, m22HexadSixMap_section,
    MulEquiv.symm_apply_apply]

theorem m22HexadSection_injective {B : Finset (Fin 22)} (hB : B ∈ m22Blocks) :
    Function.Injective (m22HexadSection hB) := by
  intro a b hab
  apply (m22HexadMarking hB).injective
  simpa only [m22HexadSixMap_section] using congrArg (m22HexadSixMap hB) hab

/-- The range of the constructed section is complementary to the actual pointwise kernel. -/
theorem m22HexadSection_isComplement {B : Finset (Fin 22)} (hB : B ∈ m22Blocks) :
    (m22SetAction B).ker.IsComplement' (m22HexadSection hB).range := by
  let s := m22HexadSection hB
  let q := m22HexadSixMap hB
  have hd : Disjoint (m22SetAction B).ker s.range := by
    apply disjoint_iff_inf_le.mpr
    rintro g ⟨hg, a, rfl⟩
    have he : q (s a) = 1 := by
      change s a ∈ q.ker
      rw [m22HexadSixMap_ker]
      exact hg
    rw [m22HexadSixMap_section, map_eq_one_iff _ (m22HexadMarking hB).injective] at he
    rw [he, map_one]
    exact Subgroup.one_mem _
  refine ⟨Subgroup.mul_injective_of_disjoint hd, ?_⟩
  intro g
  let a := (m22HexadMarking hB).symm (q g)
  have hn : g * (s a)⁻¹ ∈ (m22SetAction B).ker := by
    rw [← m22HexadSixMap_ker hB]
    change q (g * (s a)⁻¹) = 1
    rw [map_mul, map_inv, m22HexadSixMap_section, MulEquiv.apply_symm_apply,
      mul_inv_cancel]
  exact ⟨(⟨g * (s a)⁻¹, hn⟩, ⟨s a, a, rfl⟩), inv_mul_cancel_right g (s a)⟩

/-- Native splitting and marked natural-module coordinates for every actual hexad.
The quotient map is precisely the one induced by the original six-point restriction. -/
theorem m22Hexad_split_natural_coordinates {B : Finset (Fin 22)} (hB : B ∈ m22Blocks) :
    ∃ (alpha : alternatingGroup (Fin 6) ≃* alternatingGroup (Fin 6))
      (s : alternatingGroup (Fin 6) →* MulAction.stabilizer M22 B)
      (E : (m22SetAction B).ker ≃* Multiplicative (BinaryPermutation.natural (Fin 6))),
      (∀ a, m22HexadQuotientAlternatingEquiv hB (QuotientGroup.mk (s a)) = alpha a) ∧
      (m22SetAction B).ker.IsComplement' s.range ∧
      (∀ a u, (E (MulAut.conjNormal (s a) u)).toAdd =
        BinaryPermutation.naturalRepresentation (Fin 6) a.val (E u).toAdd) ∧
      (∀ g u, (E (MulAut.conjNormal g u)).toAdd =
        BinaryPermutation.naturalRepresentation (Fin 6)
          (alpha.symm (m22HexadQuotientAlternatingEquiv hB (QuotientGroup.mk g))).val
          (E u).toAdd) :=
  ⟨m22HexadMarking hB, m22HexadSection hB, m22HexadNaturalCoordinates hB,
    m22HexadSixMap_section hB, m22HexadSection_isComplement hB,
    m22HexadNaturalCoordinates_section hB, m22HexadNaturalCoordinates_conjugation hB⟩

end
end Sporadic.Mathieu
