module
public import Theory.SpecificGroups.SU3.TernaryOrthogonalThreeRank
import all Theory.SpecificGroups.SU3.TernaryOrthogonalThreeRank
public import GorensteinWalter.PSL2PerfectSubnormal
public import Theory.GroupTheory.GeneralizedFitting.IndexTwoCover
public import Theory.AtlasPort.ExceptionalIsomorphisms.Order168Models
public import Theory.SpecificGroups.SU3.OddPrimeSylowAutomorphisms.NormalizedOuterInvolutions.Descent.SymmetricSimilarity
import all Theory.SpecificGroups.SU3.OddPrimeSylowAutomorphisms.NormalizedOuterInvolutions.Descent.SymmetricSimilarity
public import Theory.SpecificGroups.SU3.OddPrimeSylowAutomorphisms.NormalizedOuterInvolutions.FormTransport
import all Theory.SpecificGroups.SU3.OddPrimeSylowAutomorphisms.NormalizedOuterInvolutions.FormTransport

/-!
# Components of ternary special orthogonal groups

The checked adjoint SL₂ construction has scalar kernel and index-two image.
A component is perfect, so lies in that image, and remains subnormal there.
Transport to the actual PSL₂ quotient and the perfect-subnormal theorem show
that the component is the whole PSL₂ image, including exclusion of the small
solvable case. If the component is PSL₃(2), its order 168 then forces the field
prime to be seven. Order divisibility alone is not used for this recognition.

Finite-field ternary similarity and conjugation extend the calculation to
arbitrary nondegenerate symmetric forms. The three internal imports are
intentional continuations of the adjoint, similarity, and matrix conjugation
proofs; their private constructions remain private. Attribution and license
for the finite-form classification and the order-168 model remain in their
imported ATLAS ports.

Source: GLS3, §§2.7 and 4.3; Aschbacher--Smith, proof of 15.3.38, printed p.1137,
and Theorem C, printed p.33.
-/

open Matrix Subgroup Theory.GroupTheory
namespace BenderSuzuki.MatrixGroups.HermitianForm.OddPrimeSylow.TernaryOrthogonal
variable {F : Type*} [Field F] [Finite F]

/-- Every ordinary component is the full adjoint PSL₂ image. -/
public theorem component_equiv_psl2 {p : ℕ} (hp : p.Prime) (ho : Odd p)
    (hc : Nat.card F = p) {D : Subgroup (splitOrthogonalForm F).specialSubgroup}
    (hD : IsComponent _ D) :
    Nonempty (D ≃* ProjectiveSpecialLinearGroup (Fin 2) F) := by
  let := Fintype.ofFinite F
  have h2 : (2 : F) ≠ 0 := by
    apply Ring.two_ne_zero
    intro he
    have hh := FiniteField.even_card_of_char_two he
    rw [← Nat.card_eq_fintype_card, hc] at hh
    obtain ⟨k, hk⟩ := ho
    omega
  let H := (adjointHom h2).range
  let e := (pslEquivRange h2).symm
  let : IsQuasisimple D := hD.2
  have hle : D ≤ H := le_of_isPerfect_of_index_eq_two D H (adjoint_range_index h2 (hc ▸ ho))
  have hcpt := (hD.subgroupOf hle).map_equiv e
  let L := (D.subgroupOf H).map e.toMonoidHom
  let f : D ≃* L := (subgroupOfEquivOfLe hle).symm.trans
    ((D.subgroupOf H).equivMapOfInjective e.toMonoidHom e.injective)
  let : IsQuasisimple L := hcpt.2
  let : IsSimpleGroup (L ⧸ center L) := IsQuasisimple.simple
  let : Nontrivial L := (QuotientGroup.mk'_surjective (center L)).nontrivial
  have hn : L ≠ ⊥ := (Subgroup.nontrivial_iff_ne_bot L).mp inferInstance
  obtain ⟨_, ht⟩ := GorensteinWalter.psl2_perfect_subnormal_eq_top F
    ⟨p, 1, hp, ho, by omega, by simpa using hc⟩ L hn inferInstance hcpt.1
  exact ⟨f.trans ((MulEquiv.subgroupCongr ht).trans topEquiv)⟩

/-- A PSL₃(2) component of the split group forces field prime seven. -/
public theorem prime_eq_seven_of_component {p : ℕ} (hp : p.Prime) (ho : Odd p)
    (hc : Nat.card F = p) {D : Subgroup (splitOrthogonalForm F).specialSubgroup}
    (hD : IsComponent _ D) (e : D ≃* ProjectiveSpecialLinearGroup (Fin 3) (ZMod 2)) :
    p = 7 := by
  obtain ⟨f⟩ := component_equiv_psl2 hp ho hc hD
  have hDcard : Nat.card D = 168 := by
    rw [Nat.card_congr e.toEquiv,
      ← Nat.card_congr Atlas.Comparisons.Exceptional.sl3TwoEquivPsl3Two.toEquiv]
    exact Atlas.Comparisons.Exceptional.sl3Two_card
  have h := ProjectiveSpecialLinearGroup.psl2_card_twice (F := F) (hc ▸ ho)
  rw [← Nat.card_congr f.toEquiv, hDcard, hc] at h
  have hp2 := hp.two_le
  have hs : p ^ 2 - 1 + 1 = p ^ 2 := Nat.sub_add_cancel (by nlinarith)
  have hcube : p ^ 3 = p + 336 := by nlinarith
  have hl : p ≤ 7 := by
    by_contra! he
    have hsq : 64 ≤ p ^ 2 := by nlinarith
    have hm := Nat.mul_le_mul_left p hsq
    nlinarith
  interval_cases p <;> first | rfl | norm_num at hcube

end BenderSuzuki.MatrixGroups.HermitianForm.OddPrimeSylow.TernaryOrthogonal

namespace BenderSuzuki.MatrixGroups.HermitianForm.OddPrimeSylow
open NormalizedOuter.Descent NormalizedOuter.FormTransport
variable {F : Type*} [Field F] [Finite F]
/-- Finite odd ternary similarity gives an equivalence of the entire isometry groups. -/
public theorem orthogonal_equiv_split (J : HermitianForm 3 F) (hJ : J.conj = 1)
    (h2 : (2 : F) ≠ 0) :
    Nonempty (J.specialSubgroup ≃* (splitOrthogonalForm F).specialSubgroup) := by
  let := invertibleOfNonzero h2
  have hs : J.form.transpose = J.form := by
    ext i j
    have h := J.form_hermitian i j
    rw [hJ] at h
    exact h
  obtain ⟨a, C, ha, hC⟩ := ternary_similarity h2 J.form hs J.form_nondegenerate
  have hconj (M : Matrix (Fin 3) (Fin 3) F) : J.conjTranspose M = M.transpose := by
    ext i j
    change J.conj (M j i) = M j i
    rw [hJ]
    rfl
  have hm (B : GL (Fin 3) F) :
      C * B * C⁻¹ ∈ J.specialSubgroup ↔ B ∈ (splitOrthogonalForm F).specialSubgroup := by
    rw [J.mem_specialSubgroup_iff, (splitOrthogonalForm F).mem_specialSubgroup_iff,
      conjugate_preserves_iff, hconj, hconj, hC]
    simp only [Matrix.mul_smul, Matrix.smul_mul, smul_right_inj ha,
      map_mul, map_inv, mul_assoc, mul_mul_inv_cancel'_right]
    rfl
  exact ⟨(restrictConjugation _ _ C hm).symm⟩

/-- The component parameter calculation for every nondegenerate symmetric ternary form. -/
public theorem prime_eq_seven_of_orthogonal_component
    (J : HermitianForm 3 F) (hJ : J.conj = 1)
    {p : ℕ} (hp : p.Prime) (ho : Odd p) (hc : Nat.card F = p)
    {D : Subgroup J.specialSubgroup} (hD : IsComponent J.specialSubgroup D)
    (e : D ≃* ProjectiveSpecialLinearGroup (Fin 3) (ZMod 2)) : p = 7 := by
  let := Fintype.ofFinite F
  have h2 : (2 : F) ≠ 0 := by
    apply Ring.two_ne_zero
    intro he
    have hh := FiniteField.even_card_of_char_two he
    rw [← Nat.card_eq_fintype_card, hc] at hh
    obtain ⟨k, hk⟩ := ho
    omega
  obtain ⟨f⟩ := orthogonal_equiv_split J hJ h2
  exact TernaryOrthogonal.prime_eq_seven_of_component hp ho hc (hD.map_equiv f)
    ((D.equivMapOfInjective f.toMonoidHom f.injective).symm.trans e)

end BenderSuzuki.MatrixGroups.HermitianForm.OddPrimeSylow
