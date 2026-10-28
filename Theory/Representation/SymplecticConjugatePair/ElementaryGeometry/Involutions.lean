module

public import Theory.Representation.SymplecticConjugatePair.ElementaryGeometry.Involutions.RootIdentification

/-!
# Native involutions on the natural-plus-graph symplectic pair

On the central root plane the actual exceptional graph automorphism sends
`(s,t)` to `(t²,s)`. Conjugacy normal form and the geometric moved-space tests
therefore show that it interchanges Suzuki types b₁ and a₂ and preserves c₂.

Root involutions have paired fixed codimension 3n; mixed central elements,
and hence all c₂ involutions, have codimension 4n. For c₂ the fixed space
is exactly the displacement image, the intrinsic freeness identity. Every
native involution consequently has codimension at least 3n. Restriction
through the genuine commutator inclusion gives the same lower bound, including
over the binary field, without asserting membership of attaining root witnesses.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*,
Definition E.2.6, printed p.218, and H.7, printed pp.388–389.
-/

public section

open scoped Matrix
open Matrix Representation Representation.BinaryOffender
open Theory.SpecificGroups.SymplecticFour
open Representation.OneCohomology.SymplecticFour
open Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.ExceptionalGraph
open Theory.SpecificGroups.SymplecticFour.InvolutionTypes

namespace SymplecticConjugatePair.Involutions
set_option linter.unusedSimpArgs false
variable {F : Type*} [Field F] [CharP F 2] [Finite F] [Algebra (ZMod 2) F]

private lemma graph_conjugate_central {g h : Sp F} {s t : F}
    (he : h*g*h⁻¹ = rootElement 0 s * rootElement 4 t) :
    graphAut h * graphAut g * (graphAut h)⁻¹ = rootElement 0 (t^2) * rootElement 4 s := by
  rw [← map_inv,← map_mul,← map_mul,he,graphAut_central]

lemma graphAut_isB1_iff {n : ℕ} (hF : Nat.card F = 2^n) (g : Sp F) :
    IsB1 (graphAut g) ↔ IsA2 g := by
  by_cases hg : orderOf g = 2
  · obtain ⟨h,s,t,he⟩ := involution_conjugate_central hF g hg
    rw [← isB1_conj_iff (graphAut h),graph_conjugate_central he,central_isB1_iff,
      ← isA2_conj_iff h g,he,central_isA2_iff]
    simp only [ne_eq,sq_eq_zero_iff,and_comm]
  · simp only [IsB1,IsA2,graphAut.orderOf_eq,hg,false_and]

lemma graphAut_isA2_iff {n : ℕ} (hF : Nat.card F = 2^n) (g : Sp F) :
    IsA2 (graphAut g) ↔ IsB1 g := by
  by_cases hg : orderOf g = 2
  · obtain ⟨h,s,t,he⟩ := involution_conjugate_central hF g hg
    rw [← isA2_conj_iff (graphAut h),graph_conjugate_central he,central_isA2_iff,
      ← isB1_conj_iff h g,he,central_isB1_iff]
    simp only [sq_eq_zero_iff,and_comm]
  · simp only [IsB1,IsA2,graphAut.orderOf_eq,hg,false_and]

lemma graphAut_isC2_iff {n : ℕ} (hF : Nat.card F = 2^n) (g : Sp F) :
    IsC2 (graphAut g) ↔ IsC2 g := by
  by_cases hg : orderOf g = 2
  · obtain ⟨h,s,t,he⟩ := involution_conjugate_central hF g hg
    rw [← isC2_conj_iff (graphAut h),graph_conjugate_central he,central_isC2_iff,
      ← isC2_conj_iff h g,he,central_isC2_iff]
    simp only [ne_eq,sq_eq_zero_iff,and_comm]
  · simp only [IsC2,graphAut.orderOf_eq,hg,false_and]

lemma rootElement_fixedCodim {n : ℕ} (hF : Nat.card F = 2^n)
    (g : Sp F) (hg : IsRootElement g) : fixedCodim graphPair (Subgroup.zpowers g) = 3*n := by
  obtain ⟨h,r,t,ht,rfl⟩ := hg
  rw [fixedCodim_zpowers_conj]
  exact root_fixedCodim_of_card hF r ht

lemma isB1_fixedCodim {n : ℕ} (hF : Nat.card F = 2^n)
    (g : Sp F) (hg : IsB1 g) : fixedCodim graphPair (Subgroup.zpowers g) = 3*n :=
  rootElement_fixedCodim hF g ((isRootElement_iff hF g).mpr (Or.inl hg))

lemma isA2_fixedCodim {n : ℕ} (hF : Nat.card F = 2^n)
    (g : Sp F) (hg : IsA2 g) : fixedCodim graphPair (Subgroup.zpowers g) = 3*n :=
  rootElement_fixedCodim hF g ((isRootElement_iff hF g).mpr (Or.inr hg))

lemma isC2_fixedCodim {n : ℕ} (hF : Nat.card F = 2^n)
    (g : Sp F) (hg : IsC2 g) : fixedCodim graphPair (Subgroup.zpowers g) = 4*n := by
  obtain ⟨h,s,t,he⟩ := involution_conjugate_central hF g hg.1
  have hz := (isC2_conj_iff h g).mpr hg
  rw [he,central_isC2_iff] at hz
  rw [← fixedCodim_zpowers_conj graphPair g h,he]
  exact central_mixed_fixedCodim hF hz.1 hz.2

/-- The intrinsic freeness identity for type c₂: fixed space equals displacement. -/
lemma isC2_fixedSpace_eq_displacement {n : ℕ} (hF : Nat.card F = 2^n)
    (g : Sp F) (hg : IsC2 g) :
    fixedSpace graphPair (Subgroup.zpowers g) = LinearMap.range (graphPair g - LinearMap.id) := by
  apply (Submodule.eq_of_le_of_finrank_eq
    (involution_displacement_le_fixed g (orderOf_eq_prime_iff.mp hg.1).1) ?_).symm
  have hc := fixedCodim_add_finrank (graphPair (F := F)) (Subgroup.zpowers g)
  have hr := fixedCodim_zpowers_eq_displacement_rank (graphPair (F := F)) g
  rw [finrank_space hF,isC2_fixedCodim hF g hg] at hc
  rw [isC2_fixedCodim hF g hg] at hr
  omega

/-- Every involution in the native matrix group has paired binary codimension at least 3n. -/
lemma involution_fixedCodim_lower {n : ℕ} (hF : Nat.card F = 2^n)
    (g : Sp F) (hg : orderOf g = 2) : 3*n ≤ fixedCodim graphPair (Subgroup.zpowers g) := by
  rcases InvolutionCentralizers.involution_types g hg with hb | ha | hc
  · exact (isB1_fixedCodim hF g hb).ge
  · exact (isA2_fixedCodim hF g ha).ge
  · rw [isC2_fixedCodim hF g hc]
    omega

/-- Restriction through the actual commutator inclusion preserves this lower bound,
including over the binary field. No attaining root is claimed to lie in the derived group. -/
lemma derived_involution_fixedCodim_lower {n : ℕ} (hF : Nat.card F = 2^n)
    (g : commutator (Sp F)) (hg : orderOf g = 2) :
    3*n ≤ fixedCodim (derivedPair (graphAut (F := F))) (Subgroup.zpowers g) := by
  have ho : orderOf (g : Sp F) = 2 :=
    (orderOf_injective (commutator (Sp F)).subtype Subtype.val_injective g).trans hg
  have hc := involution_fixedCodim_lower hF (g : Sp F) ho
  change 3*n ≤ Module.finrank (ZMod 2) (Space F ⧸
    fixedSpace (graphPair.comp (commutator (Sp F)).subtype) (Subgroup.zpowers g))
  rw [fixedSpace_comp_map,MonoidHom.map_zpowers]
  exact hc
end SymplecticConjugatePair.Involutions
