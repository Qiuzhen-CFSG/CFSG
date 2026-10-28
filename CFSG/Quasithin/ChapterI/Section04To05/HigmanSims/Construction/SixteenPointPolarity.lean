module

public import CFSG.Quasithin.ChapterI.Section04To05.HigmanSims.Construction.PureSixteenIncidence
public import Theory.Representation.BinaryPolarity.ElementarySixteen

/-!
# The alternating form on the original pure sixteen

The actual point cores cut out hyperplanes in the original elementary
sixteen. Reciprocal core membership gives symmetric incidence, and each
point lies in its own core. Binary polarity reconstructs a nondegenerate
alternating form with those literal kernels. The full original normalizer
preserves the form by conjugation covariance of the original point cores.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.HigmanSims
variable {G : Type*} [Group G] [Finite G] {z : G} {V : Subgroup G}

/-- Literal point-core hyperplanes reconstruct an invariant alternating
form on the same original elementary sixteen. -/
theorem TypeAt.sixteen_point_core_form (h : TypeAt z V)
    (A : Subgroup G) [IsElementaryAbelian 2 A] (hA : Nat.card A = 16)
    (hpure : ∀ x ∈ A, x ≠ 1 → IsConj x z)
    (hpoints : ∀ x ∈ A, x ≠ 1 →
      Nat.card (A ⊓ (involutionCentralizer x).pCoreIn 2 : Subgroup G) = 8) :
    ∃ B : LinearMap.BilinForm (ZMod 2) (Additive A), B.IsAlt ∧ B.Nondegenerate ∧
      (∀ (g : normalizer (A : Set G)) (x y : A),
        B (Additive.ofMul (A.normalizerMonoidHom g x))
          (Additive.ofMul (A.normalizerMonoidHom g y)) =
        B (Additive.ofMul x) (Additive.ofMul y)) ∧
      (∀ (x : A) (_hx : x ≠ 1) (y : A),
        B (Additive.ofMul x) (Additive.ofMul y) = 0 ↔
          (y : G) ∈ (involutionCentralizer (x : G)).pCoreIn 2) := by
  let ρ := A.normalizerMonoidHom
  have hne (x : A) (hx : x ≠ 1) : (x : G) ≠ 1 := fun he => hx (Subtype.ext he)
  have hindex (x : {x : A // x ≠ 1}) :
      (((involutionCentralizer (x.val : G)).pCoreIn 2).subgroupOf A).index = 2 := by
    let D := ((involutionCentralizer (x.val : G)).pCoreIn 2).subgroupOf A
    have hc : Nat.card D = 8 := by
      rw [← card_subtype A D, subgroupOf_map_subtype, inf_comm]
      exact hpoints x.val x.val.property (hne x.val x.property)
    have hh := D.card_mul_index
    rw [hc, hA] at hh
    change 8 * (((involutionCentralizer (x.val : G)).pCoreIn 2).subgroupOf A).index = 16 at hh
    omega
  let π : {x : A // x ≠ 1} → {D : Subgroup A // D.index = 2} := fun x =>
    ⟨((involutionCentralizer (x.val : G)).pCoreIn 2).subgroupOf A, hindex x⟩
  have hs : ∀ x y : {x : A // x ≠ 1}, x.val ∈ (π y).val ↔ y.val ∈ (π x).val := by
    intro x y
    exact h.conjugate_point_core_reciprocal y.val x.val
      (hpure y.val y.val.property (hne y.val y.property))
      (hpure x.val x.val.property (hne x.val x.property))
  have ha : ∀ x, x.val ∈ (π x).val := by
    intro x
    obtain ⟨W, hxT⟩ := h.exists_typeAt_of_isConj x.val
      (hpure x.val x.val.property (hne x.val x.property))
    have hh := hxT.seed_le_core hxT.involution_mem_seed
    rwa [hxT.centralizer_fitting] at hh
  have he : ∀ (g : normalizer (A : Set G)) (x : {x : A // x ≠ 1}),
      (π ⟨ρ g x, fun hh => x.property ((ρ g).map_eq_one_iff.mp hh)⟩).val =
        (π x).val.map (ρ g).toMonoidHom := by
    intro g x
    apply map_injective A.subtype_injective
    have hleft : (π ⟨ρ g x, fun hh => x.property ((ρ g).map_eq_one_iff.mp hh)⟩).val.map A.subtype =
        A ⊓ (involutionCentralizer ((g : G) * (x.val : G) * (g : G)⁻¹)).pCoreIn 2 := by
      rw [subgroupOf_map_subtype, inf_comm]
      rfl
    rw [hleft]
    have hright : ((π x).val.map (ρ g).toMonoidHom).map A.subtype =
        (A ⊓ (involutionCentralizer (x.val : G)).pCoreIn 2 : Subgroup G).map
          (MulAut.conj (g : G)).toMonoidHom := by
      rw [map_map]
      have heq : A.subtype.comp (ρ g).toMonoidHom =
          (MulAut.conj (g : G)).toMonoidHom.comp A.subtype := rfl
      rw [heq, ← map_map, subgroupOf_map_subtype, inf_comm]
    rw [hright, pointCore_intersection_conjugate A x.val g g.property]
  obtain ⟨B, hAlt, hN, hInv, hker⟩ :=
    BinaryPolarity.exists_invariant_form_of_elementary_hyperplanes ρ π hs ha he
  refine ⟨B, hAlt, hN, ?_, ?_⟩
  · intro g x y
    exact hInv g (Additive.ofMul x) (Additive.ofMul y)
  · intro x hx y
    exact hker ⟨x, hx⟩ y

/-- Original HS local data construct a pure self-centralizing elementary
sixteen with the actual normalizer-invariant point-core alternating form. -/
theorem TypeAt.exists_sixteen_point_core_form (h : TypeAt z V) :
    ∃ (A : Subgroup G) (hAe : IsElementaryAbelian 2 A), letI := hAe
      Nat.card A = 16 ∧ centralizer (A : Set G) = A ∧
      (∀ x ∈ A, x ≠ 1 → IsConj x z) ∧
      (∀ x ∈ A, x ≠ 1 → Nat.card (A ⊓ (involutionCentralizer x).pCoreIn 2 : Subgroup G) = 8) ∧
      ∃ B : LinearMap.BilinForm (ZMod 2) (Additive A), B.IsAlt ∧ B.Nondegenerate ∧
        (∀ (g : normalizer (A : Set G)) (x y : A),
          B (Additive.ofMul (A.normalizerMonoidHom g x))
            (Additive.ofMul (A.normalizerMonoidHom g y)) =
          B (Additive.ofMul x) (Additive.ofMul y)) ∧
        (∀ (x : A) (_hx : x ≠ 1) (y : A),
          B (Additive.ofMul x) (Additive.ofMul y) = 0 ↔
            (y : G) ∈ (involutionCentralizer (x : G)).pCoreIn 2) := by
  obtain ⟨u, c, b, E, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hAe, hA16,
    _, _, _, _, _, hCA, _, _, _, _, hpure, _, hpoints, _⟩ := h.exists_all_point_core_eights
  let A := E.val ⊔ zpowers b
  let : IsElementaryAbelian 2 A := hAe
  exact ⟨A, hAe, hA16, hCA, hpure, hpoints, h.sixteen_point_core_form A hA16 hpure hpoints⟩

end CFSG.Quasithin.HigmanSims
