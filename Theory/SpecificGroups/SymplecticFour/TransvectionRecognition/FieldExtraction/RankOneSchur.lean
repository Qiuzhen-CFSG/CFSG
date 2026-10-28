module
public import Theory.Representation.AbsolutelyIrreducible
public import Theory.SpecificGroups.SymplecticFour.TwoConjugate.MovingPair
public import Theory.SpecificGroups.SymplecticFour.InvolutionTypes
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.LinearAlgebra.BilinearForm.Properties

/-!
# Rank-one Schur bridge for the actual moving pair

A finite-dimensional irreducible action containing an operator with
one-dimensional displacement has scalar commutant.  We retain the actual
coefficient field throughout: this bridge proves absolute irreducibility over
that field and makes no binary-irreducibility or prime-field assertion.

For the source E.2.7 pair, the rank-one witness is an element of
`oppositePair V`; no root-axis intersection with the original `V` is inferred.
-/

@[expose] public noncomputable section
set_option linter.style.haveILetI false
namespace Representation.RankOneSchur
variable {F G V : Type*} [Field F] [Group G] [AddCommGroup V] [Module F V]
  [FiniteDimensional F V] (ρ : Representation F G V) [ρ.IsIrreducible]

omit [FiniteDimensional F V] in
/-- An irreducible action with a rank-one displacement has scalar commutant. -/
theorem end_scalar_of_rank_one (g : G)
    (hr : Module.finrank F (LinearMap.range (ρ g - 1)) = 1)
    (f : ρ.IntertwiningMap ρ) : ∃ c : F, f = algebraMap F (Representation.End ρ) c := by
  let W := LinearMap.range (ρ g - 1)
  have hW : W ≠ ⊥ := by
    intro h
    have hh := hr
    change Module.finrank F W = 1 at hh
    rw [h,finrank_bot] at hh
    exact Nat.zero_ne_one hh
  obtain ⟨v,hv,hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW
  have hfv : f v ∈ W := by
    obtain ⟨w,rfl⟩ := hv
    refine ⟨f w,?_⟩
    change ρ g (f w) - f w = f (ρ g w - w)
    rw [map_sub,Representation.IntertwiningMap.isIntertwining]
  have he := eq_span_singleton_of_mem_of_finrank_eq_one hr hv hv0
  change f v ∈ LinearMap.range (ρ g - 1) at hfv
  rw [he] at hfv
  obtain ⟨c,hc⟩ := Submodule.mem_span_singleton.mp hfv
  refine ⟨c,?_⟩
  have hz : f - algebraMap F (Representation.End ρ) c = 0 := by
    rcases IsIrreducible.injective_or_eq_zero
        (f - algebraMap F (Representation.End ρ) c) with hinj | hz
    · have h : (f - algebraMap F (Representation.End ρ) c) v =
          (f - algebraMap F (Representation.End ρ) c) 0 := by
        change f v - c • v = _
        rw [hc,sub_self,map_zero]
      exact (hv0 (hinj h)).elim
    · exact hz
  exact sub_eq_zero.mp hz

/-- A rank-one displacement forces absolute irreducibility over the actual
coefficient field; no irreducibility over its prime subfield is asserted. -/
theorem absolutelyIrreducible_of_rank_one (g : G)
    (hr : Module.finrank F (LinearMap.range (ρ g - 1)) = 1) :
    ρ.IsAbsolutelyIrreducible := by
  apply (isAbsolutelyIrreducible_iff_surjective ρ).mpr
  intro f
  obtain ⟨c,hc⟩ := end_scalar_of_rank_one ρ g hr f
  exact ⟨c,hc.symm⟩

/-- A nondegenerate invariant form is unique up to coefficient scalar in an
irreducible representation with a rank-one displacement. -/
theorem invariant_form_scalar_of_rank_one (g : G)
    (hr : Module.finrank F (LinearMap.range (ρ g - 1)) = 1)
    (B : LinearMap.BilinForm F V) (hB : B.Nondegenerate)
    (hBinv : ∀ a v w, B (ρ a v) (ρ a w) = B v w)
    (C : LinearMap.BilinForm F V)
    (hCinv : ∀ a v w, C (ρ a v) (ρ a w) = C v w) :
    ∃ c : F, C = c • B := by
  let T : Module.End F V := (B.toDual hB).symm.toLinearMap.comp C
  have hT (v w : V) : B (T v) w = C v w :=
    LinearMap.BilinForm.apply_toDual_symm_apply (hB := hB) (C v) w
  let f : ρ.IntertwiningMap ρ := {
    toLinearMap := T
    isIntertwining' a := by
      apply LinearMap.ext
      intro v
      apply (B.toDual hB).injective
      apply LinearMap.ext
      intro w
      obtain ⟨w,rfl⟩ := (ρ.apply_bijective a).surjective w
      change B (T (ρ a v)) (ρ a w) = B (ρ a (T v)) (ρ a w)
      rw [hT,hCinv,hBinv,hT] }
  obtain ⟨c,hc⟩ := end_scalar_of_rank_one ρ g hr f
  refine ⟨c,?_⟩
  apply LinearMap.ext
  intro v
  apply LinearMap.ext
  intro w
  have hf : T v = c • v := congrArg (fun f : ρ.End => f v) hc
  change C v w = c • B v w
  rw [←hT,hf]
  simp only [map_smul,LinearMap.smul_apply]
end Representation.RankOneSchur

namespace Theory.SpecificGroups.SymplecticFour.TwoConjugate
open Representation
open Subgroup Theory.SpecificGroups.SymplecticFour
open DiagramAutomorphisms EvenBorelTorus CentralRootGeometry
open Representation.OneCohomology.SymplecticFour
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

/-- The actual moving opposite pair is absolutely irreducible after a
rank-one displacement witness in that pair.  The witness remains in
`oppositePair V`, so no root is forced into the original central subgroup. -/
theorem pairAction_absolutelyIrreducible_of_moving_rank_one
    (hq : 2 < Nat.card F)
    (a : ActorReduction.stabilizer (F := F)) (ha : ¬PreservesDiagram a.val)
    (V : Subgroup (Sp F)) (hV : V.map a.val.toMonoidHom = V)
    (hc : V ≤ (center (unipotent (F := F))).map (unipotent (F := F)).subtype)
    (hr : 2 < Nat.card V)
    (g : oppositePair V)
    (hdisp : Module.finrank F (LinearMap.range ((pairAction V) g - 1)) = 1) :
    (pairAction V).IsAbsolutelyIrreducible := by
  haveI := pairAction_irreducible_of_moving_actor hq a ha V hV hc hr
  exact Representation.RankOneSchur.absolutelyIrreducible_of_rank_one
    (pairAction V) g hdisp

/-- The same bridge with the source's actual b₁/transvection predicate. -/
theorem pairAction_absolutelyIrreducible_of_moving_isB1
    (hq : 2 < Nat.card F)
    (a : ActorReduction.stabilizer (F := F)) (ha : ¬PreservesDiagram a.val)
    (V : Subgroup (Sp F)) (hV : V.map a.val.toMonoidHom = V)
    (hc : V ≤ (center (unipotent (F := F))).map (unipotent (F := F)).subtype)
    (hr : 2 < Nat.card V)
    (g : oppositePair V)
    (hg : InvolutionTypes.IsB1 (g : Sp F)) :
    (pairAction V).IsAbsolutelyIrreducible := by
  apply pairAction_absolutelyIrreducible_of_moving_rank_one hq a ha V hV hc hr g
  change Module.finrank F (InvolutionTypes.movedSpace (g : Sp F)) = 1
  exact hg.2

end Theory.SpecificGroups.SymplecticFour.TwoConjugate
