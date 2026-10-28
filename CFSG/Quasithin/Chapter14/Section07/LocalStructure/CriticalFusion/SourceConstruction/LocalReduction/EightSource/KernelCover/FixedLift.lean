module
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.LinearReduction.Orthogonal.OffenderModels.StrongSections.Extensions.PerfectCover
public import Theory.Representation.BinaryPermutation.AlternatingEightSylowFixed
public import Theory.Representation.BinaryPermutation.EightSixMovedFixed

/-!
# A Sylow-fixed lift distinguishes the natural module from its cover

In the seven-dimensional augmentation core, a Sylow-fixed vector is constant,
so every equivariant map to the natural six-space kills it. A surjection from
a natural-or-core module with a Sylow-fixed vector mapping nontrivially must
therefore be an isomorphism.
-/

public section
open Subgroup Representation Representation.BinaryOffender BinaryPermutation
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.EightSource.KernelCover
open Chapter13.Section08.ComponentSieve.AlternatingAndLinear.LinearReduction
variable {H U : Type*} [Group H] [Finite H] [AddCommGroup U] [Module (ZMod 2) U]
  [FiniteDimensional (ZMod 2) U]

/-- A nonzero natural image of a Sylow-fixed vector excludes the augmentation
cover and makes the displayed surjection injective. -/
theorem injective_of_naturalOrCover_fixed_lift
    (ρ : Representation (ZMod 2) H U) (eH : H ≃* Equiv.Perm (Fin 8))
    (hm : IsEightNaturalOrCover ρ eH)
    (p : U →ₗ[ZMod 2] natural (Fin 8))
    (hp : ∀ g u, p (ρ g u) = naturalRepresentation (Fin 8) (eH g) (p u))
    (hsur : Function.Surjective p) (P : Sylow 2 H)
    (x : U) (hx : ∀ g ∈ (P : Subgroup H), ρ g x = x) (hpx : p x ≠ 0) :
    Function.Injective p := by
  rcases hm with ⟨e, _⟩ | ⟨e, he⟩
  · exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank e.finrank_eq).mpr hsur
  · let P' := P.mapSurjective (f := eH.toMonoidHom) eH.surjective
    obtain ⟨S,hS⟩ := P'.exists_subgroupOf_eq_of_normal (alternatingGroup (Fin 8))
    have hc : (e x).val ∈ constants (Fin 8) := by
      apply alternatingEight_core_sylow_fixed_constant S
      intro g hg
      rw [hS] at hg
      obtain ⟨k,hk,hkg⟩ := hg
      change eH k = g.val at hkg
      change coreRepresentation (Fin 8) g.val (e x) = e x
      rw [←hkg,←he,hx k hk]
    apply False.elim
    apply hpx
    apply eight_natural_fixed_eq_zero
    intro g
    let k := eH.symm g.val
    have hxk : ρ k x = x := by
      apply e.injective
      rw [he]
      change coreRepresentation (Fin 8) (eH (eH.symm g.val)) (e x) = e x
      rw [eH.apply_symm_apply]
      exact (core_fixed_iff_constant (by simp : 3 ≤ Nat.card (Fin 8)) (e x)).mpr hc g
    have hh := hp k x
    rw [hxk] at hh
    change naturalRepresentation (Fin 8) g.val (p x) = p x
    simpa only [k,eH.apply_symm_apply] using hh.symm

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.EightSource.KernelCover
