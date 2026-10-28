module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.AlternatingBranches.OrdinarySeven.SourcePlacement.Marking.ModuleComparison.Representation
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.AlternatingBranches.OrdinarySeven.SourcePlacement.Marking.ModuleComparison.Summand
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.AlternatingBranches.OrdinarySeven.SourcePlacement.Marking.ModuleComparison.FixedVectors
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.AlternatingBranches.OrdinarySeven.SourcePlacement.Marking.Baumann

/-!
# Fixed-vector detection through the original plus projection

An actual natural summand carries the three pair-indicator vectors into W₀.
An element centralizing C_W(J(Tᵥ)) fixes those vectors, so its permutation
lies in the marked three-transposition subgroup. Injectivity of the original
permutation action gives the centralizer bound inside G⁺. The existing
Baumann lemma then gives Baum(Tᵥ)⁺ = J(Tᵥ)⁺.

This is a conditional application of the explicit splitting interface; its
construction from the chosen ordinary block model remains required. The
centralizer bound and Baumann equality are conclusions, not assumptions.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, 13.6.22,
printed p.932, and the fixed-vector argument of B.2.20.
-/

@[expose] public section
open Subgroup Equiv
open Representation.BinaryOffender
open scoped IsMulCommutative
open CFSG.Quasithin.Chapter13.Section06.CentralizerReduction
open CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.AlternatingBranches.OrdinarySeven.SourcePlacement.Marking.ModuleComparison
variable {G : Type*} [Group G]

/-- Fixed vectors in the natural summand detect the original centralizer image.
This consumes the actual summand, not a fixed-codimension assertion. -/
theorem fixed_centralizer_le_thompson
    (K L T : Subgroup G) (z v : G)
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G))
    [IsElementaryAbelian 2 (WK K L T z v)]
    (hWT : WK K L T z v ≤ Tv T v)
    (φ : Gplus K L T z v hL hz →* Perm (Fin 7)) (hφ : Function.Injective φ)
    (d : NaturalSummand (representation K L T z v hL hz hWT) φ)
    (g : Perm (Fin 7))
    (hg : ((plusImage K L T z v hL hz
      (Stellmacher.elementaryAbelianMaxJ (Tv T v))).map φ).map
        (MulAut.conj g).toMonoidHom = threeTranspositions) :
    plusImage K L T z v hL hz
      (Tv T v ⊓ centralizer
        (WK K L T z v ⊓ centralizer
          (Stellmacher.elementaryAbelianMaxJ (Tv T v) : Set G) : Set G)) ≤
      plusImage K L T z v hL hz (Stellmacher.elementaryAbelianMaxJ (Tv T v)) := by
  let J := Stellmacher.elementaryAbelianMaxJ (Tv T v)
  have hJA : J ≤ plusActor K L T v :=
    (sSup_le fun _ hA => hA.1).trans le_sup_right
  rintro _ ⟨t, ht, rfl⟩
  have hm : φ (plusMk K L T z v hL hz t) ∈
      (plusImage K L T z v hL hz J).map φ := by
    apply natural_fixed_detection_conjugate _ g hg
    intro w hw
    have hfix : d.inclusion w ∈ fixedSpace (representation K L T z v hL hz hWT)
        (plusImage K L T z v hL hz J) := by
      intro j
      exact (d.inclusion_equivariant j.val w).trans
        (congrArg d.inclusion (hw ⟨φ j.val, mem_map_of_mem φ j.property⟩))
    have hc := (mem_fixedSpace_image K L T z v hL hz hWT J hJA (d.inclusion w)).mp hfix
    have he : representation K L T z v hL hz hWT (plusMk K L T z v hL hz t)
        (d.inclusion w) = d.inclusion w := by
      apply Additive.toMul.injective
      apply Subtype.ext
      apply Subtype.ext
      rw [representation_apply]
      have hwK : (((d.inclusion w).toMul : plusActor K L T v) : G) ∈ WK K L T z v :=
        (d.inclusion w).toMul.property
      have htcomm : (((d.inclusion w).toMul : plusActor K L T v) : G) * (t : G) =
          (t : G) * (((d.inclusion w).toMul : plusActor K L T v) : G) := ht.2 _ ⟨hwK, hc⟩
      rw [← htcomm, mul_inv_cancel_right]
    apply d.inclusion_injective
    exact (d.inclusion_equivariant (plusMk K L T z v hL hz t) w).symm.trans he
  obtain ⟨j, hj, he⟩ := hm
  exact hφ he ▸ hj

/-- The natural summand discharges the fixed-centralizer premise of Baumann's
lemma, for any simultaneous conjugation giving the three pair swaps. -/
theorem baumann_image_eq_thompson [Finite G]
    (K L T : Subgroup G) (z v : G)
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G))
    [IsElementaryAbelian 2 (WK K L T z v)]
    (hWT : WK K L T z v ≤ Tv T v)
    (φ : Gplus K L T z v hL hz →* Perm (Fin 7)) (hφ : Function.Injective φ)
    (d : NaturalSummand (representation K L T z v hL hz hWT) φ)
    (g : Perm (Fin 7))
    (hg : ((plusImage K L T z v hL hz
      (Stellmacher.elementaryAbelianMaxJ (Tv T v))).map φ).map
        (MulAut.conj g).toMonoidHom = threeTranspositions) :
    plusImage K L T z v hL hz (ChapterB.baumann (Tv T v)) =
      plusImage K L T z v hL hz (Stellmacher.elementaryAbelianMaxJ (Tv T v)) :=
  baumann_plus_eq_of_fixed_centralizer K L T z v hL hz hWT
    (fixed_centralizer_le_thompson K L T z v hL hz hWT φ hφ d g hg)

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.AlternatingBranches.OrdinarySeven.SourcePlacement.Marking.ModuleComparison
end
