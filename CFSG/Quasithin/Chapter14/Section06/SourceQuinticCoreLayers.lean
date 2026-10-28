module
public import CFSG.Quasithin.Chapter14.Section06.SourceQuinticFrattiniPoint
public import CFSG.Quasithin.Chapter14.Section06.SourceQuinticFrattiniReduction

/-!
# Exact full quintic core layers

The full-kernel Frattini bound removes the remaining kernel terms from the
original derived and Frattini reductions. Both full layers are the original
quintic span, and the next commutator is the original central line.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section06
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]

/-- The full core has derived and embedded Frattini subgroup equal to the
original quintic span; its third commutator is the original central line. -/
theorem source_quintic_full_core_layers
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃*
      Equiv.Perm (Fin 3))
    (H : Subgroup G) (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (hi : (T : Subgroup G).relIndex H = 5) :
    let U := conjugateSpanBy (localModule T M) H
    let Q := H.pCoreIn 2
    ⁅Q,Q⁆ = U ∧ (frattini Q).map Q.subtype = U ∧
      ⁅⁅Q,Q⁆,Q⁆ = centralInvolutions T := by
  let U := conjugateSpanBy (localModule T M) H
  let Q := H.pCoreIn 2
  let C := H ⊓ centralizer (U : Set G)
  have hZU : centralInvolutions T ≤ U :=
    (le_conjugateSpanBy _ _).trans (le_conjugateSpanBy _ _)
  have hphi : (frattini C).map C.subtype ≤ U :=
    (source_quintic_full_kernel_frattini_le_point hG T hempty hM hu hmany hcard e H hH hi).trans hZU
  have hCp : IsPGroup 2 C := (isPGroup_pCoreIn 2 H).to_le
    (source_quintic_span_centralizer_le_core hG T hM H hH hi)
  have hder : ⁅Q,Q⁆ = U := by
    rw [source_quintic_core_derived_reduction hG T hempty hM hu hmany hcard e H hH hi]
    exact sup_eq_left.mpr (derived_le_of_frattini_image_le hCp hphi)
  have hfrat : (frattini Q).map Q.subtype = U := by
    rw [source_quintic_core_frattini_reduction hG T hempty hM hu hmany hcard e H hH hi]
    exact sup_eq_left.mpr hphi
  refine ⟨hder,hfrat,?_⟩
  change ⁅⁅Q,Q⁆,Q⁆ = centralInvolutions T
  rw [hder]
  exact (source_quintic_core_commutators hG T hempty hM hu hmany hcard e H hH hi).2

end CFSG.Quasithin.Chapter14.Section06
