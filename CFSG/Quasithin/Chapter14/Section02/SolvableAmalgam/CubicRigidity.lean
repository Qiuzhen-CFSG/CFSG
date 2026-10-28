module
public import CFSG.Quasithin.Chapter14.Section02.SolvableAmalgam.SmallLocal.Orientation
public import CFSG.Quasithin.Chapter14.Section02.SolvableAmalgam.SmallLocal.G2DerivedRigidity
public import CFSG.Quasithin.Chapter14.Section02.SolvableAmalgam.SmallLocal.ExtraspecialRigidity.Source
public import CFSG.Quasithin.Chapter14.Section02.SolvableAmalgam.SmallLocal.AutM12.OriginalRigidity

/-!
# Original rigidity for the four cubic exceptional rows

The source recognition is forced into its original orientation by the central
involution in H. The derived G2 row is rigid by its quaternion-cyclic core;
the full G2 and M12 rows are rigid by the elementary-eight normalizer action.
For Aut(M12), the corrected nonsplit core alternative forces equality, while
the two quaternion alternatives supply an independent cubic whose diagonal
action violates the source plane normalizer. All maps and Sylow intersections
are those of the original marked pair. Once H equals Mc, the original
centralizer-factor decomposition gives M = YT.

Source: Aschbacher--Smith, Lemma 14.2.21, printed pp.988--989.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section02.SolvableAmalgam
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06 SmallLocal
open ChapterF.SourceAssembly ChapterF.GreenBook
variable {G : Type*} [Group G] [Finite G]

/-- All four original cubic rows force the selected local to be Mc and M to be YT. -/
theorem source_cubic_rigidity
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (H : Subgroup G) (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (eH : (H ⧸ pCore 2 H) ≃* Equiv.Perm (Fin 3)) :
    H = Mc ∧ M = sourceResidual M Mc ⊔ (T : Subgroup G) := by
  have c := cubic_source_context hG T hempty hM hu hmany hcard e H hH eH
  have hm := source_cubic_oriented_amalgam hG T hempty hM hu hmany hcard e H hH eH
  have he : H = Mc := by
    rcases hm with hg | hg | hm | ha
    · obtain ⟨f⟩ := hg
      exact (source_g2_derived_rigidity hG T hempty hM hu hmany hcard e H hH
        f.left.symm).1
    · exact ExtraspecialRigidity.g2_rigidity T M Mc H c hg
    · exact ExtraspecialRigidity.m12_rigidity T M Mc H c hm
    · exact AutM12.OriginalRigidity.source_rigidity T M Mc H c ha
  exact ⟨he,m_eq_yt_of_rigidity H M Mc (sourceResidual M Mc) (T : Subgroup G)
    (centralInvolutions T) (localModule T M) he c.H_inf_M c.Mc_centralizer
    (le_conjugateSpanBy _ _) c.decomposition (sourceResidual_le _ _) hM.1.2⟩

end CFSG.Quasithin.Chapter14.Section02.SolvableAmalgam
