module

public import CFSG.Quasithin.Chapter14.Section04.LargerDimension.Mathieu.ActorCatalogue.NativeParabolics.Cubic
public import CFSG.Quasithin.Chapter14.Section04.LargerDimension.Mathieu.ActorCatalogue.NativeParabolics.DesignProjection
public import CFSG.Quasithin.Chapter14.Section04.LargerDimension.Mathieu.ActorCatalogue.NativeParabolics.Residuals
public import CFSG.Quasithin.Chapter14.Section04.LargerDimension.Mathieu.ActorCatalogue.NativeParabolics.Catalogue.LocalLifts
public import CFSG.Quasithin.Chapter14.Section04.LargerDimension.Mathieu.ActorCatalogue.NativeParabolics.Catalogue.DesignContract
public import CFSG.Quasithin.Chapter14.Section04.LargerDimension.Mathieu.ActorCatalogue.NativeParabolics.Catalogue.DesignPositions
public import CFSG.Quasithin.Chapter14.Section04.LargerDimension.Mathieu.ActorCatalogue.NativeParabolics.Catalogue.PartitionAction

/-!
# Assembly of the native Mathieu rank-one catalogue

Every literal residual actor comes from an index-three overgroup of the
specified Sylow subgroup. Besides the cubic overgroup, these project
injectively to the design group. A design catalogue in common coordinates,
together with the binary nonfixation of partition lifts, identifies the supplied
Borel as the pair--hexad type and constructs the other lift. Uniqueness of lifts
then exhausts all actors, retaining their literal design images and common hexad.

The theorem `exists_catalogue` discharges the two inputs to the retained
conditional assembly `catalogue_of_design`: the design classification comes
from `DesignPositions`, and partition nonfixation comes from the original
binary column action in `PartitionAction`. Its hypotheses are just the supplied
nonzero point and index-three Borel containments. The parent retains hexad
generation and the separate overlap quotient of Lemma 14.4.12.

Source: Aschbacher--Smith, 14.4.12, printed pp.1011--1012; case 14.4.2(6),
printed p.1006; H.12.1, printed pp.393--394.
-/

@[expose] public section
open Subgroup
open Sporadic.Mathieu
open CFSG.Quasithin.Chapter14.Section04.LargerDimension
open CFSG.Quasithin.Chapter14.Section04.LargerDimension.Mathieu.ActorCatalogue.Native
open CFSG.Quasithin.Chapter14.Section04.LargerDimension.Mathieu.ActorCatalogue.NativeParabolics
open scoped Pointwise
namespace CFSG.Quasithin.Chapter14.Section04.LargerDimension.Mathieu.ActorCatalogue.NativeParabolics.Catalogue
lemma residual_not_fixed (S : Sylow 2 Model) {v : Space} {P : Subgroup Model}
    (hSP : (S : Subgroup Model) ≤ P) (hSv : (S : Subgroup Model) ≤ pointCentralizer v)
    (hm : ¬ P ≤ pointCentralizer v) : ¬ twoResidual P ≤ pointCentralizer v := by
  intro h
  apply hm
  rw [← residual_sup_sylow S P hSP]
  exact sup_le h hSv

lemma firstActor_ne_residual_of_disjoint {P : Subgroup Model} (hd : Disjoint cubic P) :
    twoResidual (pCore 3 Model) ≠ twoResidual P := by
  rw [firstActor_eq_cubic]
  intro he
  have hcP : cubic ≤ P := he ▸ map_subtype_le (pResidual 2 P)
  have hb : cubic = ⊥ := le_antisymm (fun x hx => hd.le_bot ⟨hx, hcP hx⟩) bot_le
  have h := cubic_card
  rw [hb, card_bot] at h
  omega

/-- Conditional native assembly. The design classification and the binary
partition nonfixation are the two geometric inputs; every cubic-cover lift,
uniqueness, actor condition, distinction, and family-exhaustion step is proved
here. `exists_catalogue` below discharges both inputs. -/
lemma catalogue_of_design (S : Sylow 2 Model) {v : Space} (hv : v ≠ 0)
    (B : Subgroup Model) (hSB : (S : Subgroup Model) ≤ B)
    (hB : B ≤ pointCentralizer v) (hiB : (S : Subgroup Model).relIndex B = 3)
    (hdesign : ∃ g, DesignCatalogueAt (S.mapSurjective designProjection_surjective) g)
    (hmove : ∀ (g : m22DesignAut) (P : Subgroup Model), P ∈ rankOneOvergroups S →
      Disjoint cubic P → P.map designProjection = partitionAt g → ¬ P ≤ pointCentralizer v) :
    ∃ (P : Subgroup Model) (g : m22DesignAut),
      P ∈ rankOneOvergroups S ∧ Disjoint cubic P ∧
      P.map designProjection = partitionAt g ∧ B.map designProjection = pairAt g ∧
      P ≤ hexadPreimage (g • m22Hexad123) ∧ B ≤ hexadPreimage (g • m22Hexad123) ∧
      ThreeExtension ⊤ (S : Subgroup Model) (twoResidual P) ∧
      ¬ twoResidual P ≤ pointCentralizer v ∧
      twoResidual (pCore 3 Model) ≠ twoResidual P ∧
      twoResidual (pCore 3 Model) ≠ twoResidual B ∧ twoResidual P ≠ twoResidual B ∧
      XFamily ⊤ (S : Subgroup Model) =
        {twoResidual (pCore 3 Model), twoResidual P, twoResidual B} := by
  obtain ⟨g, dg⟩ := hdesign
  have hdB := (cubic_disjoint_pointCentralizer hv).mono_right hB
  have hBm : B.map designProjection ∈ rankOneOvergroups (S.mapSurjective designProjection_surjective) :=
    ⟨map_mono hSB, (relIndex_image_of_disjoint S hSB hdB).trans hiB⟩
  have hmB : B.map designProjection = pairAt g := by
    rw [dg.overgroups, Set.mem_insert_iff, Set.mem_singleton_iff] at hBm
    rcases hBm with hm | hm
    · exact (hmove g B ⟨hSB, hiB⟩ hdB hm hB).elim
    · exact hm
  have hpart : partitionAt g ∈ rankOneOvergroups (S.mapSurjective designProjection_surjective) := by
    rw [dg.overgroups]
    exact Set.mem_insert _ _
  obtain ⟨epart⟩ := dg.partition_quotient
  obtain ⟨epair⟩ := dg.pair_quotient
  obtain ⟨P, hP, hmP, hdP⟩ := exists_rankOne_lift S (partitionAt g) hpart epart
  have hnot := residual_not_fixed S hP.1 (hSB.trans hB) (hmove g P hP hdP hmP)
  have hfamily : rankOneOvergroups S = {cubic ⊔ (S : Subgroup Model), P, B} := by
    ext R
    constructor
    · intro hR
      rcases eq_cubic_sup_or_disjoint S hR with hRc | hdR
      · exact Set.mem_insert_iff.mpr (Or.inl hRc)
      have hRm : R.map designProjection ∈ rankOneOvergroups (S.mapSurjective designProjection_surjective) :=
        ⟨map_mono hR.1, (relIndex_image_of_disjoint S hR.1 hdR).trans hR.2⟩
      rw [dg.overgroups, Set.mem_insert_iff, Set.mem_singleton_iff] at hRm
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      rcases hRm with hRm | hRm
      · have heR : Nonempty (((R.map designProjection ⊓ M22ValueBound.Concrete.inner : Subgroup m22DesignAut) ⧸
          pCore 2 (R.map designProjection ⊓ M22ValueBound.Concrete.inner : Subgroup m22DesignAut)) ≃* Equiv.Perm (Fin 3)) := by
          rw [hRm]
          exact ⟨epart⟩
        exact Or.inr (Or.inl (lift_unique_of_inner_symmetricThree S R P hR.1 hP.1 hdR hdP (hRm.trans hmP.symm) heR.some))
      · have heR : Nonempty (((R.map designProjection ⊓ M22ValueBound.Concrete.inner : Subgroup m22DesignAut) ⧸
          pCore 2 (R.map designProjection ⊓ M22ValueBound.Concrete.inner : Subgroup m22DesignAut)) ≃* Equiv.Perm (Fin 3)) := by
          rw [hRm]
          exact ⟨epair⟩
        exact Or.inr (Or.inr (lift_unique_of_inner_symmetricThree S R B hR.1 hSB hdR hdB (hRm.trans hmB.symm) heR.some))
    · simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      rintro (rfl | rfl | rfl)
      · exact cubic_sup_mem_rankOneOvergroups S
      · exact hP
      · exact ⟨hSB, hiB⟩
  refine ⟨P, g, hP, hdP, hmP, hmB, ?_, ?_,
    residual_threeExtension_of_index_three S P hP.1 hP.2, hnot,
    firstActor_ne_residual_of_disjoint hdP, firstActor_ne_borelResidual B hv hB, ?_,
    XFamily_eq_of_rankOneOvergroups S P B hfamily⟩
  · exact map_le_iff_le_comap.mp (hmP ▸ partitionAt_le_hexad g)
  · exact map_le_iff_le_comap.mp (hmB ▸ pairAt_le_hexad g)
  · intro he
    exact hnot (he ▸ borelResidual_le_pointCentralizer B hB)

/-- The native three-actor catalogue in the Mathieu case of 14.4.12.
The supplied Borel is the pair--hexad lift; the remaining noncubic lift is
the partition parabolic in the same hexad coordinates. Its residual moves
the nonzero binary point, and these two residuals together with the cubic
actor are pairwise distinct and exhaust the literal source family.

No design classification or binary nonfixation hypothesis remains. Sylow
fixation of the point follows from `hSB` and `hB`. -/
theorem exists_catalogue (S : Sylow 2 Model) {v : Space} (hv : v ≠ 0)
    (B : Subgroup Model) (hSB : (S : Subgroup Model) ≤ B)
    (hB : B ≤ pointCentralizer v) (hiB : (S : Subgroup Model).relIndex B = 3) :
    ∃ (P : Subgroup Model) (g : m22DesignAut),
      P ∈ rankOneOvergroups S ∧ Disjoint cubic P ∧
      P.map designProjection = partitionAt g ∧ B.map designProjection = pairAt g ∧
      P ≤ hexadPreimage (g • m22Hexad123) ∧ B ≤ hexadPreimage (g • m22Hexad123) ∧
      ThreeExtension ⊤ (S : Subgroup Model) (twoResidual P) ∧
      ¬ twoResidual P ≤ pointCentralizer v ∧
      twoResidual (pCore 3 Model) ≠ twoResidual P ∧
      twoResidual (pCore 3 Model) ≠ twoResidual B ∧ twoResidual P ≠ twoResidual B ∧
      XFamily ⊤ (S : Subgroup Model) =
        {twoResidual (pCore 3 Model), twoResidual P, twoResidual B} :=
  catalogue_of_design S hv B hSB hB hiB
    (exists_design_catalogue (S.mapSurjective designProjection_surjective))
    (partition_not_le_pointCentralizer S v hv)


end CFSG.Quasithin.Chapter14.Section04.LargerDimension.Mathieu.ActorCatalogue.NativeParabolics.Catalogue
