module
public import CFSG.Quasithin.ChapterE.Section02.Witnesses.ResidualComponentBender
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.Classification.ThreeFree
public import Theory.GroupTheory.NormalCenterQuotient

/-!
# An order-two module image excludes the three-free nonsolvable rows

Pass from the original minimal parabolic to its literal maximal-core
quotient. The original nonzero subgroup has image of order two and is
normalized by the actual maximal subgroup, so it supplies a central
point there. The complete A.3.6 catalogue identifies a generating simple
component as a Suzuki group when three does not divide the group order.
Pointwise Borel rigidity then excludes that central point for both normal
and exchanged components. No numerical generation-parameter equality
across a quotient is used.

Source: a sufficient specialization of the E.2.2/B.6.8 sieve used in
Aschbacher--Smith 8.2.9(3), printed p.720, refs/quasithin.pdf. The Chapter12
application constructs the order-two image from the original code action.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter7.NormalizedSource.MathieuShadowRows
open ChapterB ChapterE
variable {X : Type*} [Group X] [Finite X]

/-- The original maximal-invariant subgroup of quotient order at most two
cannot survive in a nonsolvable three-free SQTK minimal parabolic. -/
theorem source_three_free_image_two_impossible
    (hX : IsSQTK KnownSimple.IsKnownSimple X)
    (S : Sylow 2 X) (hP : IsMinimalParabolicOver S ⊤)
    (hs : ¬ Group.IsSolvable X) (h3 : ¬ 3 ∣ Nat.card X)
    (W : Subgroup X) (hWS : W ≤ S)
    (hout : ¬ W ≤ minimalParabolicCore S hP)
    (hMW : minimalParabolicMax S hP ≤ normalizer (W : Set X))
    (hcard : Nat.card (W.map (QuotientGroup.mk' (pCore 2 X))) ≤ 2) : False := by
  let J := minimalParabolicCore S hP
  let q := QuotientGroup.mk' J
  let R := S.mapSurjective (QuotientGroup.mk'_surjective J)
  let A := W.map q
  let : Group.IsSolvable J := minimalParabolic_core_solvable S hP
  have hsQ : ¬ Group.IsSolvable (X ⧸ J) := fun hx =>
    hs ((Group.isSolvable_iff_subgroup_quotient J).mpr ⟨inferInstance,hx⟩)
  have hmin := (Structure.source_star_minimal_core_free S hP).1
  have hcore : minimalParabolicCore R hmin = ⊥ :=
    (Structure.source_star_minimal_core_free S hP).2
  have hrad : solvableRadical (X ⧸ J) = ⊥ :=
    (minimalParabolic_nonsolvable_core_eq_radical R hmin hsQ).symm.trans hcore
  have hsqtk := Structure.source_star_sqtk ChapterA.Section02.theoremA_knownSimple hX S hP hs
  have htwo : pCore 2 (X ⧸ J) = ⊥ := le_bot_iff.mp
    ((minimalParabolicTwoCore_le_core R hmin).trans hcore.le)
  obtain ⟨K,hK,_,hgen,_⟩ := Structure.source_original_component hX S hP hs
  let D := K.map q
  have hi := Structure.source_component_simple_image S hP hs K hK hgen
  let : IsSimpleGroup D := hi.1
  have hc := ChapterA.SQTKStructure.a36Input_of_theoremsAC
    (fun _ _ _ => ChapterA.Section02.theoremA_knownSimple)
    (fun _ _ _ => ChapterA.Section02.theoremC_knownSimple) _ hsqtk htwo D hi.2.1.isCComponent
  have hD3 : ¬ 3 ∣ Nat.card D := fun hd =>
    h3 (hd.trans (D.card_subgroup_dvd_card.trans (card_quotient_dvd_card J)))
  obtain ⟨m,hm,he⟩ := hc.suzuki_of_three_free hD3
  have hb : ClassificationModels.IsBenderModel D := .suzuki m hm he
  let M := minimalParabolicMax R hmin
  have hmax : M = (minimalParabolicMax S hP).map q :=
    (minimalParabolicMax_map_core S hP q (QuotientGroup.mk'_surjective J)
      (by rw [QuotientGroup.ker_mk'])).symm
  have hAM : M ≤ normalizer (A : Set (X ⧸ J)) := by
    rw [hmax]
    exact (map_mono hMW).trans (le_normalizer_map q)
  have hAin : A ≤ M := by
    rw [hmax]
    exact map_mono (hWS.trans (minimalParabolicMax_spec S hP).2)
  have hAn : A ≠ ⊥ := by
    intro he
    exact hout (by simpa only [q,QuotientGroup.ker_mk'] using (map_eq_bot_iff W).mp he)
  let f : (X ⧸ pCore 2 X) →* (X ⧸ J) := QuotientGroup.map _ _ (MonoidHom.id X)
    (by simpa using minimalParabolicTwoCore_le_core S hP)
  have hmap : (W.map (QuotientGroup.mk' (pCore 2 X))).map f = A := by
    rw [map_map]; rfl
  have hsmall : Nat.card A ≤ 2 := by
    rw [←hmap]
    exact (Nat.le_of_dvd Nat.card_pos (card_dvd_of_surjective
      (f.subgroupMap _) (f.subgroupMap_surjective _))).trans hcard
  have htwoA : Nat.card A = 2 := by
    have hp := Nat.card_pos (α := A)
    have hn : Nat.card A ≠ 1 := fun he => hAn (Subgroup.card_eq_one.mp he)
    omega
  let : (A.subgroupOf M).Normal := normal_subgroupOf_of_le_normalizer hAM
  have htwoM : Nat.card (A.subgroupOf M) = 2 :=
    (Nat.card_congr (subgroupOfEquivOfLe hAin).toEquiv).trans htwoA
  have hcentral := central_of_normal_card_two (A.subgroupOf M) htwoM
  have hex : ∃ z : X ⧸ J, z ∈ A ∧ z ≠ 1 := by
    by_contra! he
    exact hAn (eq_bot_iff.mpr he)
  obtain ⟨z,hz,hzne⟩ := hex
  apply hzne
  apply Witnesses.PairedBender.component_bender_center_point_eq_one
    hsqtk.stronglyQuasithin R hmin hrad D hi.2.1 hi.2.2.2 hb z
  exact ⟨⟨z,hAin hz⟩,hcentral hz,rfl⟩

end CFSG.Quasithin.Chapter7.NormalizedSource.MathieuShadowRows
