module
public import CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.Centralizers.Pure.Sylows.Four.XiFixed
public import CFSG.Quasithin.ChapterA.Section04.Signalizers.NormalizerAction

/-!
# The Sylow kernel in the original pure-point component action

The two-core of the full marked Thompson normalizer is the marked offender.
Transport through the original LT action puts O₂(XT) inside the point
subgroup T₁: its image is the Thompson image, and its action kernel already
centralizes the marked point. A.4.2 identifies C_T(X/O₂(X)) with O₂(XT).
Restricting a trivial action on a containing section then gives
C_T(Y/O₂(Y)) ≤ T₁ whenever X ≤ Y.

Both chosen-module applications retain the original Sylow, pure point and
contrary ambient-Sylow branch. No MS input or maximality input is needed.
The faithful section quotient and its component application are in Quotient.
The remaining component exclusions and final Sylow/fusion/closure assembly
belong to qt-d-double-natural-pure-fusion; qt-d-double-natural-centralizers
supplies the original earlier inputs.
Source: Aschbacher--Smith 12.1.4, printed pp.790--791, and A.4.2, p.57.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterH.NaturalDual.SourceSetup
open SourceFourActors
variable {M E : Type*} [Group M] [AddCommGroup E] [Module (ZMod 2) E]
  (S : SourceSetup 4 M E) (P : Sylow 2 M)

private theorem four_A0_normalizer_core :
    (normalizer (A0 S P : Set M)).pCoreIn 2 = A0 S P := by
  apply Subgroup.map_injective (f := (permutation S P).toMonoidHom) (permutation S P).injective
  rw [map_pCoreIn_of_injective 2 _ _ (permutation S P).injective,
    S.four_A0_normalizer P]
  have ha : (A0 S P).map (permutation S P).toMonoidHom =
      BinaryNaturalDual.FourActors.permutationA0 := by
    change (A0 S P).map (BinaryNaturalDual.FourActors.permutationEquiv.toMonoidHom.comp
      (group S P).toMonoidHom) = _
    rw [←map_map,actor_map]
    exact BinaryNaturalDual.FourActors.PermutationCatalogue.actor_map 0
  rw [ha,BinaryNaturalDual.FourActors.PermutationCatalogue.permutationA0_eq_kleinGroup]
  exact Theory.SpecificGroups.SymmetricEight.FourBlockCoreAction.fourStabilizer_pCoreIn
end CFSG.Quasithin.ChapterH.NaturalDual.SourceSetup

namespace CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.PureFourXi
open ChapterA.Section04
variable {G : Type*} [Group G] [Finite G]

/-- The Sylow section centralizer is exactly the two-core of the join. -/
private theorem sylow_sectionCentralizer_eq_core (T : Sylow 2 G) (X : Subgroup G)
    (hX : IsPPerfect 2 X) (hTX : (T : Subgroup G) ≤ normalizer (X : Set G)) :
    twoSectionCentralizer X (T : Subgroup G) = (X ⊔ (T : Subgroup G)).pCoreIn 2 := by
  let C := twoSectionCentralizer X (normalizer (X : Set G))
  obtain ⟨P,hP⟩ := sylow_core_sectionCentralizer T X hX hTX
  have hcoreT : (X ⊔ (T : Subgroup G)).pCoreIn 2 ≤ (T : Subgroup G) := by
    simpa only [Sylow.coe_subtype,map_subgroupOf_eq_of_le (show (T : Subgroup G) ≤
      X ⊔ (T : Subgroup G) from le_sup_right)] using
      pCoreIn_le_sylow (X ⊔ (T : Subgroup G)) (T.subtype le_sup_right)
  have hPT : (P : Subgroup C) ≤ (T : Subgroup G).subgroupOf C := by
    intro x hx
    exact hcoreT (hP ▸ mem_map_of_mem C.subtype hx)
  have he := P.is_maximal' T.isPGroup'.comap_subtype hPT
  have hm := congrArg (map C.subtype) he
  change ((T : Subgroup G).subgroupOf C).map C.subtype = _ at hm
  rw [subgroupOf_map_subtype,hP] at hm
  rw [←hm]
  ext g
  simp only [mem_twoSectionCentralizer,mem_inf]
  constructor
  · intro hg
    exact ⟨hg.1,hg.2.1,hg.2.1,hg.2.2⟩
  · intro hg
    exact ⟨hg.1,hg.2.2⟩

omit [Finite G] in
/-- Restricting a trivial quotient action retains the original two-core. -/
private theorem sectionCentralizer_le_of_le (T X Y : Subgroup G)
    (hXY : X ≤ Y) (hTX : T ≤ normalizer (X : Set G)) :
    twoSectionCentralizer Y T ≤ twoSectionCentralizer X T := by
  have hcore : X ⊓ Y.pCoreIn 2 ≤ X.pCoreIn 2 :=
    le_pCoreIn_of_normalizes ((isPGroup_pCoreIn 2 Y).to_le inf_le_right) inf_le_left
      ((le_inf X.le_normalizer (hXY.trans (Y.le_normalizer.trans
        (normalizer_le_normalizer_characteristic_image Y (pCore 2 Y))))).trans
          inf_normalizer_le_normalizer_inf)
  intro t ht
  refine ⟨ht.1,hTX ht.1,fun x hx => hcore ⟨?_,ht.2.2 x (hXY hx)⟩⟩
  exact X.mul_mem ((mem_normalizer_iff.mp (hTX ht.1) x).mp hx) (X.inv_mem hx)
end CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.PureFourXi

namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter12.Section01.DoubleNaturalSource ChapterH.NaturalDual.SourceFourActors
open ChapterA.Section04
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- The original O₂(XT) lies in the marked point subgroup T₁. -/
theorem doubleNatural_four_pure_normalizer_core_le_of_many
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (B : DoubledBranch T L V 4) :
    letI := D.doubledOrbit_elementary h
    ∀ S : B.SourceModel, ∀ w : componentOrbit V (T : Subgroup G), w ≠ 1 →
      ∀ hp : (B.coordinates w).toAdd.2 = 0,
      (⟨Additive.ofMul w,(S.natural_marking w).mpr hp⟩ : S.setup.natural) ∈
        S.setup.naturalFixed (S.setup.naturalSylowNormalizer
          ((T.subtype D.sylow_normalizes_component).mapSurjective B.actionProjection_surjective)) →
      ¬ Chapter1.IsSylowIn 2 (B.pointSylow w) (B.pointCentralizer w) →
      (PureFourXi.normalizerJoin T L).pCoreIn 2 ≤ B.pointSylow w := by
  let := D.doubledOrbit_elementary h
  intro S w hw hp hfix hf
  let H := L ⊔ (T : Subgroup G)
  let J := elementaryAbelianMaxJ (T : Subgroup G)
  let N := (normalizer (J : Set G)).subgroupOf H
  let f := B.joinActionProjection D.sylow_normalizes_component
  let P := (T.subtype D.sylow_normalizes_component).mapSurjective B.actionProjection_surjective
  have hJpoint : J ≤ B.pointSylow w :=
    (D.doubleNatural_four_pure_thompson_eq_of_many h hmany B S w hw hp hfix).1
  have hm := (D.doubleNatural_four_pure_thompson_moves_of_many h hmany B S w hw hp hfix hf).2
  have hWT := (D.doubledOrbit_E322 h).le_sylow
  obtain ⟨_,hk,hkT⟩ := S.four_join_action D.sylow_normalizes_component
  have hN : N.map f = normalizer (A0 S.setup P : Set B.ActionQuotient) :=
    S.four_thompson_normalizer_image D.sylow_normalizes_component hWT hm
  have hc : (N.pCoreIn 2).map f = A0 S.setup P := by
    rw [map_pCoreIn_of_ker_isPGroup f hk N,hN,S.setup.four_A0_normalizer_core P]
  have hJH : J ≤ H := (show J ≤ (T : Subgroup G) from sSup_le fun _ hA => hA.1).trans le_sup_right
  have hJi : (J.subgroupOf H).map f = A0 S.setup P := by
    have he : (J.subgroupOf H).map f = (J.subgroupOf (normalizer (L : Set G))).map B.actionProjection := by
      ext a
      constructor <;> rintro ⟨x,hx,rfl⟩
      · exact ⟨⟨x,(sup_le L.le_normalizer D.sylow_normalizes_component) x.property⟩,hx,rfl⟩
      · exact ⟨⟨x,hJH hx⟩,hx,rfl⟩
    rw [he]
    exact S.four_thompson_image D.sylow_normalizes_component hWT hm
  have hkpoint : f.ker ≤ (B.pointSylow w).subgroupOf H := by
    intro x hx
    refine ⟨hkT hx,?_⟩
    let m : normalizer (L : Set G) :=
      ⟨x,(sup_le L.le_normalizer D.sylow_normalizes_component) x.property⟩
    have hqm : B.actionProjection m = 1 := hx
    have hact : m ∈ (normalizerAction T L V B.orbit_eq).ker :=
      (QuotientGroup.eq_one_iff m).mp hqm
    rw [normalizerAction_ker] at hact
    exact centralizer_le (Set.singleton_subset_iff.mpr w.property) hact
  have hbound : N.pCoreIn 2 ≤ (B.pointSylow w).subgroupOf H := by
    have he : (N.pCoreIn 2).map f ≤ (J.subgroupOf H).map f := by rw [hc,hJi]
    have hh := (le_comap_map f (N.pCoreIn 2)).trans (comap_mono he)
    rw [comap_map_eq] at hh
    exact hh.trans (sup_le (comap_mono hJpoint) hkpoint)
  have hmapped := map_mono (f := H.subtype) hbound
  rw [map_pCoreIn_of_injective 2 _ _ H.subtype_injective,
    subgroupOf_map_subtype] at hmapped
  change (PureFourXi.normalizerJoin T L).pCoreIn 2 ≤ _ at hmapped
  rw [subgroupOf_map_subtype] at hmapped
  exact hmapped.trans inf_le_left
end CFSG.Quasithin.Chapter12.Section02.ChosenModule
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter12.Section01.DoubleNaturalSource ChapterA.Section04
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- Trivial action on any containing section has its Sylow kernel inside T₁. -/
theorem doubleNatural_four_pure_sectionCentralizer_le_of_many
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (B : DoubledBranch T L V 4) :
    letI := D.doubledOrbit_elementary h
    ∀ S : B.SourceModel, ∀ w : componentOrbit V (T : Subgroup G), w ≠ 1 →
      ∀ hp : (B.coordinates w).toAdd.2 = 0,
      (⟨Additive.ofMul w,(S.natural_marking w).mpr hp⟩ : S.setup.natural) ∈
        S.setup.naturalFixed (S.setup.naturalSylowNormalizer
          ((T.subtype D.sylow_normalizes_component).mapSurjective B.actionProjection_surjective)) →
      ¬ Chapter1.IsSylowIn 2 (B.pointSylow w) (B.pointCentralizer w) →
      ∀ Y : Subgroup G, PureFourXi.residual T L ≤ Y →
        twoSectionCentralizer Y (T : Subgroup G) ≤ B.pointSylow w := by
  let := D.doubledOrbit_elementary h
  intro S w hw hp hfix hf Y hXY
  have hXi := (D.doubleNatural_four_pure_xi_of_many h hmany B S w hw hp hfix hf).1
  have hc := PureFourXi.sectionCentralizer_le_of_le (T : Subgroup G)
    (PureFourXi.residual T L) Y hXY hXi.invariant
  rw [PureFourXi.sylow_sectionCentralizer_eq_core T _ hXi.perfect hXi.invariant,
    PureFourXi.residual_sup_sylow] at hc
  exact hc.trans (D.doubleNatural_four_pure_normalizer_core_le_of_many h hmany B S w hw hp hfix hf)

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
