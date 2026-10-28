module
public import CFSG.Quasithin.Chapter12.Section09.NaturalSource.Components.FourCatalogue
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantLarge.OddSylowPairs
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantLarge.A315Source.FiniteSource.ExceptionalOdd.Held
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.OrderBound
public import Theory.SpecificGroups.Rudvalis.Model.Order

/-!
# The complete degree-four three-space component comparison

A nonquasisimple three-space enlargement places its characteristic
seven-radical inside the original normal point component. The detected
ordinary component and the SQTK rank bound make the point quotient
quasisimple of seven-rank at least two. The actual point catalogue excludes
every row except Held by its order. For Held, the radical's odd complement
permutes with a full point-component Sylow; the native odd-Sylow-pair
obstruction excludes that remaining row without a false rank bound.

Thus the three-space quotient is quasisimple. The original full linear
action forces equality with L₃, with normality in its literal flag
normalizer. This completes every clause of 12.9.3 in degree four and,
together with ThreeComplete, constructs ComponentGeometry for both source
degrees. The abelian-span and local-control arguments remain separate.

Source: Aschbacher--Smith 12.9.3, printed p.858. The complement-Sylow
factorization follows the checked Chapter13 OrdinaryPair argument.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups Pointwise
namespace CFSG.Quasithin.Chapter12.Section09.NaturalSource.Components
open Section02 Section08 Section08.InvariantFlag Chapter1.Section02.LocalModels
open Chapter1.XiEmbedding.InvariantLarge BinaryLinear.OuterCyclic
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
variable (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 4)
  (earlier : EarlierSetupResults.{u} KnownSimple.IsKnownSimple) (F : InvariantFlag T V 4)
include h earlier

/-- The detected seven-radical supplies an actual odd complement permuting
with a full Sylow of the original point-component quotient. -/
theorem four_three_radical_point_sylow_pair {K C : Subgroup G}
    (hK : K ∈ Chapter1.cComponentsIn (F.Gi 3))
    (hLK : F.Li L 3 ≤ K) (hN : (K.subgroupOf (F.Gi 3)).Normal)
    (hn : ¬ IsQuasisimple (K ⧸ pCore 2 K))
    (hC : C ∈ Chapter1.cComponentsIn F.H) (hLC : F.Li L 1 ≤ C)
    (hNC : (C.subgroupOf F.H).Normal) : HasOddSylowPair 7 (C ⧸ pCore 2 C) := by
  let : Fact (Nat.Prime 7) := ⟨by decide⟩
  let X := Chapter1.XiP 7 K
  have hXC : X ≤ C := (four_three_radical_point_data h earlier F hK hLK hN hn hC hLC hNC).2
  obtain ⟨hX,hshape⟩ := three_radical_mem_Xi h (Or.inl rfl) F hK hLK hN hn
  let P : Sylow 7 X := default
  let B₀ := (P : Subgroup X).map X.subtype
  have hBX : B₀ ≤ X := map_subtype_le _
  have hB : Chapter1.XiOddQuotient 7 B₀ := hshape.of_mulEquiv
    (hX.ambientSylowQuotientEquiv (by decide) hshape P).symm
  obtain ⟨S₀,hS₀⟩ := (T.subtype (F.invariant 1)).exists_subgroupOf_eq_of_subnormal
    (C.subgroupOf F.H) hC.2.subnormal
  let e := subgroupOfEquivOfLe hC.1
  let S := S₀.mapSurjective (f := e.toMonoidHom) e.surjective
  let U := (S : Subgroup C).map C.subtype
  have hUK : U ≤ C := map_subtype_le _
  have hUT : U ≤ (T : Subgroup G) := by
    rintro _ ⟨c,⟨a,ha,rfl⟩,rfl⟩
    rw [hS₀] at ha
    exact ha
  have hSX : U ≤ normalizer (X : Set G) := hUT.trans hX.invariant
  have hUS : Chapter1.IsSylowIn 2 U C := ⟨S,rfl⟩
  have hUJ : Chapter1.IsSylowIn 2 U (X ⊔ U) := hUS.restrict le_sup_right (sup_le hXC hUK)
  have hQ : X.pCoreIn 2 ≤ U := by
    obtain ⟨R,hR⟩ := hUJ
    exact (pCoreIn_mono_of_normalizes le_sup_left
      (sup_le X.le_normalizer hSX)).trans ((pCoreIn_le_sylow (X ⊔ U) R).trans_eq hR)
  have hNQ : B₀ ≤ normalizer (X.pCoreIn 2 : Set G) :=
    hBX.trans (X.le_normalizer.trans (normalizer_le_normalizer_characteristic_image X (pCore 2 X)))
  have hfactor : (B₀ : Set G) * (X.pCoreIn 2 : Set G) = X := by
    rw [← coe_mul_of_left_le_normalizer_right _ _ hNQ, sup_comm]
    exact congrArg (fun A : Subgroup G => (A : Set G)) (hX.sylow_sup hshape P)
  have hfactor' : (X.pCoreIn 2 : Set G) * (B₀ : Set G) = X := hX.sylow_mul hshape P
  have hQU : (X.pCoreIn 2 : Set G) * (U : Set G) = U := by
    rw [← coe_mul_of_left_le_normalizer_right _ _ (hQ.trans U.le_normalizer),sup_eq_right.mpr hQ]
  have hUQ : (U : Set G) * (X.pCoreIn 2 : Set G) = U := by
    rw [← set_mul_normalizer_comm _ U (hQ.trans U.le_normalizer),hQU]
  have hperm : (B₀ : Set G) * (U : Set G) = (U : Set G) * (B₀ : Set G) := by
    calc
      (B₀ : Set G) * (U : Set G) = (X : Set G) * (U : Set G) := by rw [← hfactor,mul_assoc,hQU]
      _ = (U : Set G) * (X : Set G) := (set_mul_normalizer_comm _ X hSX).symm
      _ = (U : Set G) * (B₀ : Set G) := by rw [← hfactor',← mul_assoc,hUQ]
  have hp : HasOddSylowPair 7 C := by
    refine ⟨S,B₀.subgroupOf C,hB.of_mulEquiv (subgroupOfEquivOfLe (hBX.trans hXC)).symm,?_⟩
    change (B₀.subgroupOf C : Set C) * ((S : Subgroup C) : Set C) =
      ((S : Subgroup C) : Set C) * (B₀.subgroupOf C : Set C)
    apply Set.image_injective.mpr C.subtype_injective
    simpa only [Set.image_mul, ← coe_map, map_subgroupOf_eq_of_le (hBX.trans hXC)] using hperm
  apply hp.map (QuotientGroup.mk' (pCore 2 C)) (QuotientGroup.mk'_surjective _)
  rw [QuotientGroup.ker_mk']
  obtain ⟨m,hm⟩ := (pCore_isPGroup (p := 2) (G := C)).exists_card_eq
  rw [hm]
  exact (by decide : Nat.Coprime 7 2).pow_right m

omit earlier in
private theorem point_component_center_seven_free {C : Subgroup G}
    (hC : C ∈ Chapter1.cComponentsIn F.H) [IsQuasisimple (C ⧸ pCore 2 C)] :
    ¬ 7 ∣ Nat.card (center (C ⧸ pCore 2 C)) := by
  let H : Subgroup G := F.H
  let C₀ := C.subgroupOf H
  let : Group.IsNilpotent (pCore 2 H) := pCore_isNilpotent
  let q := QuotientGroup.mk' (pCore 2 H)
  have hC₀ : C₀.IsCComponent := hC.2
  let a := subgroupOfEquivOfLe hC.1
  let e : (C ⧸ pCore 2 C) ≃* C₀.map q :=
    (QuotientGroup.congr _ _ a (pCore_map_iso 2 a)).symm.trans
      (cComponentTwoCoreQuotientEquiv hC₀)
  let : IsQuasisimple (C₀.map q) := IsQuasisimple.of_mulEquiv e
  have hH : IsSQTK KnownSimple.IsKnownSimple H :=
    h.source.simpleQTKE.twoLocal_sqtk (Gi_twoLocal h F 1 (by decide))
  have hQ := ChapterE.Structure.sqtk_two_quotient hH (pCore 2 H) pCore_isPGroup
  rw [Nat.card_congr (centerCongr e).toEquiv]
  rcases ChapterA.Section03.SourceEmbeddings.quasisimple_containing_component_models_knownSimple
      hQ (pCore_quotient_pCore_eq_bot 2) (hC₀.map_quotient _) with ⟨hs,_⟩ | ⟨⟨z⟩,_⟩
  · let := hs
    have hz : center (C₀.map q) = ⊥ := by
      rcases (inferInstance : (center (C₀.map q)).Normal).eq_bot_or_eq_top with hz | hz
      · exact hz
      · exact ((hC₀.map_quotient _).not_isSolvable
          (Group.isSolvable_of_comm (fun x y =>
            (mem_center_iff.mp (hz ▸ mem_top x) y).symm))).elim
    rw [hz,Subgroup.card_bot]
    decide
  · rw [Nat.card_congr z.toEquiv]
    norm_num

omit earlier in
private theorem point_radical_not_quasisimple {C : Subgroup G}
    (hC : C ∈ Chapter1.cComponentsIn F.H)
    (hm : HasExtension (C ⧸ pCore 2 C) (ElementaryModel 7 2) (fun X _ => IsSL X 2 7)) :
    ¬ IsQuasisimple (C ⧸ pCore 2 C) := by
  intro hq
  let : Fact (Nat.Prime 7) := ⟨by decide⟩
  let := hq
  let A := C ⧸ pCore 2 C
  obtain ⟨N,hN,⟨e⟩,_⟩ := hm
  let := hN
  have hc : Nat.card N = 49 := by rw [Nat.card_congr e.toEquiv]; simp
  let : Group.IsNilpotent N := (IsPGroup.of_card (p := 7) (n := 2) hc).isNilpotent
  have hz : N ≤ center A := by
    rcases IsQuasisimple.normal_le_center_or_eq_top N with hz | ht
    · exact hz
    · let : Group.IsSolvable A := Group.isSolvable_of_surjective
        (f := N.subtype) (by rw [ht]; exact topEquiv.surjective)
      let : IsSimpleGroup (A ⧸ center A) := IsQuasisimple.simple
      let : Nontrivial A := (QuotientGroup.mk'_surjective (center A)).nontrivial
      exact (Group.IsPerfect.not_isSolvable A inferInstance).elim
  exact point_component_center_seven_free h F hC
    ((show 7 ∣ Nat.card N by rw [hc]; decide).trans (card_dvd_of_le hz))
omit h earlier F in
private theorem large_point_seven_rank {A : Type*} [Group A] [Finite A]
    (hm : ClassicalGroup.IsPSL A 5 2 ∨ Nonempty (A ≃* Sporadic.Mathieu.M24) ∨
      Nonempty (A ≃* Janko4.Model)) : primeRank 7 A ≤ 1 := by
  let : Fact (Nat.Prime 7) := ⟨by decide⟩
  apply primeRank_le_of_prime_pow_not_dvd
  rcases hm with hm | hm | hm
  · obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
    let : Fintype F := Fintype.ofFinite F
    have hc : Fintype.card F = Fintype.card (ZMod 2) := by
      simpa only [←Nat.card_eq_fintype_card,Nat.card_zmod] using hF
    let a := (e.trans (Atlas.fieldEquivPSL 5 (FiniteField.ringEquivOfCardEq hc))).trans
      (BinaryLinear.OuterCyclic.projectiveEquivSL (by decide : 0 < 5))
    rw [Nat.card_congr a.toEquiv,Representation.SL5ExteriorSquare.card_specialLinearFive]
    decide
  · rw [Nat.card_congr hm.some.toEquiv,Sporadic.Mathieu.m24_order]
    decide
  · rw [Nat.card_congr hm.some.toEquiv,Janko4.Cardinality.model_card]
    decide

/-- The point catalogue has seven-rank at most one in every quasisimple row
except Held. The radical extension is excluded by the actual center. -/
theorem four_point_seven_rank_or_held {C : Subgroup G}
    (hC : C ∈ Chapter1.cComponentsIn F.H) (hLC : F.Li L 1 ≤ C)
    [IsQuasisimple (C ⧸ pCore 2 C)] :
    primeRank 7 (C ⧸ pCore 2 C) ≤ 1 ∨ Nonempty ((C ⧸ pCore 2 C) ≃* Held.He) := by
  let : Fact (Nat.Prime 7) := ⟨by decide⟩
  rcases four_point_component_models h earlier F hC hLC with he | hm | hm
  · subst C
    left
    apply primeRank_le_of_prime_pow_not_dvd
    rw [Nat.card_congr (Li_three_core_equiv h F 1 (Or.inr ⟨rfl,Or.inl rfl⟩) rfl).some.toEquiv,
      Atlas.Comparisons.Exceptional.sl3Two_card]
    decide
  · exact .inl (large_point_seven_rank hm)
  · rcases hm with hm | hm | hm | hm | hm | hm | hm | hm
    · left
      obtain ⟨k,_,_,hk,⟨e⟩⟩ := hm
      apply primeRank_le_of_prime_pow_not_dvd
      rw [Nat.card_congr e.toEquiv]
      have hc := Atlas.ExceptionalSupport.card_psl_mul (F := k) 4
      rw [hk] at hc
      norm_num [Fin.prod_univ_succ] at hc
      rw [hc]
      decide
    · left
      apply primeRank_le_of_prime_pow_not_dvd
      rw [Nat.card_congr hm.some.toEquiv,nat_card_alternatingGroup, Nat.card_fin]
      decide
    · left
      obtain ⟨_,⟨z⟩,⟨e⟩⟩ := hm
      have hz : Nat.card (center (C ⧸ pCore 2 C)) = 3 := by simpa using Nat.card_congr z.toEquiv
      apply primeRank_le_of_prime_pow_not_dvd
      rw [card_eq_card_quotient_mul_card_subgroup (center (C ⧸ pCore 2 C)),
        Nat.card_congr e.toEquiv,hz,nat_card_alternatingGroup, Nat.card_fin]
      decide
    · left
      apply primeRank_le_of_prime_pow_not_dvd
      rw [Nat.card_congr hm.some.toEquiv,Sporadic.Mathieu.m23_order]
      decide
    · left
      apply primeRank_le_of_prime_pow_not_dvd
      rw [Nat.card_congr hm.some.toEquiv]
      exact fun hd => (by decide : ¬ 7^(1+1) ∣ 2^9*3^2*5^3*7*11)
        (hd.trans Sporadic.LeechRelated.HS.card_carrier_dvd)
    · exact .inr hm
    · left
      apply primeRank_le_of_prime_pow_not_dvd
      rw [Nat.card_congr hm.some.toEquiv,Rudvalis.model_card]
      decide
    · exact (point_radical_not_quasisimple h F hC hm inferInstance).elim

/-- The original degree-four three-space component has quasisimple quotient.
The rank obstruction handles the smaller models; the actual complement-Sylow
pair handles Held without incorrectly bounding its seven-rank. -/
theorem four_three_component_quasisimple {D : Subgroup G}
    (hD : D ∈ Chapter1.cComponentsIn (F.Gi 3)) (hLD : F.Li L 3 ≤ D)
    (hN : (D.subgroupOf (F.Gi 3)).Normal) : IsQuasisimple (D ⧸ pCore 2 D) := by
  by_contra hq
  obtain ⟨C,hC,hLC,hNC,_⟩ := exists_four_point_component h earlier F
  obtain ⟨⟨hqc,hr⟩,_⟩ := four_three_radical_point_data h earlier F hD hLD hN hq hC hLC hNC
  let := hqc
  rcases four_point_seven_rank_or_held h earlier F hC hLC with hb | he
  · omega
  · obtain ⟨e⟩ := he
    let : Fact (Nat.Prime 7) := ⟨by decide⟩
    have hp := (four_three_radical_point_sylow_pair h earlier F hD hLD hN hq hC hLC hNC).of_mulEquiv e
    obtain ⟨S,B,hB,hperm⟩ := hp
    exact Chapter1.XiEmbedding.InvariantLarge.A315Source.ExceptionalOdd.held_no_pair
      (Or.inr rfl) B S hB hperm

/-- The complete original three-space assertion in degree four, preserving
the two-residual and normality inside its literal flag normalizer. -/
theorem four_three_component :
    ((F.Li L 3).subgroupOf (F.Gi 3)).IsCComponent ∧
      ((F.Li L 3).subgroupOf (F.Gi 3)).Normal := by
  obtain ⟨D,hd,_⟩ := exists_unique_normal_local_component h earlier F 3
    (Or.inr ⟨rfl,Or.inr rfl⟩)
  let := h.chosen.elementary
  have he := component_eq_of_quasisimple h earlier F 3 (by decide) (by decide)
    D hd.1 hd.2.1 hd.2.2 (four_three_component_quasisimple h earlier F hd.1 hd.2.1 hd.2.2)
  exact he ▸ ⟨hd.1.2,hd.2.2⟩

/-- All original 12.9.3 component clauses in degree four, with no remaining
model-comparison premise. The nonnormal abelianity argument is still required. -/
theorem four_componentGeometry : Nonempty (ComponentGeometry F L) :=
  four_componentGeometry_of_three_component h earlier F (four_three_component h earlier F)

omit h F in
/-- Complete 12.9.3 at both original degrees. -/
theorem componentGeometry
    {n : ℕ} (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V n)
    (hn : n = 4 ∨ n = 5) (F : InvariantFlag T V n) : Nonempty (ComponentGeometry F L) := by
  rcases hn with rfl | rfl
  · exact four_componentGeometry h earlier F
  · exact five_componentGeometry h earlier F

end CFSG.Quasithin.Chapter12.Section09.NaturalSource.Components
