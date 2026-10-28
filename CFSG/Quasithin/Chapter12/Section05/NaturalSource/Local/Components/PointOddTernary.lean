module
public import CFSG.Quasithin.Chapter12.Section05.NaturalSource.Local.Components.PointCovers
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.OddThreeExtensionProjectiveModels
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.OddThreeExtensionCovers
public import CFSG.Quasithin.ChapterC.Section05.NormalizerControl.NoncubicSource.EmbeddingSelection.LargerSource.OddThree
public import Theory.GroupTheory.PerfectRankTwoCoreInvolution
public import Theory.SpecificGroups.SL2.LinearThreeSection
public import Theory.SpecificGroups.PSL3.DefiningRank
public import Theory.SpecificGroups.OddThreeSylowOrder

/-!
# The actual residual in an odd ternary point component

Intersect the containing component with the original L₁T and retain its
full relative Sylow subgroup. If the image of L₁ has trivial two-core,
it is the actual SL₃(2). The odd ternary involution-centralizer bound makes
its Sylow centralizer trivial. Normality then kills the intersection's
two-core, so its order divides the original quotient order 168. A full
Sylow has order divisible by sixteen, a contradiction.

The nontrivial core supplies an involution centralized by L₁'s image and
the full Sylow. The genuine cubic central covering of its involution
centralizer embeds that perfect image into prime-field SL₂. Its original
order-168 simple section forces prime seven and projective surjectivity;
perfectness of SL₂ lifts surjectivity, identifying the actual image with
SL₂(7). Both signs and both special/projective models are retained.

PointRemainingRefinement applies this to the full original catalogue.
The last Sylow-action exclusion at seven, the central A₇ row, general
normalizer containments and quasisimple strict enlargement remain with
qt-d-1251-local; qt-d-1251-source owns final exterior assembly.
Source: Aschbacher--Smith 12.5.3, printed pp.817--818, using A.3.21(a), p.55.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter12.Section05.NaturalSource
open Section02 Chapter1.Section02.LocalModels

private theorem odd_ternary_sixteen {Q : Type*} [Group Q] [Finite Q]
    {p : ℕ} (hp : p.Prime) (ho : Odd p) (u : Bool)
    (hm : IsPSLSign Q u 3 p ∨ IsSLSign Q u 3 p) : 16 ∣ Nat.card Q := by
  cases u
  · rcases hm with ⟨F,_,_,hF,⟨e⟩⟩ | ⟨F,_,_,hF,⟨e⟩⟩
    · rw [Nat.card_congr e.toEquiv]
      exact Theory.SpecificGroups.OddThreeSylowOrder.projective_sixteen_dvd_card (hF.symm ▸ ho)
    · rw [Nat.card_congr e.toEquiv]
      exact Theory.SpecificGroups.OddThreeSylowOrder.special_sixteen_dvd_card (hF.symm ▸ ho)
  · rcases hm with ⟨F,_,_,J,hF,hc,⟨e⟩⟩ | ⟨F,_,_,J,hF,hc,⟨e⟩⟩
    · rw [Nat.card_congr e.toEquiv]
      exact Theory.SpecificGroups.OddThreeSylowOrder.unitary_projective_sixteen_dvd_card J hp ho hF hc
    · rw [Nat.card_congr e.toEquiv]
      exact Theory.SpecificGroups.OddThreeSylowOrder.unitary_special_sixteen_dvd_card J hp ho hF hc

private theorem core_eq_bot_of_normal_corefree_faithful {Q : Type*} [Group Q] [Finite Q]
    (S : Sylow 2 Q) (B J : Subgroup Q) (hBJ : B ≤ J)
    (hn : J ≤ normalizer (B : Set Q)) (hSJ : (S : Subgroup Q) ≤ J)
    (hB : pCore 2 B = ⊥) (hf : (S : Subgroup Q) ⊓ centralizer (B : Set Q) = ⊥) :
    pCore 2 J = ⊥ := by
  have hnC : J ≤ normalizer (J.pCoreIn 2 : Set Q) := by
    simpa only [pCoreIn,normalizer_eq_top,←MonoidHom.range_eq_map,range_subtype]
      using (pCore 2 J).le_normalizer_map J.subtype
  have hcomm : ⁅J.pCoreIn 2,B⁆ ≤ B.pCoreIn 2 := by
    apply le_trans _ (inf_pCoreIn_le_of_le 2 hBJ)
    refine le_inf ?_ ?_
    · exact le_normalizer_iff_commutator_le_right.mp ((pCoreIn_le 2 J).trans hn)
    · rw [commutator_comm]
      exact le_normalizer_iff_commutator_le_right.mp (hBJ.trans hnC)
  have hc : J.pCoreIn 2 ≤ centralizer (B : Set Q) := by
    apply commutator_eq_bot_iff_le_centralizer.mp
    apply bot_unique
    simpa only [pCoreIn,hB,Subgroup.map_bot] using hcomm
  have hs : J.pCoreIn 2 ≤ (S : Subgroup Q) := by
    have hh := (pCore_isPGroup (p := 2) (G := J)).le_sylow_of_normal (S.subtype hSJ)
    have hm := map_mono (f := J.subtype) hh
    simpa only [pCoreIn,Sylow.coe_subtype,map_subgroupOf_eq_of_le hSJ] using hm
  exact ((pCore 2 J).map_eq_bot_iff_of_injective J.subtype_injective).mp
    (bot_unique ((le_inf hs hc).trans hf.le))

universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {D : ChosenModule T L V}
namespace SylowExteriorMarking
variable (s : SylowExteriorMarking D)

private theorem odd_point_image_data {K : Subgroup G}
    (hK : K ∈ Chapter1.cComponentsIn (s.marking.Gi 1)) (hLK : s.marking.Li 1 ≤ K) :
    let q := QuotientGroup.mk' (pCore 2 K)
    let B := ((s.marking.Li 1).subgroupOf K).map q
    ∃ S : Sylow 2 (K ⧸ pCore 2 K),
      (S : Subgroup _) ≤ s.pointResidualIntersectionImage K q ∧
      B ≤ s.pointResidualIntersectionImage K q ∧
      s.pointResidualIntersectionImage K q ≤ normalizer (B : Set _) ∧
      Nonempty ((B ⧸ pCore 2 B) ≃* SL(3,ZMod 2)) := by
  dsimp only
  let q := QuotientGroup.mk' (pCore 2 K)
  let B := (s.marking.Li 1).subgroupOf K
  let A := (s.marking.Li 1 ⊔ (T : Subgroup G)) ⊓ K
  obtain ⟨S,hSJ⟩ := s.pointResidualIntersectionImage_sylow hK q (QuotientGroup.mk'_surjective _)
  refine ⟨S,hSJ,?_,?_,?_⟩
  · rintro _ ⟨b,hb,rfl⟩
    exact ⟨⟨b,⟨(show s.marking.Li 1 ≤ s.marking.Li 1 ⊔ (T : Subgroup G) from le_sup_left) hb,b.property⟩⟩,rfl⟩
  · rintro _ ⟨a,rfl⟩
    apply B.le_normalizer_map q
    apply mem_map_of_mem
    intro b
    exact (s.Mi_normalizes_Li 1
      (show (a : G) ∈ s.marking.Mi 1 from
        (sup_le (s.Li_le_Mi 1) (le_inf le_sup_right s.sylow_le_G₁)) a.property.1)) (b : G)
  · let a : B ≃* s.marking.Li 1 := subgroupOfEquivOfLe hLK
    have hk : IsPGroup 2 (q.subgroupMap B).ker := by
      rw [ker_subgroupMap,QuotientGroup.ker_mk']
      exact pCore_isPGroup.comap_subtype
    exact ⟨((q.subgroupMap B).pCoreQuotientEquiv (q.subgroupMap_surjective B) hk).symm.trans
      ((QuotientGroup.congr _ _ a (pCore_map_iso 2 a)).trans (s.marking.LiCoreEquiv 1 (.inl rfl)))⟩

/-- The original point-residual image has nontrivial two-core in every odd ternary row. -/
theorem point_residual_image_twoCore_ne_bot_of_odd_ternary {K : Subgroup G}
    (hK : K ∈ Chapter1.cComponentsIn (s.marking.Gi 1)) (hLK : s.marking.Li 1 ≤ K)
    {p : ℕ} (hp : p.Prime) (ho : Odd p) (unitary : Bool)
    (hm : IsPSLSign (K ⧸ pCore 2 K) unitary 3 p ∨
      IsSLSign (K ⧸ pCore 2 K) unitary 3 p) :
    pCore 2 (((s.marking.Li 1).subgroupOf K).map (QuotientGroup.mk' (pCore 2 K))) ≠ ⊥ := by
  let Q := K ⧸ pCore 2 K
  let q := QuotientGroup.mk' (pCore 2 K)
  let B := ((s.marking.Li 1).subgroupOf K).map q
  let J := s.pointResidualIntersectionImage K q
  obtain ⟨S,hSJ,hBJ,hn,⟨eB⟩⟩ := s.odd_point_image_data hK hLK
  let a := subgroupOfEquivOfLe hLK
  let : Group.IsPerfect (s.marking.Li 1) := s.marking.Li_perfect 1
  let : Group.IsPerfect ((s.marking.Li 1).subgroupOf K) :=
    Group.IsPerfect.ofSurjective (f := a.symm.toMonoidHom) a.symm.surjective
  let : Group.IsPerfect B := Group.IsPerfect.map q
  intro hcore
  let e : B ≃* SL(3,ZMod 2) := ((QuotientGroup.quotientBot.symm).trans
    (QuotientGroup.quotientMulEquivOfEq hcore.symm)).trans eB
  have hz : center B = ⊥ := by
    apply eq_bot_iff.mpr
    intro b hb
    have hh : e b ∈ center SL(3,ZMod 2) := (centerCongr e ⟨b,hb⟩).property
    rw [BinaryLinear.OuterCyclic.binary_center_eq_bot (by decide : 0 < 3),mem_bot] at hh
    exact e.map_eq_one_iff.mp hh
  have hr : 2 ≤ primeRank 2 B := by
    rw [primeRank_congr 2 e]
    rw [primeRank_congr 2 Atlas.Comparisons.Exceptional.sl3TwoEquivPsl3Two]
    exact Matrix.PSL3.DefiningRank.two_mul_fieldExponent_le_primeRank (ZMod 2) (e := 1) (by simp)
  have hf := ChapterC.Section05.NormalizerControl.EmbeddingSelection.odd_three_perfect_sylow_faithful
    S B hz hr hp ho unitary hm
  have hJ := core_eq_bot_of_normal_corefree_faithful S B J hBJ hn hSJ hcore hf
  have hc := s.pointResidualIntersectionImage_corefree_card q hJ
  have h16 : 16 ∣ Nat.card S := S.pow_dvd_card_of_pow_dvd_card (n := 4)
    (odd_ternary_sixteen hp ho unitary hm)
  have hd := (h16.trans (card_dvd_of_le hSJ)).trans hc
  norm_num at hd

/-- The odd ternary point row forces characteristic seven and the actual residual image SL₂(7). -/
theorem point_component_odd_ternary_residual_model {K : Subgroup G}
    (hK : K ∈ Chapter1.cComponentsIn (s.marking.Gi 1)) (hLK : s.marking.Li 1 ≤ K)
    {p : ℕ} (hp : p.Prime) (ho : Odd p) (unitary : Bool)
    (hm : IsPSLSign (K ⧸ pCore 2 K) unitary 3 p ∨
      IsSLSign (K ⧸ pCore 2 K) unitary 3 p) :
    p = 7 ∧ Nonempty ((((s.marking.Li 1).subgroupOf K).map
      (QuotientGroup.mk' (pCore 2 K))) ≃* SL(2,ZMod p)) := by
  let Q := K ⧸ pCore 2 K
  let q := QuotientGroup.mk' (pCore 2 K)
  let B := ((s.marking.Li 1).subgroupOf K).map q
  obtain ⟨S,hSJ,hBJ,hn,⟨eB⟩⟩ := s.odd_point_image_data hK hLK
  let a := subgroupOfEquivOfLe hLK
  let : Group.IsPerfect (s.marking.Li 1) := s.marking.Li_perfect 1
  let : Group.IsPerfect ((s.marking.Li 1).subgroupOf K) :=
    Group.IsPerfect.ofSurjective (f := a.symm.toMonoidHom) a.symm.surjective
  let : Group.IsPerfect B := Group.IsPerfect.map q
  let : Fact p.Prime := ⟨hp⟩
  let : IsSimpleGroup SL(3,ZMod 2) := Atlas.Comparisons.Exceptional.sl3Two_simple
  let : IsSimpleGroup (B ⧸ pCore 2 B) := eB.isSimpleGroup
  let : Nontrivial B := (QuotientGroup.mk'_surjective (pCore 2 B)).nontrivial
  obtain ⟨z,_,hz,hzB⟩ := exists_involution_centralized_by_perfect_sup_sylow S B
    (ChapterA.Section03.SourceEmbeddings.odd_three_two_rank ho unitary hm)
    (hSJ.trans hn) (s.point_residual_image_twoCore_ne_bot_of_odd_ternary hK hLK hp ho unitary hm)
  obtain ⟨r,H,_,_,hH,f,hf,hc,h3⟩ :=
    ChapterA.Section03.SourceEmbeddings.odd_three_cubic_carrier ho unitary hm
  obtain ⟨i,hi⟩ := ChapterA.Section03.SourceEmbeddings.rankThree_cubic_quotient_perfect_embedding
    hH f hf hc h3 z hz B (le_sup_left.trans hzB)
  have hp3 : 3 < p := by
    by_contra hh
    have he : p = 3 := by have := hp.two_le; have := Nat.odd_iff.mp ho; omega
    have hsol : Group.IsSolvable SL(2,ZMod 3) := by
      let : Group.IsSolvable (GL (Fin 2) (ZMod 3)) := Matrix.GeneralLinearGroup.three_isSolvable
      exact Group.isSolvable_of_isSolvable_injective
        (Matrix.SpecialLinearGroup.toGL_injective (n := Fin 2) (R := ZMod 3))
    let : Group.IsSolvable SL(2,ZMod p) := he ▸ hsol
    exact Group.IsPerfect.not_isSolvable B (Group.isSolvable_of_isSolvable_injective hi)
  let : Group.IsSolvable i.ker := by
    rw [(MonoidHom.ker_eq_bot_iff i).mpr hi]
    infer_instance
  obtain ⟨hp7,hproj⟩ := Theory.SL2.prime_seven_and_projective_surjective_of_solvable_kernel
    ((Nat.card_congr eB.toEquiv).trans Atlas.Comparisons.Exceptional.sl3Two_card)
    hp hp3 (Nat.card_zmod p) i
  let : Group.IsPerfect SL(2,ZMod p) :=
    GorensteinWalter.sl2_isPerfect_of_card_gt_three (ZMod p) (by simpa using hp3)
  have hsurj : Function.Surjective i :=
    PerfectCentralCovering.surjective_of_comp_surjective_of_ker_le_center_of_isPerfect
      (QuotientGroup.mk' (center SL(2,ZMod p))) i hproj (by rw [QuotientGroup.ker_mk'])
  exact ⟨hp7,⟨MulEquiv.ofBijective i ⟨hi,hsurj⟩⟩⟩

/-- Both odd ternary signs, special or projective, have the source prime seven. -/
theorem point_component_odd_ternary_prime_eq_seven {K : Subgroup G}
    (hK : K ∈ Chapter1.cComponentsIn (s.marking.Gi 1)) (hLK : s.marking.Li 1 ≤ K)
    {p : ℕ} (hp : p.Prime) (ho : Odd p) (unitary : Bool)
    (hm : IsPSLSign (K ⧸ pCore 2 K) unitary 3 p ∨
      IsSLSign (K ⧸ pCore 2 K) unitary 3 p) : p = 7 :=
  (s.point_component_odd_ternary_residual_model hK hLK hp ho unitary hm).1

end SylowExteriorMarking
end CFSG.Quasithin.Chapter12.Section05.NaturalSource
