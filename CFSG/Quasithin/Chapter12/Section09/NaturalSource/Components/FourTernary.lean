module
public import CFSG.Quasithin.Chapter12.Section09.NaturalSource.Components.FourRankOne
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.OddThreeExtensionProjectiveModels
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.OddThreeExtensionCovers
public import CFSG.Quasithin.ChapterC.Section05.NormalizerControl.NoncubicSource.EmbeddingSelection.LargerSource.OddThree
public import Theory.GroupTheory.PerfectRankTwoCoreInvolution
public import Theory.SpecificGroups.PSL3.DefiningRank
public import Theory.SpecificGroups.OddThreeSylowOrder
public import Theory.SpecificGroups.OddThreeSevenResidual
/-!
# Excluding both odd ternary signs at the original degree-four point

Keep the literal image of L₁ and the full Sylow in the image of
(L₁T) ∩ K₁. If the residual image had trivial two-core, faithful Sylow
action would kill the intersection image's core; its order would divide
168 despite containing a Sylow subgroup of order divisible by sixteen.
Its nontrivial core instead supplies a centralizing involution. The
involution-centralizer covering embeds the perfect residual image into
SL₂(p), forcing p=7 and identifying that actual image with SL₂(7).

The signed ternary-seven normalizer calculation contradicts the order-168
bound for the literal intersection quotient. Thus both special and
projective odd ternary rows are excluded under the original hypotheses,
without an extra diagram-action assumption. FourEven and FourNormal
retain this comparison in the natural-source consumer import path.
Source: Aschbacher--Smith 12.9.3, printed p.858, and A.3.21(a), p.55.
The proof adapts Section05 PointOddTernary and PointTernaryExclusion,
preserving the natural degree-four marking and quotient maps.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter12.Section09.NaturalSource.Components
open Section02 Section08 Section08.InvariantFlag Chapter1.Section02.LocalModels
open Theory.SpecificGroups.OddThreeSevenResidual
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
variable (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 4)
  (earlier : EarlierSetupResults.{u} KnownSimple.IsKnownSimple) (F : InvariantFlag T V 4)
include h earlier
/-- The original point-residual image has nontrivial two-core in every odd ternary row. -/
theorem four_point_residual_image_twoCore_ne_bot_of_odd_ternary {K : Subgroup G}
    (hK : K ∈ Chapter1.cComponentsIn (F.H)) (hLK : F.Li L 1 ≤ K)
    {p : ℕ} (hp : p.Prime) (ho : Odd p) (unitary : Bool)
    (hm : IsPSLSign (K ⧸ pCore 2 K) unitary 3 p ∨
      IsSLSign (K ⧸ pCore 2 K) unitary 3 p) :
    pCore 2 (((F.Li L 1).subgroupOf K).map (QuotientGroup.mk' (pCore 2 K))) ≠ ⊥ := by
  let Q := K ⧸ pCore 2 K
  let q := QuotientGroup.mk' (pCore 2 K)
  let B := ((F.Li L 1).subgroupOf K).map q
  let J := fourPointIntersectionImage F L K q
  obtain ⟨S,hSJ,hBJ,hn,⟨eB⟩⟩ := four_point_image_data h earlier F hK hLK
  let a := subgroupOfEquivOfLe hLK
  let : Group.IsPerfect (F.Li L 1) := four_point_residual_perfect h F
  let : Group.IsPerfect ((F.Li L 1).subgroupOf K) :=
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
  have hc := four_point_intersection_corefree_card h earlier F q hJ
  have h16 : 16 ∣ Nat.card S := S.pow_dvd_card_of_pow_dvd_card (n := 4)
    (odd_ternary_sixteen hp ho unitary hm)
  have hd := (h16.trans (card_dvd_of_le hSJ)).trans hc
  norm_num at hd

/-- The odd ternary point row forces characteristic seven and the actual residual image SL₂(7). -/
theorem four_point_component_odd_ternary_residual_model {K : Subgroup G}
    (hK : K ∈ Chapter1.cComponentsIn (F.H)) (hLK : F.Li L 1 ≤ K)
    {p : ℕ} (hp : p.Prime) (ho : Odd p) (unitary : Bool)
    (hm : IsPSLSign (K ⧸ pCore 2 K) unitary 3 p ∨
      IsSLSign (K ⧸ pCore 2 K) unitary 3 p) :
    p = 7 ∧ Nonempty ((((F.Li L 1).subgroupOf K).map
      (QuotientGroup.mk' (pCore 2 K))) ≃* SL(2,ZMod p)) := by
  let Q := K ⧸ pCore 2 K
  let q := QuotientGroup.mk' (pCore 2 K)
  let B := ((F.Li L 1).subgroupOf K).map q
  obtain ⟨S,hSJ,hBJ,hn,⟨eB⟩⟩ := four_point_image_data h earlier F hK hLK
  let a := subgroupOfEquivOfLe hLK
  let : Group.IsPerfect (F.Li L 1) := four_point_residual_perfect h F
  let : Group.IsPerfect ((F.Li L 1).subgroupOf K) :=
    Group.IsPerfect.ofSurjective (f := a.symm.toMonoidHom) a.symm.surjective
  let : Group.IsPerfect B := Group.IsPerfect.map q
  let : Fact p.Prime := ⟨hp⟩
  let : IsSimpleGroup SL(3,ZMod 2) := Atlas.Comparisons.Exceptional.sl3Two_simple
  let : IsSimpleGroup (B ⧸ pCore 2 B) := eB.isSimpleGroup
  let : Nontrivial B := (QuotientGroup.mk'_surjective (pCore 2 B)).nontrivial
  obtain ⟨z,_,hz,hzB⟩ := exists_involution_centralized_by_perfect_sup_sylow S B
    (ChapterA.Section03.SourceEmbeddings.odd_three_two_rank ho unitary hm)
    (hSJ.trans hn) (four_point_residual_image_twoCore_ne_bot_of_odd_ternary h earlier F hK hLK hp ho unitary hm)
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
theorem four_point_component_odd_ternary_prime_eq_seven {K : Subgroup G}
    (hK : K ∈ Chapter1.cComponentsIn (F.H)) (hLK : F.Li L 1 ≤ K)
    {p : ℕ} (hp : p.Prime) (ho : Odd p) (unitary : Bool)
    (hm : IsPSLSign (K ⧸ pCore 2 K) unitary 3 p ∨
      IsSLSign (K ⧸ pCore 2 K) unitary 3 p) : p = 7 :=
  (four_point_component_odd_ternary_residual_model h earlier F hK hLK hp ho unitary hm).1

omit h earlier in
private theorem signed_ternary_no_small_quotient
    {Q : Type*} [Group Q] [Finite Q] (S : Sylow 2 Q) (B J : Subgroup Q)
    (e : B ≃* SL(2,ZMod 7)) (hBJ : B ≤ J) (hn : J ≤ normalizer (B : Set Q))
    (hSJ : (S : Subgroup Q) ≤ J) (unitary : Bool)
    (hm : IsPSLSign Q unitary 3 7 ∨ IsSLSign Q unitary 3 7) :
    ¬ Nat.card (J ⧸ pCore 2 J) ∣ 168 := by
  have transport {H : Type} [Group H] [Finite H] (a : Q ≃* H)
      (h : ∀ (S : Sylow 2 H) (B J : Subgroup H),
        (B ≃* SL(2,ZMod 7)) → B ≤ J → J ≤ normalizer (B : Set H) →
        (S : Subgroup H) ≤ J → ¬ Nat.card (J ⧸ pCore 2 J) ∣ 168) :
      ¬ Nat.card (J ⧸ pCore 2 J) ∣ 168 := by
    intro hsmall
    let b := B.equivMapOfInjective a.toMonoidHom a.injective
    let j := J.equivMapOfInjective a.toMonoidHom a.injective
    apply h (S.mapSurjective a.surjective) (B.map a.toMonoidHom) (J.map a.toMonoidHom)
      (b.symm.trans e) (map_mono hBJ)
      ((map_mono hn).trans (B.le_normalizer_map a.toMonoidHom)) (map_mono hSJ)
    rwa [←Nat.card_congr (QuotientGroup.congr _ _ j (pCore_map_iso 2 j)).toEquiv]
  cases unitary
  · rcases hm with ⟨F,_,_,hF,⟨a⟩⟩ | ⟨F,_,_,hF,⟨a⟩⟩
    · exact transport a (projective_linear_no_small_quotient hF)
    · exact transport a (special_linear_no_small_quotient hF)
  · rcases hm with ⟨F,_,_,M,hF,hc,⟨a⟩⟩ | ⟨F,_,_,M,hF,hc,⟨a⟩⟩
    · let : Finite (BenderSuzuki.MatrixGroups.ProjectiveSpecialUnitaryMatrixGroup M) :=
        Finite.of_surjective a a.surjective
      exact transport a (projective_unitary_no_small_quotient M hF hc)
    · exact transport a (special_unitary_no_small_quotient M hF hc)

/-- Both signs of the ternary-seven point component are excluded with the
literal residual image and original relative Sylow placement. -/
theorem four_point_component_not_ternary_seven {K : Subgroup G}
    (hK : K ∈ Chapter1.cComponentsIn (F.H)) (hLK : F.Li L 1 ≤ K)
    (unitary : Bool)
    (hm : IsPSLSign (K ⧸ pCore 2 K) unitary 3 7 ∨ IsSLSign (K ⧸ pCore 2 K) unitary 3 7) : False := by
  let q := QuotientGroup.mk' (pCore 2 K)
  let B := ((F.Li L 1).subgroupOf K).map q
  let J := fourPointIntersectionImage F L K q
  obtain ⟨_,⟨e⟩⟩ := four_point_component_odd_ternary_residual_model h earlier F hK hLK (by decide) (by decide) unitary hm
  obtain ⟨S,hSJ⟩ := four_point_intersection_sylow (L := L) F hK q (QuotientGroup.mk'_surjective _)
  have hBJ : B ≤ J := by
    rintro _ ⟨b,hb,rfl⟩
    exact ⟨⟨b,⟨(show F.Li L 1 ≤ F.Li L 1 ⊔ (T : Subgroup G) from le_sup_left) hb,b.property⟩⟩,rfl⟩
  have hn : J ≤ normalizer (B : Set (K ⧸ pCore 2 K)) := by
    rintro _ ⟨a,rfl⟩
    apply ((F.Li L 1).subgroupOf K).le_normalizer_map q
    apply mem_map_of_mem
    intro b
    exact four_point_join_normalizes h earlier F a.property.1 (b : G)
  exact signed_ternary_no_small_quotient S B J e hBJ hn hSJ unitary hm
    (four_point_intersection_core_quotient_card h earlier F q)


/-- The original natural degree-four point component has no odd ternary
quotient, for either sign and either central-cover convention. -/
theorem four_point_component_not_odd_ternary {K : Subgroup G}
    (hK : K ∈ Chapter1.cComponentsIn F.H) (hLK : F.Li L 1 ≤ K)
    {p : ℕ} (hp : p.Prime) (ho : Odd p) (unitary : Bool)
    (hm : IsPSLSign (K ⧸ pCore 2 K) unitary 3 p ∨
      IsSLSign (K ⧸ pCore 2 K) unitary 3 p) : False := by
  have he := four_point_component_odd_ternary_prime_eq_seven h earlier F hK hLK hp ho unitary hm
  subst p
  exact four_point_component_not_ternary_seven h earlier F hK hLK unitary hm

end CFSG.Quasithin.Chapter12.Section09.NaturalSource.Components
