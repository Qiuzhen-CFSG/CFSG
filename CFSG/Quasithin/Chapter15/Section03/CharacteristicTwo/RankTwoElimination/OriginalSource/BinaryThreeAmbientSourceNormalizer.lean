module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource.BinaryThreeAmbientSourceCubics
public import Theory.GroupTheory.PrimeRankResidualCentralizer
public import Theory.GroupTheory.OddPrimeRankOneSylow
public import Theory.GroupTheory.CyclicSubgroupNormalizer
public import Theory.GroupTheory.SylowNormalRestriction
public import Theory.GroupTheory.SpecificGroups.KleinFourFixedAut
public import Theory.GroupTheory.PResidual.NormalizerImage

/-!
# Proper component containment in the original binary point centralizer

The original intrinsic four F is characteristic in the component L, so its
normalizer is two-local. Rank addition with L/O₂(L)=PSL₃(2) bounds the full
section centralizer A by m₃(A)≤1. An actual cubic of Y_C moves F: fixing F
would also fix the other original plane and put the cubic in O₂(Y).
Cyclicity of the Sylow three-subgroups of A then makes the action kernel
prime to three. At a nonidentity point z of F, its automorphism stabilizer
is a two-group, so the section action bounds m₃(N_G(L)∩C_G(z)) by one.

The original elementary nine at z therefore escapes N_G(L), making L
proper in its normal containing C-component. The two-core of C_G(z) lies
in O₂(LS) and normalizes L. Perfectness lifts the quotient normalizer, so
the same rank bound forces proper component containment in the literal
C_G(z)/O₂(C_G(z)), retaining its full Sylow and original PSL₃(2) marking.

These are necessary original-source constraints, not the large-distance
contradiction. Proper parabolic embeddings are not excluded here. CommonFacts
and the independently produced Earlier premise refer to the same original
MS input throughout; no original-core fixation is assumed.

Source: Aschbacher–Smith 1.2.4 and the setting of 15.3.23, printed
pp.505,1128–1129; the intrinsic-four input comes from MS93 (4.5).
-/

public section
open Subgroup Theory.GroupTheory
open scoped Pointwise MatrixGroups
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource
open LinearThree LinearThree.OriginalSource ChapterC BinaryMS.MS93
universe u
variable {G : Type u} [Group G] [Finite G]

/-- The full section centralizer of the original binary component has
three-rank at most one, using the actual intrinsic four. -/
theorem sectionCentralizer_three_rank_le_one
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (d : LocalData G) {I : Subgroup G} (c : ComponentWitness d I)
    (e : (c.L ⧸ pCore 2 c.L) ≃* PSL(3,ZMod 2))
    (b : BinaryMS.Input KnownSimple.IsKnownSimple
      (c.L.subgroupOf (c.L ⊔ d.S)) (d.S.subgroupOf (c.L ⊔ d.S)))
    (t : InputSetup b)
    (common : CommonFacts t.reduction.radical t.source t.geometry)
    (earlier : DistanceEight.CoreFactors.Earlier t.reduction.radical t.geometry) :
    primeRank 3 (Chapter4.sectionCentralizer c.L) ≤ 1 := by
  obtain ⟨he,hcard,_⟩ := intrinsicFour_properties_of_MS93 d c.L b t common earlier
  let := he
  have hne : intrinsicFour c.L ≠ ⊥ := by
    intro hb
    rw [hb,card_bot] at hcard
    omega
  have hlocal : IsTwoLocal (normalizer (intrinsicFour c.L : Set G)) :=
    ⟨intrinsicFour c.L,hne,IsElementaryAbelian.isPGroup 2 _,rfl⟩
  obtain ⟨hn,hc⟩ := (Chapter4.le_sectionCentralizer_iff
    (Chapter4.sectionCentralizer c.L) c.L).mp le_rfl
  let eSL := e.trans (BinaryLinear.OuterCyclic.projectiveEquivSL (by decide))
  have hz : Nat.Coprime 3 (Nat.card (center (c.L ⧸ pCore 2 c.L))) := by
    rw [Nat.card_congr (centerCongr eSL).toEquiv,Matrix.PSL3Two.center_eq_bot,card_bot]
    decide
  have hr := ResidualCentralizerRank.primeRank_sum_le_of_normalized_factor
    (by decide : Odd 3) (Chapter4.sectionCentralizer c.L) c.L hn
    ((commutator_mono (map_subtype_le _) le_rfl).trans hc) hz
  have hh : Chapter4.sectionCentralizer c.L ⊔ c.L ≤
      normalizer (intrinsicFour c.L : Set G) :=
    (sup_le hn c.L.le_normalizer).trans (intrinsicFour_normalized c.L)
  have hu := (primeRank_mono 3 hh).trans
    ((hG.twoLocal_sqtk hlocal).stronglyQuasithin 3 (by decide) (by decide))
  rw [component_three_rank d c eSL] at hr
  omega

private theorem coprime_kernel_of_cubic_image
    {A B : Type*} [Group A] [Finite A] [Group B] (f : A →* B) (hr : primeRank 3 A ≤ 1)
    (a : A) (ha : orderOf a = 3) (hfa : f a ≠ 1) :
    Nat.Coprime 3 (Nat.card f.ker) := by
  apply Nat.prime_three.coprime_iff_not_dvd.mpr
  intro hd
  let D := zpowers a
  have hD : IsPGroup 3 D := IsPGroup.of_card (by simpa only [D,Nat.card_zpowers,ha] using (by norm_num : 3 = 3 ^ 1))
  obtain ⟨P,hDP⟩ := hD.exists_le_sylow
  let : IsCyclic P := P.isCyclic_of_odd_of_primeRank_le_one (by decide) hr
  obtain ⟨Q,hQ⟩ := P.exists_sylow_map_eq_inf_of_normal f.ker
  obtain ⟨q,hq⟩ := exists_prime_orderOf_dvd_card' (G := Q) 3
    (Q.dvd_card_of_dvd_card hd)
  have hqP : ((q : f.ker) : A) ∈ (P : Subgroup A) := by
    have hm := mem_map_of_mem f.ker.subtype q.property
    rw [hQ] at hm
    exact hm.1
  let k : P := ⟨((q : f.ker) : A),hqP⟩
  let x : P := ⟨a,hDP (mem_zpowers a)⟩
  have hk : orderOf k = 3 := by
    rw [Subgroup.orderOf_mk]
    exact ((Subgroup.orderOf_coe (q : f.ker)).trans
      (Subgroup.orderOf_coe q)).trans hq
  have hx : x ∈ zpowers k := mem_of_pow_card_eq_one_in_cyclic _ (by
    rw [Nat.card_zpowers,hk]
    apply Subtype.ext
    change a ^ 3 = 1
    rw [←ha]
    exact pow_orderOf_eq_one a)
  apply hfa
  have hbound : (zpowers k).map (P : Subgroup A).subtype ≤ f.ker := by
    rw [MonoidHom.map_zpowers]
    exact zpowers_le.mpr (q : f.ker).property
  exact hbound (mem_map_of_mem (P : Subgroup A).subtype hx)

open CFSG.Quasithin.Chapter15.Section03.RankTwo

private theorem cubic_YC_moves_intrinsicFour
    (d : LocalData G) {I : Subgroup G} (c : ComponentWitness d I)
    (e : (c.L ⧸ pCore 2 c.L) ≃* Matrix.PSL3Two.SL)
    (h : ResidualSourceData d c.L e) (hg : ResidualGeometry d c.L)
    (b : BinaryMS.Input KnownSimple.IsKnownSimple
      (c.L.subgroupOf (c.L ⊔ d.S)) (d.S.subgroupOf (c.L ⊔ d.S)))
    (t : InputSetup b)
    (common : CommonFacts t.reduction.radical t.source t.geometry)
    (earlier : DistanceEight.CoreFactors.Earlier t.reduction.radical t.geometry)
    (a : G) (ha : a ∈ YC d c.L) (ha3 : orderOf a = 3) :
    a ∉ centralizer (intrinsicFour c.L : Set G) := by
  intro haf
  obtain ⟨i,j,hij,hm,hf,_,hsup,_⟩ := hg.coordinates
  have hfour : intrinsicFour c.L = d.action.plane i :=
    (intrinsicFour_eq_complementary_plane_of_MS93 d c.L e h hg b t common earlier).trans hf
  have hac : a ∈ centralizer (d.V : Set G) := by
    have hm := (le_centralizer_iff.mp (zpowers_le.mpr (hg.plane_centralized ha)))
    have hf := (le_centralizer_iff.mp (zpowers_le.mpr (hfour ▸ haf)))
    exact (le_centralizer_iff.mp (hsup ▸ sup_le hm hf)) (mem_zpowers a)
  have haY : a ∈ d.Y := hg.first_choice ▸
    ((ComponentIntersection.centralizerResidual_le _ _).trans inf_le_left) ha
  have h9 : Nat.card (d.Y ⧸ pCore 2 d.Y) = 9 := hg.first_choice ▸ h.quotient_card
  have hk := residualY_centralizer_eq_twoCore d.action h.image h9
  have hak : (⟨a,haY⟩ : d.Y) ∈ pCore 2 d.Y := hk ▸ hac
  let x : pCore 2 d.Y := ⟨⟨a,haY⟩,hak⟩
  have hx3 : x ^ 3 = 1 := by
    apply Subtype.ext
    apply Subtype.ext
    change a ^ 3 = 1
    rw [←ha3]
    exact pow_orderOf_eq_one a
  have hx1 : x = 1 := (pCore_isPGroup (p := 2) (G := d.Y)).powEquiv
    (by decide : Nat.Coprime 2 3) |>.injective (by
      simpa only [IsPGroup.powEquiv_apply,one_pow] using hx3)
  have ha1 : a = 1 := congrArg (fun x : pCore 2 d.Y => ((x : d.Y) : G)) hx1
  rw [ha1,orderOf_one] at ha3
  omega

private theorem coprime_section_four_kernel
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (d : LocalData G) {I : Subgroup G} (c : ComponentWitness d I)
    (e : (c.L ⧸ pCore 2 c.L) ≃* PSL(3,ZMod 2))
    (h : ResidualSourceData d c.L
      (e.trans (BinaryLinear.OuterCyclic.projectiveEquivSL (by decide))))
    (hg : ResidualGeometry d c.L)
    (b : BinaryMS.Input KnownSimple.IsKnownSimple
      (c.L.subgroupOf (c.L ⊔ d.S)) (d.S.subgroupOf (c.L ⊔ d.S)))
    (t : InputSetup b)
    (common : CommonFacts t.reduction.radical t.source t.geometry)
    (earlier : DistanceEight.CoreFactors.Earlier t.reduction.radical t.geometry) :
    Nat.Coprime 3 (Nat.card
      ((centralizer (intrinsicFour c.L : Set G)).subgroupOf (Chapter4.sectionCentralizer c.L))) := by
  let A := Chapter4.sectionCentralizer c.L
  let F := intrinsicFour c.L
  have hn : A ≤ normalizer (F : Set G) :=
    ((Chapter4.le_sectionCentralizer_iff A c.L).mp le_rfl).1.trans
      (intrinsicFour_normalized c.L)
  let f : A →* MulAut F := F.normalizerMonoidHom.comp (inclusion hn)
  have hdiv : 3 ∣ Nat.card (YC d c.L) := by
    apply Nat.dvd_of_factorization_pos
    intro hz
    have hc := h.centralizer_three_part
    rw [hz,pow_zero] at hc
    omega
  obtain ⟨a,ha⟩ := exists_prime_orderOf_dvd_card' (G := YC d c.L) 3 hdiv
  have haA : (a : G) ∈ A :=
    ((ComponentIntersection.centralizerResidual_le _ _).trans inf_le_right) a.property
  let aa : A := ⟨a,haA⟩
  have haa : orderOf aa = 3 :=
    (Subgroup.orderOf_coe aa).symm.trans ((Subgroup.orderOf_coe a).trans ha)
  have hf : f aa ≠ 1 := by
    intro he
    have hm : inclusion hn aa ∈ F.normalizerMonoidHom.ker := he
    rw [normalizerMonoidHom_ker] at hm
    exact cubic_YC_moves_intrinsicFour d c _ h hg b t common earlier a a.property
      ((Subgroup.orderOf_coe a).trans ha) hm
  have hh := coprime_kernel_of_cubic_image f
    (sectionCentralizer_three_rank_le_one hG d c e b t common earlier) aa haa hf
  have he : f.ker = (centralizer (F : Set G)).subgroupOf A := by
    rw [←MonoidHom.comap_ker,normalizerMonoidHom_ker]
    rfl
  rwa [he] at hh

private theorem section_point_coprime
    (A F : Subgroup G) [IsKleinFour F]
    (hn : A ≤ normalizer (F : Set G))
    (hk : Nat.Coprime 3 (Nat.card ((centralizer (F : Set G)).subgroupOf A)))
    (z : G) (hz : z ∈ F) (hz1 : z ≠ 1) :
    Nat.Coprime 3 (Nat.card (A ⊓ centralizer ({z} : Set G) : Subgroup G)) := by
  let D := A ⊓ centralizer ({z} : Set G)
  let f : D →* MulAut F := F.normalizerMonoidHom.comp (inclusion (inf_le_left.trans hn))
  have hker : Nat.Coprime 3 (Nat.card f.ker) := by
    let j : f.ker →* (centralizer (F : Set G)).subgroupOf A := {
      toFun x := ⟨⟨((x : D) : G),(x : D).property.1⟩,by
        have hm : inclusion (inf_le_left.trans hn) (x : D) ∈ F.normalizerMonoidHom.ker := x.property
        rw [normalizerMonoidHom_ker] at hm
        exact hm⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
    exact hk.coprime_dvd_right (card_dvd_of_injective j (by
      intro x y hh
      exact Subtype.ext (Subtype.ext (congrArg (fun w : (centralizer (F : Set G)).subgroupOf A => ((w : A) : G)) hh))))
  have hr : IsPGroup 2 f.range :=
    IsKleinFour.isPGroup_aut_subgroup_of_fixed_ne_one f.range
      (v := ⟨z,hz⟩) (fun he => hz1 (congrArg Subtype.val he)) (by
        rintro a ⟨x,rfl⟩
        apply Subtype.ext
        change (x : G) * z * (x : G)⁻¹ = z
        rw [← x.property.2 z (Set.mem_singleton z),mul_inv_cancel_right])
  obtain ⟨n,hn⟩ := hr.exists_card_eq
  have hrc : Nat.Coprime 3 (Nat.card f.range) := by
    rw [hn]
    exact (by decide : Nat.Coprime 3 2).pow_right n
  have hcard := f.ker.card_mul_index
  rw [index_ker] at hcard
  rw [←hcard]
  exact hker.mul_right hrc

private theorem point_normalizer_rank
    (L : Subgroup G) (e : (L ⧸ pCore 2 L) ≃* PSL(3,ZMod 2))
    (z : G)
    (hk : Nat.Coprime 3 (Nat.card
      (Chapter4.sectionCentralizer L ⊓ centralizer ({z} : Set G) : Subgroup G))) :
    primeRank 3 (normalizer (L : Set G) ⊓ centralizer ({z} : Set G) : Subgroup G) ≤ 1 := by
  let N := normalizer (L : Set G) ⊓ centralizer ({z} : Set G)
  let f := (ComponentIntersection.InnerSplitting.sectionAction L).comp
    (inclusion (show N ≤ normalizer (L : Set G) from inf_le_left))
  have hker : Nat.Coprime 3 (Nat.card f.ker) := by
    let j : f.ker →* (Chapter4.sectionCentralizer L ⊓ centralizer ({z} : Set G) : Subgroup G) := {
      toFun x := ⟨((x : N) : G),
        (ComponentIntersection.InnerSplitting.sectionAction_eq_one_iff L _).mp x.property,
        (x : N).property.2⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
    exact hk.coprime_dvd_right (card_dvd_of_injective j (by
      intro x y hh
      exact Subtype.ext (Subtype.ext (congrArg
        (fun w : (Chapter4.sectionCentralizer L ⊓ centralizer ({z} : Set G) : Subgroup G) => (w : G)) hh))))
  apply (primeRank_le_of_coprime_ker 3 f hker).trans
  have hc : Nat.card (MulAut (L ⧸ pCore 2 L)) = 336 := by
    rw [Nat.card_congr (MulAut.congr e).toEquiv]
    exact Matrix.PSL3Two.Automorphisms.card_aut
  apply (primeRank_le_iff_elementary_card_le _).mpr
  intro E hE
  let := hE
  have hd : Nat.card E ∣ 3 * 112 := by
    simpa only [hc] using E.card_subgroup_dvd_card
  obtain ⟨n,hn⟩ := (IsElementaryAbelian.isPGroup 3 E).exists_card_eq
  have hcop : Nat.Coprime (Nat.card E) 112 := by
    rw [hn]
    exact (by decide : Nat.Coprime 3 112).pow_left n
  exact Nat.le_of_dvd (by decide) (hcop.dvd_mul_right.mp hd)


private theorem perfect_twoPerfect {X : Type*} [Group X] [Finite X]
    [Group.IsPerfect X] : IsPPerfect 2 X := by
  intro N hN hp
  let := hN
  have hs : Subsingleton (X ⧸ N) := by
    by_contra! hn
    exact Group.IsPerfect.not_isNilpotent (X ⧸ N) hp.isNilpotent
  apply eq_top_iff.mpr
  intro g _
  exact (QuotientGroup.eq_one_iff g).mp (Subsingleton.elim _ _)


variable (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (d : LocalData G)
    (hempty : MainForward.faithfulLocalComponents d.T = ∅)
    (hM : ChapterA.Section05To06.IsOrderingMaximal d.T d.M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions d.T : Set G)) = {d.Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (d.T : Subgroup G)).ncard)
    {I : Subgroup G} (hI : I ∈ d.Hplus) (htwo : OutsideStructure.RankTwoCase d I)
    (hf : HasCharacteristicTwo I) (c : ComponentWitness d I)
    (e : (c.L ⧸ pCore 2 c.L) ≃* PSL(3,ZMod 2))
    (b : BinaryMS.Input KnownSimple.IsKnownSimple
      (c.L.subgroupOf (c.L ⊔ d.S)) (d.S.subgroupOf (c.L ⊔ d.S)))
    (t : InputSetup b)
    (common : CommonFacts t.reduction.radical t.source t.geometry)
    (earlier : DistanceEight.CoreFactors.Earlier t.reduction.radical t.geometry)

include hG hempty hM hu hmany hI htwo hf e b t common earlier

/-- In the original component normalizer, the stabilizer of a nonidentity
intrinsic-four point has three-rank at most one. Its section-action kernel
has order prime to three. -/
theorem binary_three_source_point_normalizer_rank
    (z : G) (hz : z ∈ intrinsicFour c.L) (hz1 : z ≠ 1) :
    Nat.Coprime 3 (Nat.card (Chapter4.sectionCentralizer c.L ⊓
      centralizer ({z} : Set G) : Subgroup G)) ∧
    primeRank 3 (normalizer (c.L : Set G) ⊓ centralizer ({z} : Set G) : Subgroup G) ≤ 1 := by
  obtain ⟨hW,hJ,hcore,_⟩ := source_lemma_15_3_16_local_geometry
    hG d hempty hM hu hmany hI htwo hf c
  obtain ⟨hne,hBaum,_⟩ := InitialSource.UniformControl.source_controls_of_ordering_maximal
    hG d.T hempty hM hu hmany (d.action.card_centralInvolutions d.T d.sylow_le)
  let eSL := e.trans (BinaryLinear.OuterCyclic.projectiveEquivSL (by decide))
  obtain ⟨_,h,hg⟩ := residual_geometry_of_original hG d hempty hM hu hmany hne hBaum
    hI c (OutsideStructure.rankTwoCase_three_rank hG d hI htwo) eSL hW hJ hcore
  obtain ⟨he,hcard,_⟩ := intrinsicFour_properties_of_MS93 d c.L b t common earlier
  let := he
  let : Nontrivial (intrinsicFour c.L) := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  let : IsKleinFour (intrinsicFour c.L) := ⟨hcard,IsElementaryAbelian.exponent_eq_prime⟩
  have hk := section_point_coprime (Chapter4.sectionCentralizer c.L) (intrinsicFour c.L)
    (((Chapter4.le_sectionCentralizer_iff (Chapter4.sectionCentralizer c.L) c.L).mp le_rfl).1.trans
      (intrinsicFour_normalized c.L))
    (coprime_section_four_kernel hG d c e h hg b t common earlier) z hz hz1
  exact ⟨hk,point_normalizer_rank c.L e z hk⟩

/-- The elementary nine supplied by the opposite component escapes the
full original component normalizer, not only LS. The point is unchanged. -/
theorem binary_three_source_point_nine_escapes_normalizer
    (z : G) (hz : z ∈ intrinsicFour c.L) (hz1 : z ≠ 1)
    (g : G) (hgT : g ∈ (d.T : Subgroup G)) (hgS : g ∉ d.S) :
    ∃ E : Subgroup G, E ≤ centralizer ({z} : Set G) ∧
      IsElementaryAbelian 3 E ∧ Nat.card E = 9 ∧
      ¬ E ≤ normalizer (c.L : Set G) := by
  obtain ⟨a,v,E,_,_,_,_,_,_,_,_,hEC,_,_,hE,hcard⟩ :=
    binary_three_source_intrinsic_point_elementary_nine
      hG d hempty hM hu hmany hI htwo hf c e b t common earlier z hz g hgT hgS
  refine ⟨E,hEC,hE,hcard,?_⟩
  intro hEN
  let N := normalizer (c.L : Set G) ⊓ centralizer ({z} : Set G)
  have hle : E ≤ N := le_inf hEN hEC
  let := hE
  let : IsElementaryAbelian 3 (E.subgroupOf N) := IsElementaryAbelian.subgroupOf hle
  have hlo : 2 ≤ primeRank 3 N := IsElementaryAbelian.primeRank_ge_of_card (E.subgroupOf N)
    ((Nat.card_congr (subgroupOfEquivOfLe hle).toEquiv).trans hcard)
  have hhi := (binary_three_source_point_normalizer_rank
    hG d hempty hM hu hmany hI htwo hf c e b t common earlier z hz hz1).2
  exact (by decide : ¬ (2 ≤ 1)) (hlo.trans hhi)

/-- The normal C-component containing the original L in the chosen point
centralizer is strictly larger. The nonnormalizing nine certifies strictness.
This is a proper component embedding, not yet its exclusion. -/
theorem binary_three_source_point_component_strict
    (g : G) (hgT : g ∈ (d.T : Subgroup G)) (hgS : g ∉ d.S) :
    ∃ z : G, z ∈ intrinsicFour c.L ∧ orderOf z = 2 ∧
      c.L ⊔ d.S ≤ centralizer ({z} : Set G) ∧
      ¬ centralizer ({z} : Set G) ≤ d.M ∧
      IsSQTK KnownSimple.IsKnownSimple (centralizer ({z} : Set G)) ∧
      primeRank 3 (centralizer ({z} : Set G)) ≤ 2 ∧
      let C := centralizer ({z} : Set G)
      ∃ K : Subgroup C, K.IsCComponent ∧ K.Normal ∧ c.L.subgroupOf C < K := by
  obtain ⟨z,hz,hz2,hLS,hout,hsq,hr,K,hK,hKn,hLK,_⟩ :=
    binary_three_source_point_component
      hG d hempty hM hu hmany hI htwo hf c e b t common earlier
  have hz1 : z ≠ 1 := by intro he; rw [he,orderOf_one] at hz2; omega
  obtain ⟨E,hEC,_,_,hEN⟩ := binary_three_source_point_nine_escapes_normalizer
    hG d hempty hM hu hmany hI htwo hf c e b t common earlier z hz hz1 g hgT hgS
  refine ⟨z,hz,hz2,hLS,hout,hsq,hr,K,hK,hKn,lt_of_le_of_ne hLK ?_⟩
  intro he
  have hn : (c.L.subgroupOf (centralizer ({z} : Set G))).Normal := he ▸ hKn
  have hCN : centralizer ({z} : Set G) ≤ normalizer (c.L : Set G) :=
    (normal_subgroupOf_iff_le_normalizer (le_sup_left.trans hLS)).mp hn
  exact hEN (hEC.trans hCN)


/-- The full component normalizer in the literal point quotient still has
three-rank at most one. Normalizers lift because the two-core kernel
normalizes the original perfect component. -/
theorem binary_three_source_point_quotient_normalizer_rank
    (z : G) (hz : z ∈ intrinsicFour c.L) (hz1 : z ≠ 1)
    (hLS : c.L ⊔ d.S ≤ centralizer ({z} : Set G))
    (P : Sylow 2 (centralizer ({z} : Set G)))
    (hP : (P : Subgroup _).map (centralizer ({z} : Set G)).subtype = d.S)
    (g : G) (hgT : g ∈ (d.T : Subgroup G)) (hgS : g ∉ d.S) :
    let C := centralizer ({z} : Set G)
    let q := QuotientGroup.mk' (pCore 2 C)
    let B := (c.L.subgroupOf C).map q
    primeRank 3 (normalizer (B : Set (C ⧸ pCore 2 C))) ≤ 1 := by
  let C := centralizer ({z} : Set G)
  let J := c.L ⊔ d.S
  let q := QuotientGroup.mk' (pCore 2 C)
  let B := c.L.subgroupOf C
  have hLC : c.L ≤ C := le_sup_left.trans hLS
  obtain ⟨hcore,_,_,_⟩ := binary_three_source_point_opposite_core
    hG d hempty hM hu hmany hI htwo hf c e z hLS P hP g hgT hgS
  have hJN : J ≤ normalizer (c.L : Set G) :=
    (normal_subgroupOf_iff_le_normalizer (show c.L ≤ J from le_sup_left)).mp b.component_normal
  have hqn : q.ker ≤ normalizer (B : Set C) := by
    rw [QuotientGroup.ker_mk',←subgroupOf_normalizer_eq hLC]
    intro x hx
    exact hJN ((hcore.trans (J.pCoreIn_le 2)) (mem_map_of_mem C.subtype hx))
  have hq : IsPGroup 2 q.ker := by rw [QuotientGroup.ker_mk']; exact pCore_isPGroup
  let : Group.IsPerfect (c.L.subgroupOf J) := b.component.perfect
  let ec : (c.L.subgroupOf J) ≃* B :=
    (subgroupOfEquivOfLe (show c.L ≤ J from le_sup_left)).trans
      (subgroupOfEquivOfLe hLC).symm
  have hp : IsPPerfect 2 B :=
    (perfect_twoPerfect (X := c.L.subgroupOf J)).of_surjective ec.toMonoidHom ec.surjective
  have he := map_normalizer_of_pPerfect q (QuotientGroup.mk'_surjective _) B hp hq hqn
  change primeRank 3 (normalizer (B.map q : Set (C ⧸ pCore 2 C))) ≤ 1
  rw [←he,ResidualCentralizerRank.primeRank_map_of_twoGroup_kernel (by decide) q hq,
    ←subgroupOf_normalizer_eq hLC]
  let en : ((normalizer (c.L : Set G)).subgroupOf C) ≃*
      (normalizer (c.L : Set G) ⊓ C : Subgroup G) :=
    ((normalizer (c.L : Set G)).subgroupOf C).equivMapOfInjective C.subtype C.subtype_injective |>.trans
      (MulEquiv.subgroupCongr (subgroupOf_map_subtype (normalizer (c.L : Set G)) C))
  rw [primeRank_congr 3 en]
  exact (binary_three_source_point_normalizer_rank
    hG d hempty hM hu hmany hI htwo hf c e b t common earlier z hz hz1).2

/-- The actual point quotient contains a proper smaller local component.
Its full normalizer has three-rank at most one, whereas the point quotient
has rank two; the same full Sylow and intrinsic quotient marking are retained. -/
theorem binary_three_source_point_quotient_strict_component
    (g : G) (hgT : g ∈ (d.T : Subgroup G)) (hgS : g ∉ d.S) :
    ∃ z : G, z ∈ intrinsicFour c.L ∧ orderOf z = 2 ∧
      c.L ⊔ d.S ≤ centralizer ({z} : Set G) ∧
      ¬ centralizer ({z} : Set G) ≤ d.M ∧
      let C := centralizer ({z} : Set G)
      let q := QuotientGroup.mk' (pCore 2 C)
      let B := (c.L.subgroupOf C).map q
      IsSQTK KnownSimple.IsKnownSimple (C ⧸ pCore 2 C) ∧
      pCore 2 (C ⧸ pCore 2 C) = ⊥ ∧
      Nat.card (intrinsicFour B) ≤ 2 ∧
      Nonempty ((B ⧸ pCore 2 B) ≃* PSL(3,ZMod 2)) ∧
      primeRank 3 (C ⧸ pCore 2 C) = 2 ∧
      primeRank 3 (normalizer (B : Set (C ⧸ pCore 2 C))) ≤ 1 ∧
      ∃ P : Sylow 2 C, (P : Subgroup C).map C.subtype = d.S ∧
        B ∈ ChapterA.Section03.localCComponents
          (P.mapSurjective (QuotientGroup.mk'_surjective (pCore 2 C))) ∧
        ∃ K : Subgroup C, K.IsCComponent ∧ K.Normal ∧ c.L.subgroupOf C ≤ K ∧
          (K.map q).IsCComponent ∧ (K.map q).Normal ∧ B < K.map q := by
  obtain ⟨z,hz,hz2,hLS,hout,hsq,hzero,hfour,he,_,_,_,_,_,hr,_,_,
    P,hP,hB,K,hK,hKn,hLK,hKq,hKnq,hBKq⟩ :=
    binary_three_source_point_quotient_with_escaping_nine
      hG d hempty hM hu hmany hI htwo hf c e b t common earlier g hgT hgS
  have hz1 : z ≠ 1 := by intro he; rw [he,orderOf_one] at hz2; omega
  have hn := binary_three_source_point_quotient_normalizer_rank
    hG d hempty hM hu hmany hI htwo hf c e b t common earlier z hz hz1 hLS P hP g hgT hgS
  refine ⟨z,hz,hz2,hLS,hout,hsq,hzero,hfour,he,hr,hn,
    P,hP,hB,K,hK,hKn,hLK,hKq,hKnq,lt_of_le_of_ne hBKq ?_⟩
  intro heq
  have hnorm := heq.symm ▸ hKnq
  have htop := (normalizer_eq_top_iff.mpr hnorm)
  dsimp only at hn
  rw [htop,primeRank_congr 3 topEquiv,hr] at hn
  omega

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource
