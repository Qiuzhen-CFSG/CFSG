module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison.Overcomponent.EmbeddingProof.JankoFourMathieuPoints
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.JankoRank
public import CFSG.Quasithin.MainConverse.SporadicLocal.J4.SylowCenterEven

/-!
# Placing the original J₄ point image in the first involution centralizer

The A₅ seed forces a factor five in the point image's radical quotient,
so its action on every elementary two-group of order at most eight is
trivial. The full source catalogue and faithful Sylow action also force
the point image to have nontrivial two-core. The native J₄ normal-elementary
catalogue, together with the Mathieu-local exclusion, now places the point
image and full Sylow in an involution centralizer. The full Sylow order
excludes the second involution class.

This is the local placement step of the A.3.12 comparison in
Aschbacher–Smith, *The Classification of Quasithin Groups*, 11.4.2,
printed pp. 776–777. It retains both intrinsic two-core quotients and every
previously proved proper pair; identification of the remaining point
quotient with the genuine triple M₂₂ cover is a subsequent step.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups IsMulCommutative Pointwise
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison.Overcomponent.EmbeddingProof
open Chapter1.Section02 ChapterA.Section03 ChapterA.Section03.SourceEmbeddings
open Chapter1.Section02.LocalModels

variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G}
    {L V : Subgroup G} {D : Chapter12.Section02.ChosenModule T L V}

attribute [local irreducible] Janko4.modelGroup Janko4.matrixA Janko4.matrixB
  Janko4.Cardinality.max1Subgroup Janko4.Cardinality.localKernel

private theorem five_dvd_radical_quotient_of_seed
    {A : Type*} [Group A] [Finite A] (U B : Subgroup A) (hUB : U ≤ B)
    [Group.IsPerfect U] (e : (U ⧸ pCore 2 U) ≃* alternatingGroup (Fin 5)) :
    5 ∣ Nat.card (B ⧸ solvableRadical B) := by
  let : IsSimpleGroup (alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup (by simp)
  let : IsSimpleGroup (U ⧸ pCore 2 U) := e.isSimpleGroup
  let q := QuotientGroup.mk' (solvableRadical B)
  let g := q.comp (inclusion hUB)
  let : Group.IsSolvable g.ker := by
    rw [show g = q.comp (inclusion hUB) from rfl,←MonoidHom.comap_ker,QuotientGroup.ker_mk']
    exact Group.isSolvable_of_isSolvable_injective
      (f := (inclusion hUB).subgroupComap (solvableRadical B))
      (fun x y hh => Subtype.ext ((inclusion_injective hUB) (congrArg Subtype.val hh)))
  let : Group.IsSolvable g.rangeRestrict.ker := by
    rw [MonoidHom.ker_rangeRestrict]; infer_instance
  let d := PerfectCoreTwoExtension.solvableKernelQuotientEquiv g.rangeRestrict
    g.rangeRestrict_surjective
  have h60 : Nat.card (g.range ⧸ pCore 2 g.range) = 60 := by
    rw [←Nat.card_congr d.toEquiv,Nat.card_congr e.toEquiv,nat_card_alternatingGroup]
    norm_num [Nat.factorial]
  have hd := (card_quotient_dvd_card (pCore 2 g.range)).trans g.range.card_subgroup_dvd_card
  rw [h60] at hd
  exact (by decide : 5 ∣ 60).trans hd

private theorem radical_card_eq_of_core_equiv {A B : Type*}
    [Group A] [Finite A] [Group B] [Finite B]
    (e : (A ⧸ pCore 2 A) ≃* (B ⧸ pCore 2 B)) :
    Nat.card (A ⧸ solvableRadical A) = Nat.card (B ⧸ solvableRadical B) := by
  let qA := QuotientGroup.mk' (pCore 2 A)
  let qB := QuotientGroup.mk' (pCore 2 B)
  let : Group.IsSolvable qA.ker := by
    rw [QuotientGroup.ker_mk']
    let := pCore_isNilpotent (p := 2) (G := A)
    infer_instance
  let : Group.IsSolvable qB.ker := by
    rw [QuotientGroup.ker_mk']
    let := pCore_isNilpotent (p := 2) (G := B)
    infer_instance
  let a := solvableRadicalQuotientEquiv qA (QuotientGroup.mk'_surjective _)
  let b := solvableRadicalQuotientEquiv qB (QuotientGroup.mk'_surjective _)
  let c := QuotientGroup.congr _ _ e (map_solvableRadical_equiv e)
  exact Nat.card_congr (a.trans (c.trans b.symm)).toEquiv

private theorem small_elementary_action_of_five
    {A : Type*} [Group A] [Finite A] {P C : Subgroup A}
    (hC : C ∈ localCComponents P) (h5 : 5 ∣ Nat.card (C ⧸ solvableRadical C))
    {U : Type*} [Group U] [Finite U] [IsElementaryAbelian 2 U]
    (hU : Nat.card U ≤ 8) (f : C →* MulAut U) : f = 1 := by
  have hnot : ¬5 ∣ Nat.card (MulAut U) := by
    obtain ⟨n,hn⟩ := (IsElementaryAbelian.isPGroup 2 U).exists_card_eq
    have hn3 : n ≤ 3 := (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp (by simpa [hn] using hU)
    rw [SmallNonabelianTwoGroup.card_mulAut_elementary_two_pow U n hn]
    interval_cases n <;> norm_num [Fin.prod_univ_succ]
  by_contra hf
  have ht : (⊤ : Subgroup C).IsCComponent := by
    simpa only [subgroupOf_self] using hC.subgroupOf_of_le le_rfl le_sup_left
  have hk : f.ker ≠ ⊤ := by
    intro he
    apply hf
    ext x : 1
    exact (show x ∈ f.ker from he ▸ mem_top x)
  have hs : Group.IsSolvable f.ker := by
    let d := (topEquiv (G := C)).symm
    have hh : Group.IsSolvable (f.ker.map d.toMonoidHom) := ht.isSolvable_of_subnormal_lt_top
      (show (f.ker.map d.toMonoidHom).IsSubnormal from (Normal.map inferInstance _ d.surjective).isSubnormal)
      (by intro he; apply hk; apply (map_injective (f := d.toMonoidHom) d.injective); simpa using he)
    let : Group.IsSolvable (f.ker.map d.toMonoidHom) := hh
    apply Group.isSolvable_of_isSolvable_injective (f := d.toMonoidHom.subgroupMap f.ker)
    intro x y hh
    exact Subtype.ext (d.injective (congrArg Subtype.val hh))
  let := hs
  have hkr : f.ker ≤ solvableRadical C := le_solvableRadical _ inferInstance hs
  let q := QuotientGroup.map f.ker (solvableRadical C) (MonoidHom.id C) hkr
  have hq : Function.Surjective q := by
    intro y
    obtain ⟨x,rfl⟩ := QuotientGroup.mk'_surjective (solvableRadical C) y
    exact ⟨QuotientGroup.mk' f.ker x,rfl⟩
  have hd := card_dvd_of_surjective q hq
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv] at hd
  exact hnot (h5.trans (hd.trans f.range.card_subgroup_dvd_card))

private theorem ofFlag_point_image_radical_five
    (S : D.NonbinaryNaturalInput)
    {c : LocalGeometry.Coordinates D S.field} (f : LocalGeometry.InvariantFlag c)
    (X : Subgroup G) (z : G) (H : Subgroup G)
    (e : ((ofFlag S f X z H).L₁ ⧸ pCore 2 (ofFlag S f X z H).L₁) ≃*
      Matrix.ProjectiveSpecialLinearGroup (Fin 2) S.field.Carrier)
    (hd : S.field.degree = 2)
    {A : Type*} [Group A] [Finite A]
    (a : ((ofFlag S f X z H).Kz ⧸ pCore 2 (ofFlag S f X z H).Kz) ≃*
      (A ⧸ pCore 2 A)) : 5 ∣ Nat.card (A ⧸ solvableRadical A) := by
  have hm : ClassicalGroup.IsPSL (f.Li 0 ⧸ pCore 2 (f.Li 0)) 2 (2 ^ S.field.degree) :=
    ⟨S.field.Carrier,inferInstance,inferInstance,S.field.card_eq,⟨e⟩⟩
  let : Group.IsPerfect (ofFlag S f X z H).L₁ :=
    Chapter1.mem_L_isPerfect (LocalGeometry.Components.flag_mem_local_of_model D S f 0 hm)
  obtain ⟨b⟩ := Matrix.ProjectiveSpecialLinearGroup.equiv_alternatingGroup_of_card_four
    (show Nat.card S.field.Carrier = 4 by rw [S.field.card_eq,hd]; norm_num)
  rw [←radical_card_eq_of_core_equiv a]
  exact five_dvd_radical_quotient_of_seed (ofFlag S f X z H).L₁
    (ofFlag S f X z H).Kz (le_conjugateSpanBy _ _) (e.trans b)

/-- If the actual J₄ point image has nontrivial two-core, it and its full
Sylow lie in an involution centralizer. The original A₅ seed kills every
small elementary action, and the complete point catalogue excludes max1. -/
theorem ofFlag_jankoFour_point_involution_placement
    (S : D.NonbinaryNaturalInput)
    {c : LocalGeometry.Coordinates D S.field} (f : LocalGeometry.InvariantFlag c)
    (X : Subgroup G) (z : G) (H : Subgroup G)
    (h : EarlierGeometry (ofFlag S f X z H))
    (hne : (ofFlag S f X z H).Kz ≠ (ofFlag S f X z H).K)
    (hlinear : Source.IsSL (L ⧸ pCore 2 L) 3 (2 ^ S.field.degree) →
      V ⊓ centralizer (L : Set G) = ⊥)
    (h1132 : ∀ A, Hypothesis1131At D S (c.binarySubspace (f.space 0)) A →
      Proposition1132At D S (c.binarySubspace (f.space 0)) A)
    (e : ((ofFlag S f X z H).L₁ ⧸ pCore 2 (ofFlag S f X z H).L₁) ≃*
      Matrix.ProjectiveSpecialLinearGroup (Fin 2) S.field.Carrier)
    {J : Subgroup G} (hJ : J ∈ Chapter1.L G (T : Subgroup G))
    (hlt : (ofFlag S f X z H).Kz < J)
    (b : (J ⧸ pCore 2 J) ≃* Janko4.Model)
    (P : Sylow 2 Janko4.Model) (B : Subgroup Janko4.Model)
    (hB : B ∈ localCComponents P)
    (hn : (P : Subgroup Janko4.Model) ≤ normalizer (B : Set _))
    (a : ((ofFlag S f X z H).Kz ⧸ pCore 2 (ofFlag S f X z H).Kz) ≃*
      (B ⧸ pCore 2 B)) (hc : pCore 2 B ≠ ⊥) :
    ∃ t : Janko4.Model, orderOf t = 2 ∧
      B ⊔ (P : Subgroup Janko4.Model) ≤ centralizer ({t} : Set Janko4.Model) := by
  open Janko4 Janko4.Cardinality Janko4.OuterReduction.OddIndex in
  let P₀ : Sylow 2 Model := twoSubgroup_isPGroup.toSylow (by
    rw [twoSubgroup,index_map_subtype,localTwoSubgroup_index]
    exact Nat.Prime.not_dvd_mul Nat.prime_two (by decide)
      Janko4.OuterReduction.max1_odd_index_unconditional)
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq Model P P₀
  let v := MulAut.conj g
  let C := B.map v.toMonoidHom
  have hP : (P : Subgroup Model).map v.toMonoidHom = twoSubgroup :=
    congrArg Sylow.toSubgroup hg
  let : Group.IsSolvable v.toMonoidHom.ker := by
    rw [v.toMonoidHom.ker_eq_bot v.injective]; infer_instance
  have hC : C ∈ localCComponents P₀ := by
    have hh := localCComponents_map_of_solvable_ker hB v.toMonoidHom
    rwa [hP] at hh
  have hnC : twoSubgroup ≤ normalizer (C : Set Model) := by
    rw [←hP]
    exact (map_mono hn).trans (B.le_normalizer_map v.toMonoidHom)
  let d := v.subgroupMap B
  let aq := a.trans (QuotientGroup.congr _ _ d (pCore_map_iso 2 d))
  have hcC : pCore 2 C ≠ ⊥ := by
    intro hz
    apply hc
    apply (map_eq_bot_iff_of_injective (f := d.toMonoidHom) _ d.injective).mp
    rw [pCore_map_iso 2 d]
    exact hz
  have hd := (ofFlag_proper_overcomponent_fieldFour S f X z H h hne hlinear h1132 e hJ hlt).1
  have h5 := ofFlag_point_image_radical_five S f X z H e hd aq
  obtain ⟨N,hN,hCN,hPN⟩ := FiveLocalFF.SolvableQuotients.exists_maximal_two_local P₀ C hnC hcC
  obtain ⟨R,hR,_,heR,hNR⟩ := exists_normal_elementary_normalizer_of_sylow_le P₀ hN hPN
  let E := R.map (P₀ : Subgroup Model).subtype
  have he : IsElementaryAbelian 2 E := by let := heR; exact IsElementaryAbelian.map _
  have hEn : E ≠ ⊥ := fun hz => hR ((map_eq_bot_iff_of_injective _ Subtype.val_injective).mp hz)
  have h2 : 2 ∣ Nat.card (centralizer (C : Set Model)) := by
    rcases FiveLocalFF.JankoFour.fixed_pair_minimal_alternative (C ⊔ twoSubgroup) E
        (map_subtype_le R) hEn he le_sup_right
        (sup_le (hNR ▸ hCN) (hNR ▸ hPN)) with hmax | ⟨U,hU,_,heU,hcard,hCU⟩
    · exact (ofFlag_jankoFour_point_avoids_mathieuLocal S f X z H h hne hlinear h1132 e
        hJ hlt b P B hB hn a g ⟨le_sup_left.trans hmax,by rw [hP]; exact le_sup_right.trans hmax⟩).elim
    · let := heU
      have hnU := le_sup_left.trans hCU
      let α := U.normalizerMonoidHom.comp (inclusion hnU)
      have hα := small_elementary_action_of_five hC h5 hcard α
      have hcent : C ≤ centralizer (U : Set Model) := by
        intro x hx
        have hk : inclusion hnU ⟨x,hx⟩ ∈ U.normalizerMonoidHom.ker := by
          change α ⟨x,hx⟩ = 1
          rw [hα]; rfl
        rwa [normalizerMonoidHom_ker] at hk
      have htwo : 2 ∣ Nat.card U := (IsElementaryAbelian.isPGroup 2 U).card_eq_or_dvd.resolve_left
        (fun heq => hU (U.eq_bot_of_card_eq heq))
      exact htwo.trans (card_dvd_of_le (le_centralizer_iff.mp hcent))
  obtain ⟨t,ht,hpair⟩ := exists_involution_centralizing_normalizing_two_group C twoSubgroup
    P₀.isPGroup' hnC h2
  refine ⟨v.symm t,by rw [MulEquiv.orderOf_eq]; exact ht,?_⟩
  have hh := map_mono (f := v.symm.toMonoidHom) hpair
  rw [Subgroup.map_sup,←hP,map_map,map_map] at hh
  have hid : v.symm.toMonoidHom.comp v.toMonoidHom = MonoidHom.id Model := by ext x; simp
  rw [hid,map_id,map_id,map_centralizer_equiv,Set.image_singleton] at hh
  exact hh


private theorem fieldFour_lie_seven_of_janko_order {A : Type*} [Group A] [Finite A]
    (hm : LocalGeometry.Components.LieOvergroup A 2)
    (hd : Nat.card A ∣ 86775571046077562880) : 7 ∣ Nat.card A := by
  cases hm with
  | sl3 hm =>
    obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
    have h7 : 7 ∣ Nat.card PSL(3,F) := by
      rw [Matrix.PSL3.LinearThree.card_projective,hF]; norm_num
    rw [Nat.card_congr e.toEquiv]
    exact h7.trans (card_quotient_dvd_card _)
  | psl3 hm =>
    obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
    rw [Nat.card_congr e.toEquiv,Matrix.PSL3.LinearThree.card_projective,hF]
    norm_num
  | sp4 hm =>
    obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
    rw [Nat.card_congr e.toEquiv,Theory.SpecificGroups.SymplecticFour.card_sp F,hF] at hd
    norm_num at hd
  | g2 hm =>
    obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
    rw [Nat.card_congr e.toEquiv,Atlas.G2.card_Model,hF]
    norm_num
  | ree m hm he _ => omega
  | triality hm =>
    obtain ⟨e⟩ := (Triality.Standard.isTrialityGroupAt_binary_iff A 2 (by decide)).mp hm
    rw [Nat.card_congr e.toEquiv] at hd
    have hu := (Triality.Standard.Parabolics.unipotent (Triality.Standard.binaryParameters 2 (by decide))).card_subgroup_dvd_card
    rw [Triality.Standard.ConcreteBruhat.FixedCellCount.card_unipotent,
      Triality.Standard.binaryParameters_q] at hu
    exact (by norm_num : ¬ (2^2)^12 ∣ 86775571046077562880) (hu.trans hd) |>.elim
  | trialityCube m hm he _ => omega

private theorem fieldFour_seven_or_eleven_of_janko_order
    {A : Type*} [Group A] [Finite A] [IsQuasisimple A]
    (hc : pCore 2 A = ⊥) (hm : LocalGeometry.Components.FieldFourOvergroup A)
    (hd : Nat.card A ∣ 86775571046077562880) :
    7 ∣ Nat.card A ∨ ClassicalGroup.IsPSL A 2 11 := by
  cases hm with
  | alternating hm =>
    left
    rw [Nat.card_congr hm.some.toEquiv,nat_card_alternatingGroup]
    norm_num [Nat.factorial]
  | alternatingCover hm =>
    have h7 : 7 ∣ Nat.card (A ⧸ center A) := by
      rw [Nat.card_congr hm.2.2.some.toEquiv,nat_card_alternatingGroup]
      norm_num [Nat.factorial]
    exact .inl (h7.trans (card_quotient_dvd_card _))
  | primeLinear p hp hm =>
    have hpd : p ∣ Nat.card A := by
      obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
      have ho : Odd p := hp.1.odd_of_ne_two (by have := hp.2.1; omega)
      rw [Nat.card_congr e.toEquiv,GorensteinWalter.psl2_card_formula F
        ⟨p,1,hp.1,ho,by decide,by simpa using hF⟩,hF]
      have he : 2 ∣ p^2-1 := by
        obtain ⟨a,ha⟩ := ho
        refine ⟨2*a*(a+1),?_⟩
        nlinarith [Nat.sub_add_cancel (show 1 ≤ p^2 by have := hp.1.two_le; nlinarith)]
      apply (Nat.dvd_div_iff_mul_dvd (dvd_mul_of_dvd_right he p)).mpr
      simpa only [Nat.mul_comm] using Nat.mul_dvd_mul (dvd_refl p) he
    have hpN := hpd.trans hd
    rw [show 86775571046077562880 = 2^21*3^3*5*7*11^3*23*29*31*37*43 by decide] at hpN
    simp only [hp.1.dvd_mul,or_assoc] at hpN
    have he : p = 11 ∨ p = 29 := by
      rcases hpN with h | h | h | h | h | h | h | h | h | h
      · have he := Nat.prime_eq_prime_of_dvd_pow hp.1 Nat.prime_two h
        have hx := hp.2; rw [he] at hx; norm_num at hx
      · have he := Nat.prime_eq_prime_of_dvd_pow hp.1 Nat.prime_three h
        have hx := hp.2; rw [he] at hx; norm_num at hx
      · have he := (Nat.prime_dvd_prime_iff_eq hp.1 Nat.prime_five).mp h
        have hx := hp.2; rw [he] at hx; norm_num at hx
      · have he := (Nat.prime_dvd_prime_iff_eq hp.1 (by decide : Nat.Prime 7)).mp h
        have hx := hp.2; rw [he] at hx; norm_num at hx
      · exact .inl (Nat.prime_eq_prime_of_dvd_pow hp.1 (by decide : Nat.Prime 11) h)
      · have he := (Nat.prime_dvd_prime_iff_eq hp.1 (by decide : Nat.Prime 23)).mp h
        have hx := hp.2; rw [he] at hx; norm_num at hx
      · exact .inr ((Nat.prime_dvd_prime_iff_eq hp.1 (by decide : Nat.Prime 29)).mp h)
      · have he := (Nat.prime_dvd_prime_iff_eq hp.1 (by decide : Nat.Prime 31)).mp h
        have hx := hp.2; rw [he] at hx; norm_num at hx
      · have he := (Nat.prime_dvd_prime_iff_eq hp.1 (by decide : Nat.Prime 37)).mp h
        have hx := hp.2; rw [he] at hx; norm_num at hx
      · have he := (Nat.prime_dvd_prime_iff_eq hp.1 (by decide : Nat.Prime 43)).mp h
        have hx := hp.2; rw [he] at hx; norm_num at hx
    rcases he with rfl | rfl
    · exact .inr hm
    · left
      obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
      rw [Nat.card_congr e.toEquiv,GorensteinWalter.psl2_card_formula F
        ⟨29,1,by decide,by decide,by decide,by simpa using hF⟩,hF]
      norm_num
  | linearTwentyFive hm =>
    obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
    rw [Nat.card_congr e.toEquiv,GorensteinWalter.psl2_card_formula F
      ⟨5,2,by decide,by decide,by decide,by simpa using hF⟩,hF] at hd
    norm_num at hd
  | three u hm =>
    obtain ⟨hdiv,hl,_⟩ := odd_ternary_five_card_bounds u hm
    rcases hdiv with hdiv | hdiv
    all_goals
      have hh := Nat.dvd_gcd hd hdiv
      norm_num at hh
      have := Nat.le_of_dvd (by decide) hh
      omega
  | m22 hm =>
    left
    rw [Nat.card_congr hm.some.toEquiv,Sporadic.Mathieu.m22_order]; norm_num
  | m22Cover hm =>
    have h7 : 7 ∣ Nat.card (A ⧸ center A) := by
      rw [Nat.card_congr hm.2.2.some.toEquiv,Sporadic.Mathieu.m22_order]; norm_num
    exact .inl (h7.trans (card_quotient_dvd_card _))
  | m23 hm =>
    left
    rw [Nat.card_congr hm.some.toEquiv,Sporadic.Mathieu.m23_order]; norm_num
  | j1 hm =>
    left
    rw [Nat.card_congr hm.some.toEquiv,Janko1.card_model]; norm_num
  | j2 hm =>
    left
    rw [Nat.card_congr hm.some.toEquiv,Sporadic.LeechRelated.J2.ExceptionalParabolics.FirstParabolic.card_carrier]; norm_num
  | j4 hm =>
    left
    rw [Nat.card_congr hm.some.toEquiv,Janko4.Cardinality.model_card]; norm_num
  | hs hm =>
    left
    rw [Nat.card_congr hm.some.toEquiv,Sporadic.LeechRelated.HS.NormalizerIndex.card_carrier]; norm_num
  | ru hm =>
    left
    rw [Nat.card_congr hm.some.toEquiv,Rudvalis.model_card]; norm_num
  | nilpotentExtension hm =>
    exact (Quasisimple.Classification.not_odd_sl2_extension hc _ (by decide : Odd 5) hm).elim
  | elementaryExtension p hp hm =>
    exact (Quasisimple.Classification.not_odd_sl2_extension hc _
      (hp.1.odd_of_ne_two (by have := hp.2.1; omega)) hm).elim

private theorem jankoFour_core_ne_bot_of_seven_or_eleven
    (hsq : IsSQTK KnownSimple.IsKnownSimple Janko4.Model)
    (P : Sylow 2 Janko4.Model) (B : Subgroup Janko4.Model)
    (hB : B ∈ localCComponents P) (hproper : B ≠ ⊤)
    (hn : (P : Subgroup Janko4.Model) ≤ normalizer (B : Set Janko4.Model))
    [IsQuasisimple (B ⧸ pCore 2 B)]
    (hm : 7 ∣ Nat.card (B ⧸ pCore 2 B) ∨ ClassicalGroup.IsPSL (B ⧸ pCore 2 B) 2 11) :
    pCore 2 B ≠ ⊥ := by
  intro hc
  let v : B ≃* (B ⧸ pCore 2 B) := QuotientGroup.quotientBot.symm.trans
    (QuotientGroup.quotientMulEquivOfEq hc).symm
  let : IsQuasisimple B := IsQuasisimple.of_mulEquiv v.symm
  have hf := sylow_centralizer_eq_bot_of_evenCharacteristic P
    (MainConverse.SporadicLocal.J4SylowCenterEven.evenCharacteristic P) hB hn
  rcases hm with h7 | hm
  · exact hproper (JankoRank.eq_top_of_quasisimple_faithful_sylow (MulEquiv.refl _) P B
      (hsq.subgroup B) hc (by rwa [Nat.card_congr v.toEquiv]) hn hf)
  · obtain ⟨F,_,_,hF,⟨b⟩⟩ := hm
    let : Fact (Nat.Prime 11) := ⟨by decide⟩
    let : Fintype F := Fintype.ofFinite F
    let r : F ≃+* ZMod 11 := FiniteField.ringEquivOfCardEq (by
      simpa only [←Nat.card_eq_fintype_card,Nat.card_zmod] using hF)
    let e := v.trans (b.trans (Atlas.fieldEquivPSL 2 r))
    let a := B.normalizerMonoidHom.comp (inclusion hn)
    have hi : Function.Injective a := by
      apply (MonoidHom.ker_eq_bot_iff _).mp
      apply bot_unique
      intro x hx
      apply Subtype.ext
      apply mem_bot.mp
      rw [←hf]
      refine ⟨x.property,?_⟩
      change inclusion hn x ∈ B.normalizerMonoidHom.ker at hx
      rwa [normalizerMonoidHom_ker] at hx
    have hh := Theory.GroupTheory.primeRank_le_of_injective 2 a hi
    rw [primeRank_equiv 2 (MulAut.congr e),←P.primeRank_eq] at hh
    have := Janko4.eleven_le_twoRank
    have := Theory.PSL2.primeField_automorphism_two_rank (p := 11) (by decide)
    omega

/-- The actual proper point image in J₄ has nontrivial two-core. The full
source catalogue supplies either a factor seven or PSL₂(11), and the full
Sylow action excludes both core-free alternatives. -/
theorem ofFlag_jankoFour_point_core_ne_bot
    (S : D.NonbinaryNaturalInput)
    {c : LocalGeometry.Coordinates D S.field} (f : LocalGeometry.InvariantFlag c)
    (X : Subgroup G) (z : G) (H : Subgroup G)
    (h : EarlierGeometry (ofFlag S f X z H))
    (hne : (ofFlag S f X z H).Kz ≠ (ofFlag S f X z H).K)
    (hlinear : Source.IsSL (L ⧸ pCore 2 L) 3 (2 ^ S.field.degree) →
      V ⊓ centralizer (L : Set G) = ⊥)
    (h1132 : ∀ A, Hypothesis1131At D S (c.binarySubspace (f.space 0)) A →
      Proposition1132At D S (c.binarySubspace (f.space 0)) A)
    (e : ((ofFlag S f X z H).L₁ ⧸ pCore 2 (ofFlag S f X z H).L₁) ≃*
      Matrix.ProjectiveSpecialLinearGroup (Fin 2) S.field.Carrier)
    {J : Subgroup G} (hJ : J ∈ Chapter1.L G (T : Subgroup G))
    (hlt : (ofFlag S f X z H).Kz < J)
    (b : (J ⧸ pCore 2 J) ≃* Janko4.Model)
    (P : Sylow 2 Janko4.Model) (B : Subgroup Janko4.Model)
    (hB : B ∈ localCComponents P) (hproper : B ≠ ⊤)
    (hn : (P : Subgroup Janko4.Model) ≤ normalizer (B : Set _))
    (a : ((ofFlag S f X z H).Kz ⧸ pCore 2 (ofFlag S f X z H).Kz) ≃*
      (B ⧸ pCore 2 B)) : pCore 2 B ≠ ⊥ := by
  let := point_quasisimple_in_jankoFour h hJ hlt b
  let := IsQuasisimple.of_mulEquiv a
  have hdegree := (ofFlag_proper_overcomponent_fieldFour S f X z H h hne hlinear h1132 e hJ hlt).1
  have hl := (Chapter1.Section02.Adequate.mem_L_iff_mainForward T J).mp hJ
  obtain ⟨_,_,_,_,hsq⟩ := MainForward.localComponents_local_setup S.source.simpleQTKE T hl
  have hs : IsSQTK KnownSimple.IsKnownSimple J :=
    (IsSQTK.equiv (subgroupOfEquivOfLe (show J ≤ J ⊔ (T : Subgroup G) from le_sup_left))).mp
      (hsq.subgroup (J.subgroupOf (J ⊔ (T : Subgroup G))))
  have hq := (ChapterE.Structure.sqtk_two_quotient hs (pCore 2 J) pCore_isPGroup).knownSimple_of_equiv b
  have hd : Nat.card ((ofFlag S f X z H).Kz ⧸ pCore 2 (ofFlag S f X z H).Kz) ∣ 86775571046077562880 := by
    rw [Nat.card_congr a.toEquiv,←Janko4.Cardinality.model_card]
    exact (card_quotient_dvd_card _).trans B.card_subgroup_dvd_card
  apply jankoFour_core_ne_bot_of_seven_or_eleven hq P B hB hproper hn
  have hm : 7 ∣ Nat.card ((ofFlag S f X z H).Kz ⧸ pCore 2 (ofFlag S f X z H).Kz) ∨
      ClassicalGroup.IsPSL ((ofFlag S f X z H).Kz ⧸ pCore 2 (ofFlag S f X z H).Kz) 2 11 := by
    cases ofFlag_overcomponent_alternative S f X z H e h.point_mem_local_family le_rfl with
    | equal he =>
      exact ((h.strict_comparison (fixed_and_transitive D S _ hlinear h1132).1 hne).2.1.ne he).elim
    | lie hm =>
      rw [hdegree] at hm
      exact .inl (fieldFour_lie_seven_of_janko_order hm hd)
    | four _ hm => exact fieldFour_seven_or_eleven_of_janko_order (pCore_quotient_pCore_eq_bot 2) hm hd
  exact hm.imp (by intro hh; rwa [←Nat.card_congr a.toEquiv]) (fun hh => hh.of_mulEquiv a.symm)

private theorem jankoFour_full_sylow_centralizer_marking
    (P : Sylow 2 Janko4.Model) (t : Janko4.Model) (ht : orderOf t = 2)
    (hP : (P : Subgroup Janko4.Model) ≤ centralizer ({t} : Set Janko4.Model)) :
    Nonempty ((centralizer ({t} : Set Janko4.Model)) ≃*
      Janko4.InvolutionCentralizers.First.centralizer) := by
  rcases Janko4.InvolutionCentralizers.centralizer_equiv_first_or_second t ht with h | h
  · exact h
  · have hpow : 2^21 ∣ Nat.card P := P.pow_dvd_card_of_pow_dvd_card (by
      rw [Janko4.Cardinality.model_card]; norm_num)
    have hd := hpow.trans (card_dvd_of_le hP)
    rw [Nat.card_congr h.some.toEquiv,Janko4.InvolutionCentralizers.Second.ambient_card] at hd
    norm_num at hd

/-- The actual residual J₄ comparison: both intrinsic core quotients,
full Sylow normalization and properness are retained. All conjugates of
the native Mathieu local are excluded. The point-image two-core is proved
nontrivial, placing the pair in the genuine first involution centralizer. This is an
output of the original source hypotheses, not a replacement hypothesis. -/
@[expose] def JankoFourPointPlacement (E : Closure.Geometry D) (J : Subgroup G) : Prop :=
  Nonempty ((J ⧸ pCore 2 J) ≃* Janko4.Model) ∧
    ∃ (P : Sylow 2 Janko4.Model) (B : Subgroup Janko4.Model),
      B ∈ localCComponents P ∧ B ≠ ⊤ ∧
      (P : Subgroup Janko4.Model) ≤ normalizer (B : Set Janko4.Model) ∧
      Nonempty ((E.Kz ⧸ pCore 2 E.Kz) ≃* (B ⧸ pCore 2 B)) ∧
      (∀ g : Janko4.Model, ¬
        (B.map (MulAut.conj g).toMonoidHom ≤
            Janko4.Cardinality.max1Subgroup Janko4.matrixA_mul_self Janko4.matrixB_pow_four ∧
          (P : Subgroup Janko4.Model).map (MulAut.conj g).toMonoidHom ≤
            Janko4.Cardinality.max1Subgroup Janko4.matrixA_mul_self Janko4.matrixB_pow_four)) ∧
      (pCore 2 B ≠ ⊥ ∧ ∃ t : Janko4.Model, orderOf t = 2 ∧
        B ⊔ (P : Subgroup Janko4.Model) ≤ centralizer ({t} : Set Janko4.Model) ∧
        Nonempty ((centralizer ({t} : Set Janko4.Model)) ≃*
          Janko4.InvolutionCentralizers.First.centralizer))

/-- The complete catalogue gives a proved proper pair or the literal
J₄ point-placement result. The nonquasisimple quintic and every proved
Mathieu proper pair remain present. -/
theorem ofFlag_proper_embedding_or_jankoFour_placement
    (S : D.NonbinaryNaturalInput)
    {c : LocalGeometry.Coordinates D S.field} (f : LocalGeometry.InvariantFlag c)
    (X : Subgroup G) (z : G) (H : Subgroup G)
    (h : EarlierGeometry (ofFlag S f X z H))
    (hne : (ofFlag S f X z H).Kz ≠ (ofFlag S f X z H).K)
    (hlinear : Source.IsSL (L ⧸ pCore 2 L) 3 (2 ^ S.field.degree) →
      V ⊓ centralizer (L : Set G) = ⊥)
    (h1132 : ∀ A, Hypothesis1131At D S (c.binarySubspace (f.space 0)) A →
      Proposition1132At D S (c.binarySubspace (f.space 0)) A)
    (e : ((ofFlag S f X z H).L₁ ⧸ pCore 2 (ofFlag S f X z H).L₁) ≃*
      Matrix.ProjectiveSpecialLinearGroup (Fin 2) S.field.Carrier)
    (hcent : (ofFlag S f X z H).V₁ ≤ centralizer ((ofFlag S f X z H).R₁ : Set G))
    {J : Subgroup G} (hJ : J ∈ Chapter1.LStar G (T : Subgroup G))
    (hlt : (ofFlag S f X z H).Kz < J) :
    S.field.degree = 2 ∧
      (ProperEmbedding (ofFlag S f X z H).Kz J ∨ JankoFourPointPlacement (ofFlag S f X z H) J) := by
  obtain ⟨hd,hcases⟩ := ofFlag_proper_embedding_or_jankoFour
    S f X z H h hne hlinear h1132 e hcent hJ hlt
  rcases hcases with hpair | hj
  · exact ⟨hd,.inl hpair⟩
  · obtain ⟨b⟩ := hj
    obtain ⟨P,B,hB,hproper,hn,⟨a⟩,_⟩ := proper_local_model_image h.point_mem_local_family hJ.1
      (sylow_normalizes_overcomponent h hJ.1 hlt.le) (sylow_normalizes_point h) hlt b
    refine ⟨hd,.inr ⟨⟨b⟩,P,B,hB,hproper,hn,⟨a⟩,
      ofFlag_jankoFour_point_avoids_mathieuLocal S f X z H h hne hlinear h1132 e
        hJ.1 hlt b P B hB hn a,?_⟩⟩
    have hc := ofFlag_jankoFour_point_core_ne_bot S f X z H h hne hlinear h1132 e
      hJ.1 hlt b P B hB hproper hn a
    obtain ⟨t,ht,hpair⟩ := ofFlag_jankoFour_point_involution_placement S f X z H h hne
      hlinear h1132 e hJ.1 hlt b P B hB hn a hc
    exact ⟨hc,t,ht,hpair,jankoFour_full_sylow_centralizer_marking P t ht (le_sup_right.trans hpair)⟩
end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison.Overcomponent.EmbeddingProof
