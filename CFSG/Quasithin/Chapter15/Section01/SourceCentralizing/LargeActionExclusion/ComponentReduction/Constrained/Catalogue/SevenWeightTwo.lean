module
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.Constrained.Catalogue.SevenCentralizer
public import CFSG.Quasithin.ChapterC.Section01.BlockCohomology.AlternatingSeven.ModuleCentralizer
public import Theory.Representation.BinarySevenCode.MaximalStabilizers
public import Theory.GroupTheory.TwoLocalCharacteristicControl

public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.AlternatingSevenNormalAction
public import CFSG.Quasithin.ChapterB.Section03.Offenders.OddConjugation
public import Theory.GroupTheory.PGroup.NormalSupplementCore
public import Theory.Representation.BinaryPermutation.PointStabilizerRank.Seven

/-!
# The ordinary A₇ weight-two centralizer in the original local family

An original central involution is corrected by an element of U(K) to
centralize K. The correction is nontrivial and unique because C_U(K)(K)=1,
so N_S(K) fixes it. The singleton maximal-local hypothesis puts its
centralizer in M_Z. Maximality of every nonzero natural-module point
stabilizer then identifies the literal intersection M_Z ∩ K.

The actual C.2.7 input bounds the cubic rank of every subgroup of K
normalizing Q₁ by one. Otherwise the seven-letter action makes Q₁ even,
so the odd-core offender theorem puts J(Q₁) in O₂(KQ₁), contradicting
C.2.7's Thompson condition. Weight-four and weight-six stabilizers have
cubic rank two; the corrected point therefore has weight two.

The original-source application supplies Q₁-normalization through the
proved small-alternating input. Both source primes, the prescribed literal
two-core quotient marking and the later exchanged application are retained.
The three-pair partition placement and generation needed by 15.1.22(1)
remain separate obligations of this catalogue.

Source: Aschbacher--Smith 15.1.20(2b), printed pp.1094--1095, and
15.1.22(1), pp.1098--1099; C.1.13(c), pp.124--125, and C.2.7(2), p.146.
-/

public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender Stellmacher
namespace CFSG.Quasithin.Chapter15.Section01.CaseIComponentData
open ChapterC ChapterC.C27Source
open Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface
open Section03 Section03.InitialSource ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V : Subgroup G}

omit [Finite G] in
private theorem seven_fixed_trivial {K : Subgroup G} (hb : IsAlternatingBlock K 7)
    {u : G} (hu : u ∈ (blockU K).map K.subtype)
    (hc : u ∈ centralizer (K : Set G)) : u = 1 := by
  obtain ⟨v,hv,rfl⟩ := hu
  have hz : (⟨v,hv⟩ : blockU K) ∈ blockFixed K := by
    change v ∈ center K
    exact mem_center_iff.mpr fun k => Subtype.ext (hc k k.property)
  rw [hb.seven_fixed_eq_bot] at hz
  exact congrArg (fun x : blockU K => ((x : K) : G)) hz

omit [Finite G] in
private theorem seven_point_coatom {K : Subgroup G}
    (e : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 7))
    (E : blockU K ≃* Multiplicative (BinaryPermutation.core (Fin 7)))
    (hE : ∀ k u, E (blockConjugate K k u) =
      BinaryPermutation.SevenMarkedAction.coreAction
        (e (QuotientGroup.mk' (pCore 2 K) k)).val (E u))
    (u : blockU K) (hu : u ≠ 1) :
    IsCoatom ((centralizer ({((u : K) : G)} : Set G)).comap K.subtype) := by
  let w := BinarySevenCode.evenWordsEquivCore.symm (E u).toAdd
  have hw : w ≠ 0 := by
    intro hw
    apply hu
    apply E.injective
    apply Multiplicative.toAdd.injective
    rw [map_one]
    change (E u).toAdd = 0
    have hh := congrArg BinarySevenCode.evenWordsEquivCore hw
    simpa only [w, LinearEquiv.apply_symm_apply, map_zero] using hh
  apply BinarySevenCode.isCoatom_of_mem_iff_fixes_evenWord
    (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 K)))
    (e.surjective.comp (QuotientGroup.mk'_surjective _)) w hw
  intro k
  have he := hE k u
  constructor
  · intro hk
    have hh : blockConjugate K k u = u := by
      apply Subtype.ext
      apply Subtype.ext
      change (k : G) * ((u : K) : G) * (k : G)⁻¹ = ((u : K) : G)
      have hc : (k : G) * ((u : K) : G) = ((u : K) : G) * k :=
        mem_centralizer_singleton_iff.mp hk
      rw [hc,mul_inv_cancel_right]
    rw [hh] at he
    apply Subtype.ext
    exact congrArg (fun v => v.toAdd.val) he.symm
  · intro hk
    have hh : blockConjugate K k u = u := by
      apply E.injective
      rw [he]
      apply Multiplicative.toAdd.injective
      apply Subtype.ext
      exact congrArg (fun v : BinarySevenCode.EvenWord => v.val) hk
    apply mem_centralizer_singleton_iff.mpr
    have hh' := congrArg (fun x : blockU K => ((x : K) : G)) hh
    exact mul_inv_eq_iff_eq_mul.mp hh'

/-- The original marked intersection is the maximal centralizer of a
nonidentity block vector fixed by the full normalizer Sylow subgroup. -/
theorem localFamily_seven_point (d : CaseIComponentData T M Mc V)
    (h : PreparedChosenModule T M V) (hTM : (T : Subgroup G) ≤ M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    {K : Subgroup G} (hK : K ∈ Chapter1.LIn d.G1 d.S)
    (hq : IsQuasisimple (K ⧸ pCore 2 K)) (hout : ¬ K ≤ d.MZ)
    (hb : IsAlternatingBlock K 7)
    (e : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 7)) :
    ∃ E : blockU K ≃* Multiplicative (BinaryPermutation.core (Fin 7)),
      (∀ k u, E (blockConjugate K k u) =
        BinaryPermutation.SevenMarkedAction.coreAction
          (e (QuotientGroup.mk' (pCore 2 K) k)).val (E u)) ∧
      ∃ u : blockU K, u ≠ 1 ∧
        ((u : K) : G) ∈ centralizer (d.normalizerSylow K : Set G) ∧
        d.MZ ⊓ K = K ⊓ centralizer ({((u : K) : G)} : Set G) ∧
        IsCoatom ((d.MZ ⊓ K).subgroupOf K) := by
  let U := (blockU K).map K.subtype
  let H := K ⊔ d.normalizerSylow K
  have hHN : H ≤ normalizer (K : Set G) := sup_le le_normalizer inf_le_right
  have hHU : H ≤ normalizer (U : Set G) := hHN.trans
    (normalizer_le_normalizer_characteristic_image K (blockU K))
  have hUH : U ≤ H := (map_subtype_le _).trans le_sup_left
  have hUQ : U ≤ H.pCoreIn 2 := le_pCoreIn_of_normalizes
    ((pCore_isPGroup.to_le blockU_le_core).map K.subtype) hUH hHU
  obtain ⟨⟨P,hP⟩,_,hZR⟩ := d.localFamily_normalizer_setup h hTM hu hK hq hout hb.2.1.fitting
  have hUR : U ≤ d.normalizerSylow K := hUQ.trans (by
    have hh := map_mono (f := H.subtype) (pCore_isPGroup.le_sylow_of_normal P)
    exact hP ▸ hh)
  have hUT : U ≤ (T : Subgroup G) := hUR.trans (inf_le_left.trans d.S_le_T)
  have hMc : centralizer (centralInvolutions T : Set G) ≤ Mc :=
    (show Mc ∈ maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) from
      hu ▸ Set.mem_singleton Mc).2
  have hn : ¬ centralInvolutions T ≤ centralizer (K : Set G) := by
    intro hc
    exact hout (le_inf hK.1 ((le_centralizer_iff.mp hc).trans hMc))
  obtain ⟨z,hz,hzc⟩ := SetLike.not_le_iff_exists.mp hn
  have hz1 : z ≠ 1 := fun he => hzc (he ▸ one_mem _)
  have hzN : z ∈ normalizer (K : Set G) := (hZR hz).2
  have hzU : z ∈ centralizer (U : Set G) :=
    (centralizer_le hUT) (centralInvolutions_le_centralizer_sylow T hz)
  obtain ⟨u,huc⟩ := hb.seven_module_fixer_factorization hzN hzU
  have huU : ((u : K) : G) ∈ U := mem_map_of_mem K.subtype u.property
  have hu1 : u ≠ 1 := by
    intro he
    apply hzc
    simpa only [he,OneMemClass.coe_one,mul_one,one_mul] using huc
  have huR : ((u : K) : G) ∈ centralizer (d.normalizerSylow K : Set G) := by
    intro r hr
    have hrN := hr.2
    have hrz : r*z*r⁻¹ = z := by
      rw [centralInvolutions_le_centralizer_sylow T hz r (d.S_le_T hr.1),mul_inv_cancel_right]
    have hu' : r * ((u : K) : G) * r⁻¹ ∈ U :=
      (mem_normalizer_iff.mp (hHU (mem_sup_right hr)) _).mp huU
    have hc' : (r * ((u : K) : G) * r⁻¹) * z ∈ centralizer (K : Set G) := by
      have hh := (mem_normalizer_iff.mp (normalizer_le_normalizer_centralizer K hrN) _).mp huc
      have he : r * (((u : K) : G)*z) * r⁻¹ = (r*((u : K) : G)*r⁻¹)*z := by
        calc
          _ = (r*((u : K) : G)*r⁻¹)*(r*z*r⁻¹) := by group
          _ = _ := by rw [hrz]
      exact he ▸ hh
    have hd : ((u : K) : G) * (r * ((u : K) : G) * r⁻¹)⁻¹ ∈ centralizer (K : Set G) := by
      have hh := (centralizer (K : Set G)).mul_mem huc ((centralizer (K : Set G)).inv_mem hc')
      simpa only [mul_inv_rev,mul_assoc,mul_inv_cancel_left] using hh
    have hone := seven_fixed_trivial hb (U.mul_mem huU (U.inv_mem hu')) hd
    have he := mul_inv_eq_one.mp hone
    exact (mul_inv_eq_iff_eq_mul.mp he.symm)
  have hCz : centralizer ({z} : Set G) ≤ Mc := by
    have hzp : IsPGroup 2 (zpowers z) :=
      T.isPGroup'.to_le ((zpowers_le.mpr hz).trans (centralInvolutions_le_sylow T))
    have hh := centralizer_le_of_unique_twoLocal hzp
      (fun he => hz1 (show z ∈ (⊥ : Subgroup G) from he ▸ mem_zpowers z))
      ((centralizer_le (show (zpowers z : Set G) ⊆ centralInvolutions T from
        zpowers_le.mpr hz)).trans (Subgroup.centralizer_le_normalizer _))
      (M := Mc) (by
        intro N hN hCN
        exact Set.mem_singleton_iff.mp (hu ▸ (show N ∈ maximalTwoLocalOvergroups
          (centralizer (centralInvolutions T : Set G)) from ⟨hN,hCN⟩)))
    apply le_trans ?_ hh
    rw [le_centralizer_iff, zpowers_le]
    intro x hx
    exact mem_centralizer_singleton_iff.mp hx
  have hCu : K ⊓ centralizer ({((u : K) : G)} : Set G) ≤ d.MZ ⊓ K := by
    intro k hk
    refine ⟨⟨hK.1 hk.1,hCz ?_⟩,hk.1⟩
    apply mem_centralizer_singleton_iff.mpr
    have hc := huc k hk.1
    have hku := mem_centralizer_singleton_iff.mp hk.2
    symm
    calc
      z*k = ((u : K) : G)⁻¹ * ((((u : K) : G)*z)*k) := by group
      _ = ((u : K) : G)⁻¹ * (k*(((u : K) : G)*z)) := by rw [hc]
      _ = k*z := by rw [←mul_assoc k,hku]; group
  obtain ⟨E,hE⟩ := hb.seven_module_coordinates_at e
  have hc := seven_point_coatom e E hE u hu1
  have hproper : (d.MZ ⊓ K).subgroupOf K ≠ ⊤ := by
    intro he
    exact hout fun k hk => (he.ge (show (⟨k,hk⟩ : K) ∈ ⊤ from mem_top _)).1
  have he : (d.MZ ⊓ K).subgroupOf K = (centralizer ({((u : K) : G)} : Set G)).comap K.subtype :=
    (hc.le_iff_eq hproper).mp (fun k hk => hCu ⟨k.property,hk⟩)
  refine ⟨E,hE,u,hu1,huR,?_,he.symm ▸ hc⟩
  ext k
  constructor
  · intro hk
    refine ⟨hk.2,?_⟩
    change (⟨k,hk.2⟩ : K) ∈ (centralizer ({((u : K) : G)} : Set G)).comap K.subtype
    rw [←he]
    exact hk
  · intro hk
    exact hCu hk

private theorem seven_radical_normalizer_rank
    {H K Q N D : Subgroup G} (hi : Input KnownSimple.IsKnownSimple H Q N K)
    (hb : IsAlternatingBlock K 7) (hDK : D ≤ K)
    (hDQ : D ≤ normalizer (Q : Set G)) : primeRank 3 D ≤ 1 := by
  by_contra hsmall
  have hr : 2 ≤ primeRank 3 D := by omega
  let J := K ⊔ Q
  let K0 := K.subgroupOf J
  let Q0 := Q.subgroupOf J
  let D0 := D.subgroupOf J
  let e : K0 ≃* K := subgroupOfEquivOfLe le_sup_left
  let : K0.Normal := normal_subgroupOf_of_le_normalizer (sup_le le_normalizer hi.normalizes)
  have hb0 := RankOne.Solvable.isAlternatingBlock_of_equiv e.symm hb
  obtain ⟨q,E,f,hf,hE,himage,hker⟩ := hb0.seven_normal_action K0
  have hQ : IsPGroup 2 Q := by
    have hh := hi.setup.radical.isPGroup.map H.subtype
    rwa [map_subgroupOf_eq_of_le hi.setup.radical_le] at hh
  have heven : Q0.map f ≤ alternatingGroup (Fin 7) := by
    apply seven_normalized_two_image_even (X := K0) (K := D0)
      (fun x hx => hDK hx) _ hQ.comap_subtype _ f hker
    · rw [primeRank_congr 3 (subgroupOfEquivOfLe (hDK.trans le_sup_left))]
      exact hr
    · intro x hx
      apply mem_normalizer_iff.mpr
      intro y
      exact mem_normalizer_iff.mp (hDQ hx) (y : G)
  let W := (blockU K0).map K0.subtype
  let : W.Normal := by
    apply normalizer_eq_top_iff.mp
    exact top_unique ((show (⊤ : Subgroup J) ≤ normalizer (K0 : Set J) from
      le_normalizer_of_normal).trans (normalizer_le_normalizer_characteristic_image K0 (blockU K0)))
  let := hb0.2.1.elementary
  let : IsElementaryAbelian 2 W := IsElementaryAbelian.map K0.subtype
  let j : blockU K0 ≃* W := (blockU K0).equivMapOfInjective K0.subtype K0.subtype_injective
  let F : W ≃* Multiplicative (BinaryPermutation.core (Fin 7)) := j.symm.trans E
  have hF (g : J) (w : W) : (F (MulAut.conjNormal g w)).toAdd =
      BinaryPermutation.coreRepresentation (Fin 7) (f g) (F w).toAdd := by
    have hh : j.symm (MulAut.conjNormal g w) =
        MulAut.characteristic (blockU K0) (MulAut.conjNormal g) (j.symm w) := by
      apply j.injective
      rw [j.apply_symm_apply]
      apply Subtype.ext
      change g * (w : J) * g⁻¹ = g * (((j.symm w : blockU K0) : K0) : J) * g⁻¹
      congr 2
      exact (congrArg Subtype.val (j.apply_symm_apply w)).symm
    change (E (j.symm _)).toAdd = _
    rw [hh]
    exact hE g (j.symm w)
  have hcore : J.pCoreIn 2 ≤ Q := source_joinCore_le_radical (source_join_input hi)
  have hWQ : W ≤ Q0 := by
    intro w hw
    have hh := ((map_mono (f := K0.subtype) (blockU_le_core (L := K0))).trans
      (pCoreIn_le_of_subnormal 2 (inferInstance : K0.Normal).isSubnormal)) hw
    exact hcore (mem_map_of_mem J.subtype hh)
  have hJ := ChapterB.Offenders.thompson_le_kernel_of_even_core_action (Or.inr rfl) W Q0 hWQ f
    (seven_action_kernel K0 E f hE) F hF heven
  have hgen : K0 ⊔ Q0 = ⊤ := by
    rw [←subgroupOf_sup (show K ≤ J from le_sup_left) (show Q ≤ J from le_sup_right),
      subgroupOf_self]
  have hJcore : elementaryAbelianMaxJ Q0 ≤ pCore 2 J := by
    have hh := (le_inf ((sSup_le fun _ hA => hA.1).trans le_sup_right) hJ).trans
      (inf_ker_le_core_of_two_supplement f K0 Q0 le_normalizer_of_normal hQ.comap_subtype
        (hker ▸ pCore_isPGroup))
    rw [hgen] at hh
    exact hh.trans (pCoreIn_le_of_subnormal 2 (inferInstance : (⊤ : Subgroup J).Normal).isSubnormal)
  have hm := map_mono (f := J.subtype) hJcore
  rw [←elementaryAbelianMaxJ_map_injective J.subtype J.subtype_injective,
    map_subgroupOf_eq_of_le (show Q ≤ J from le_sup_right)] at hm
  have he := elementaryAbelianMaxJ_eq_of_intermediate Q (J.pCoreIn 2) hm hcore
  exact (kernel_offender_from_source hi).2.thompson he.ge

private theorem seven_point_weight_two {K : Subgroup G}
    (e : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 7))
    (E : blockU K ≃* Multiplicative (BinaryPermutation.core (Fin 7)))
    (hE : ∀ k u, E (blockConjugate K k u) =
      BinaryPermutation.SevenMarkedAction.coreAction
        (e (QuotientGroup.mk' (pCore 2 K) k)).val (E u))
    (u : blockU K) (hu : u ≠ 1)
    (hr : primeRank 3 ((centralizer ({((u : K) : G)} : Set G)).comap K.subtype) ≤ 1) :
    BinarySevenCode.weight (E u).toAdd.val = 2 := by
  let C := (centralizer ({((u : K) : G)} : Set G)).comap K.subtype
  let v := (E u).toAdd
  let B := BinaryNaturalDual.VectorStabilizers.representationStabilizer
    (BinaryPermutation.alternatingCoreRepresentation (Fin 7)) v
  let f := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 K))
  have hfs : Function.Surjective f := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hCB (k : K) : k ∈ C ↔ f k ∈ B := by
    change k ∈ C ↔ BinaryPermutation.coreRepresentation (Fin 7) (f k).val v = v
    constructor
    · intro hk
      have hh : blockConjugate K k u = u := by
        apply Subtype.ext
        apply Subtype.ext
        change (k : G) * ((u : K) : G) * (k : G)⁻¹ = ((u : K) : G)
        have hc : (k : G) * ((u : K) : G) = ((u : K) : G) * k :=
          mem_centralizer_singleton_iff.mp hk
        rw [hc,mul_inv_cancel_right]
      exact (congrArg Multiplicative.toAdd (hE k u)).symm.trans
        (congrArg (fun w => (E w).toAdd) hh)
    · intro hk
      have hh : blockConjugate K k u = u := by
        apply E.injective
        apply Multiplicative.toAdd.injective
        exact (congrArg Multiplicative.toAdd (hE k u)).trans hk
      apply mem_centralizer_singleton_iff.mpr
      exact mul_inv_eq_iff_eq_mul.mp (congrArg (fun w : blockU K => ((w : K) : G)) hh)
  let g : C →* B := (f.comp C.subtype).codRestrict B (fun k => (hCB k).mp k.property)
  have hgs : Function.Surjective g := by
    intro b
    obtain ⟨k,hk⟩ := hfs b
    exact ⟨⟨k,(hCB k).mpr (hk ▸ b.property)⟩,Subtype.ext hk⟩
  have hgker : IsPGroup 2 g.ker := by
    let j : g.ker →* pCore 2 K := (C.subtype.comp g.ker.subtype).codRestrict _ (by
      intro k
      apply (QuotientGroup.eq_one_iff (N := pCore 2 K) (k.val : K)).mp
      apply e.injective
      have hh := congrArg Subtype.val k.property
      exact hh.trans (map_one e).symm)
    apply pCore_isPGroup.of_injective j
    intro x y hh
    exact Subtype.ext (Subtype.ext (congrArg (fun z : pCore 2 K => (z : K)) hh))
  have hc : Nat.Coprime 3 (Nat.card g.ker) := by
    obtain ⟨n,hn⟩ := hgker.exists_card_eq
    rw [hn]
    exact (by decide : Nat.Coprime 3 2).pow_right n
  have hrB : primeRank 3 B ≤ 1 :=
    (primeRank_le_of_surjective_of_coprime 3 g hgs hc).trans hr
  let w := BinarySevenCode.evenWordsEquivCore.symm v
  have hw0 : w.val ≠ 0 := by
    intro hh
    have hw : w = 0 := Subtype.ext hh
    have hv := congrArg BinarySevenCode.evenWordsEquivCore hw
    have hv0 : v = 0 := by simpa only [w,LinearEquiv.apply_symm_apply,map_zero] using hv
    apply hu
    apply E.injective
    apply Multiplicative.toAdd.injective
    rw [map_one]
    exact hv0
  rcases BinarySevenCode.weight_of_mem_evenWords w.property hw0 with hw | hw | hw
  · exact hw
  · have hh := BinaryPermutation.PointStabilizerRank.two_le_weight_four_stabilizer v hw
    change 2 ≤ primeRank 3 B at hh
    exact False.elim (by omega)
  · have hh := BinaryPermutation.PointStabilizerRank.two_le_weight_six_stabilizer v hw
    change 2 ≤ primeRank 3 B at hh
    exact False.elim (by omega)

/-- The ordinary A7 row has its literal weight-two centralizer at the
prescribed two-core marking. The actual Q1 input rules out the other weights. -/
theorem localFamily_seven_weight_two (d : CaseIComponentData T M Mc V)
    (h : PreparedChosenModule T M V) (hTM : (T : Subgroup G) ≤ M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    {K : Subgroup G} (hK : K ∈ Chapter1.LIn d.G1 d.S)
    (hi : Input KnownSimple.IsKnownSimple d.G1 d.Q1 d.MZ K)
    (hb : IsAlternatingBlock K 7)
    (e : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 7)) :
    ∃ E : blockU K ≃* Multiplicative (BinaryPermutation.core (Fin 7)),
      (∀ k u, E (blockConjugate K k u) =
        BinaryPermutation.SevenMarkedAction.coreAction
          (e (QuotientGroup.mk' (pCore 2 K) k)).val (E u)) ∧
      ∃ u : blockU K, BinarySevenCode.weight (E u).toAdd.val = 2 ∧
        ((u : K) : G) ∈ centralizer (d.normalizerSylow K : Set G) ∧
        d.MZ ⊓ K = K ⊓ centralizer ({((u : K) : G)} : Set G) ∧
        IsCoatom ((d.MZ ⊓ K).subgroupOf K) := by
  obtain ⟨E,hE,u,hu1,huc,heq,hmax⟩ := d.localFamily_seven_point h hTM hu hK
    hi.quasisimple hi.outside hb e
  have hr := seven_radical_normalizer_rank hi hb (D := d.MZ ⊓ K) inf_le_right
    (inf_le_left.trans (d.MZ.le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image d.MZ (pCore 2 d.MZ))))
  have he : ((d.MZ ⊓ K).subgroupOf K) =
      (centralizer ({((u : K) : G)} : Set G)).comap K.subtype := by
    ext k
    change (k : G) ∈ d.MZ ⊓ K ↔ (k : G) ∈ centralizer ({((u : K) : G)} : Set G)
    rw [heq]
    exact and_iff_right k.property
  have hri : primeRank 3 ((centralizer ({((u : K) : G)} : Set G)).comap K.subtype) ≤ 1 := by
    rw [←he,primeRank_congr 3 (subgroupOfEquivOfLe (show d.MZ ⊓ K ≤ K from inf_le_right))]
    exact hr
  exact ⟨E,hE,u,seven_point_weight_two e E hE u hu1 hri,huc,heq,hmax⟩

/-- Weight-two placement before prime exclusion, with the original FF
quotient marking and both possible source primes retained. -/
theorem PreExclusionSource.constrained_seven_weight_two
    {d : CaseIComponentData T M Mc V} {h : PreparedChosenModule T M V} {p : ℕ}
    (s : d.PreExclusionSource h.normalized p)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hf : generalizedFitting d.L = pCore 2 d.L)
    (e : d.normalizerImage d.L ≃* alternatingGroup (Fin 7)) :
    IsAlternatingBlock d.L 7 ∧
      ∃ t : (d.L ⧸ pCore 2 d.L) ≃* alternatingGroup (Fin 7),
        (∀ k : d.L, t (QuotientGroup.mk' (pCore 2 d.L) k) = e (d.toNormalizerImage d.L k)) ∧
        ∃ E : blockU d.L ≃* Multiplicative (BinaryPermutation.core (Fin 7)),
          (∀ k u, E (blockConjugate d.L k u) =
            BinaryPermutation.SevenMarkedAction.coreAction
              (t (QuotientGroup.mk' (pCore 2 d.L) k)).val (E u)) ∧
          ∃ u : blockU d.L, BinarySevenCode.weight (E u).toAdd.val = 2 ∧
            ((u : d.L) : G) ∈ centralizer (d.normalizerSylow d.L : Set G) ∧
            d.ML = d.L ⊓ centralizer ({((u : d.L) : G)} : Set G) ∧
            IsCoatom (d.ML.subgroupOf d.L) := by
  obtain ⟨_,hi,_⟩ := s.constrained_small_alternating_input (h := h)
    hG hempty hM hJ hu hf (Or.inr rfl) e
  obtain ⟨hb,t,ht⟩ := s.constrained_seven_block (h := h) hG hempty hM hJ hu hf e
  exact ⟨hb,t,ht,d.localFamily_seven_weight_two h hM.1.2 hu
    ⟨d.L_component.1,s.local_component⟩ hi hb t⟩

/-- The later exchanged selection has the same marked weight-two centralizer. -/
theorem ExchangedSource.constrained_seven_weight_two
    {d : CaseIComponentData T M Mc V} (s : d.ExchangedSource)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (h : PreparedChosenModule T M V)
    (hf : generalizedFitting d.L = pCore 2 d.L)
    (e : d.normalizerImage d.L ≃* alternatingGroup (Fin 7)) :
    IsAlternatingBlock d.L 7 ∧
      ∃ t : (d.L ⧸ pCore 2 d.L) ≃* alternatingGroup (Fin 7),
        (∀ k : d.L, t (QuotientGroup.mk' (pCore 2 d.L) k) = e (d.toNormalizerImage d.L k)) ∧
        ∃ E : blockU d.L ≃* Multiplicative (BinaryPermutation.core (Fin 7)),
          (∀ k u, E (blockConjugate d.L k u) =
            BinaryPermutation.SevenMarkedAction.coreAction
              (t (QuotientGroup.mk' (pCore 2 d.L) k)).val (E u)) ∧
          ∃ u : blockU d.L, BinarySevenCode.weight (E u).toAdd.val = 2 ∧
            ((u : d.L) : G) ∈ centralizer (d.normalizerSylow d.L : Set G) ∧
            d.ML = d.L ⊓ centralizer ({((u : d.L) : G)} : Set G) ∧
            IsCoatom (d.ML.subgroupOf d.L) := by
  obtain ⟨_,hi,_⟩ := s.constrained_small_alternating_input hG hempty hM hJ hu h hf (Or.inr rfl) e
  obtain ⟨hb,t,ht⟩ := s.constrained_seven_block hG hempty hM hJ hu h hf e
  exact ⟨hb,t,ht,d.localFamily_seven_weight_two h hM.1.2 hu
    ⟨d.L_component.1,s.local_component⟩ hi hb t⟩

end CFSG.Quasithin.Chapter15.Section01.CaseIComponentData

namespace CFSG.Quasithin.Chapter15.Section01
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender Stellmacher ChapterC
open Section03 Section03.InitialSource ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]

/-- The actual original marker supplies the weight-two centralizer on the
same component and quotient. Original 15.1.14 remains explicit. -/
theorem PreparedChosenModule.source_preExclusion_constrained_seven_weight_two
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc V : Subgroup G} (hM : IsOrderingMaximal T M)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hne : M ≠ Mc) (h : PreparedChosenModule T M V)
    (hfull : V = localModule T M)
    (m : CaseIPreExclusionMarker T M V h.normalized)
    (hres : (pResidual 2 (centralizer (centralInvolutions T : Set G))).map
      (centralizer (centralInvolutions T : Set G)).subtype ≤
        centralizer (thompsonFixed T V : Set G)) :
    ∃ d : CaseIComponentData T M Mc V, d.Z1 = m.Z1 ∧ d.row = m.row ∧
      d.PreExclusionSource h.normalized m.prime ∧
      (generalizedFitting d.L = pCore 2 d.L →
        ∀ e : d.normalizerImage d.L ≃* alternatingGroup (Fin 7),
          IsAlternatingBlock d.L 7 ∧
          ∃ t : (d.L ⧸ pCore 2 d.L) ≃* alternatingGroup (Fin 7),
            (∀ k : d.L, t (QuotientGroup.mk' (pCore 2 d.L) k) = e (d.toNormalizerImage d.L k)) ∧
            ∃ E : blockU d.L ≃* Multiplicative (BinaryPermutation.core (Fin 7)),
              (∀ k u, E (blockConjugate d.L k u) =
                BinaryPermutation.SevenMarkedAction.coreAction
                  (t (QuotientGroup.mk' (pCore 2 d.L) k)).val (E u)) ∧
              ∃ u : blockU d.L, BinarySevenCode.weight (E u).toAdd.val = 2 ∧
                ((u : d.L) : G) ∈ centralizer (d.normalizerSylow d.L : Set G) ∧
                d.ML = d.L ⊓ centralizer ({((u : d.L) : G)} : Set G) ∧
                IsCoatom (d.ML.subgroupOf d.L)) := by
  obtain ⟨d,hZ,hr,s⟩ := h.component_of_preExclusionMarker
    hG T hempty hM hmany hJ hu hne hfull m hres
  exact ⟨d,hZ,hr,s,fun hf e =>
    s.constrained_seven_weight_two (h := h) hG hempty hM hJ hu hf e⟩

end CFSG.Quasithin.Chapter15.Section01
