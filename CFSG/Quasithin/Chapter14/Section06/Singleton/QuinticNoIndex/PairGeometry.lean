module
public import CFSG.Quasithin.Chapter14.Section06.Singleton.QuinticNoIndex.Wreath
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.OddNormalizer.Quintic.ModuleGeometry.ExchangedFactors

/-!
# The actual component pair before the factor-join index

The no-index strict-closure theorem supplies a PSL₂(16) component and its
exchanged conjugate. Transport their intrinsic core quotients and use exact
order-five generation to identify the ordinary central-point closure with
K_z. The prime-to-five residual identity proves the reverse inclusion.
Relative component normalizers have index two, and their intrinsic two-core
is the original Mc two-core. This constructs the existing ExchangedFactorData
interface without the earlier index-bearing Context or full wreath surjectivity.

The two components have not been identified with the original D10 factor
residuals. That support comparison and the outer contradiction remain open.
Source: Aschbacher--Smith 14.6.14--15, printed pp.1033--1034.
-/

public section
open Subgroup Theory.GroupTheory Representation.BinaryOffender
open scoped IsMulCommutative Pointwise
namespace CFSG.Quasithin.Chapter14.Section06
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open Chapter15.Section03.AbelianAmalgam
open Chapter15.Section03.AbelianAmalgam.GenerationOne
open OddNormalizer Chapter1 Chapter1.XiEmbedding
open Chapter13.Section08.Components.Models Chapter13.Section08.Components.SourceModels
open OddNormalizer.Quintic.ModuleGeometry (ExchangedFactorData component_normalizer_intersection_core)
namespace Singleton.QuinticNoIndex
open SourcePairCompatibility.QuinticGeometryParallel

private theorem component_core_model {G : Type*} [Group G] [Finite G]
    {Mc K : Subgroup G} (hK : K ≤ Mc) (hc : (K.subgroupOf Mc).IsCComponent)
    (hm : ClassicalGroup.IsPSL
      ((K.subgroupOf Mc).map (QuotientGroup.mk' (pCore 2 Mc))) 2 16) :
    Nonempty ((K ⧸ pCore 2 K) ≃* Theory.PSL2.SixteenWreathComponents.L) := by
  obtain ⟨em⟩ := binary_component_equiv (m := 4) hm
  let ek := subgroupOfEquivOfLe hK
  exact ⟨(QuotientGroup.congr _ _ ek (pCore_map_iso 2 ek)).symm.trans
    ((cComponentTwoCoreQuotientEquiv hc).trans em)⟩

private theorem component_five_generated {G : Type*} [Group G] [Finite G]
    {Mc K : Subgroup G} (hK : K ≤ Mc) (hc : (K.subgroupOf Mc).IsCComponent)
    (em : Nonempty ((K ⧸ pCore 2 K) ≃* Theory.PSL2.SixteenWreathComponents.L)) :
    closure {x : G | x ∈ K ∧ orderOf x = 5} = K := by
  obtain ⟨f⟩ := em
  let := Theory.PSL2.SixteenWreathComponents.simple
  let : IsSimpleGroup (K ⧸ pCore 2 K) := f.isSimpleGroup
  let := hc.perfect
  let : Group.IsPerfect K := Group.IsPerfect.ofSurjective
    (f := (subgroupOfEquivOfLe hK).toMonoidHom) (subgroupOfEquivOfLe hK).surjective
  have hp : IsPPerfect 2 K := by
    intro N hN hQ
    let := hN
    let : Group.IsNilpotent (K ⧸ N) := hQ.isNilpotent
    exact top_le_iff.mp (le_of_isPerfect_of_solvable_quotient ⊤ N)
  have hd : 5 ∣ Nat.card (K ⧸ pCore 2 K) := by
    rw [Nat.card_congr f.toEquiv]
    exact Theory.PSL2.SixteenWreathComponents.five_dvd_card
  have ht := closure_prime_order_eq_top_of_simple_quotient (pCore 2 K)
    pCore_isPGroup hp (by decide : Nat.Coprime 2 5) hd
  apply le_antisymm ((closure_le _).mpr (fun _ hx => hx.1))
  intro x hx
  have hl : closure {y : K | orderOf y = 5} ≤
      (closure {y : G | y ∈ K ∧ orderOf y = 5}).comap K.subtype := by
    apply (closure_le _).mpr
    intro y hy
    exact subset_closure ⟨y.property,(Subgroup.orderOf_coe y).trans hy⟩
  exact hl (ht.ge (mem_top (⟨x,hx⟩ : K)))

private theorem component_pair_indices {G : Type*} [Group G] [Finite G]
    {T Mc Kz K1 : Subgroup G} (hTM : T ≤ Mc) (h1 : K1 ≤ Mc)
    (hc : (K1.subgroupOf Mc).IsCComponent) {t : G} (ht : t ∈ T)
    (hnt : t ∉ normalizer (K1 : Set G))
    (hKN : Mc ≤ normalizer (Kz : Set G))
    (hprod : (Kz : Set G) =
      (K1 : Set G) * (K1.map (MulAut.conj t⁻¹).toMonoidHom : Set G)) :
    let K2 := K1.map (MulAut.conj t⁻¹).toMonoidHom
    K2 ≤ Mc ∧ (K2.subgroupOf Mc).IsCComponent ∧
      K1 ⊔ K2 = Kz ∧
      (Mc ⊓ normalizer (K1 : Set G)).relIndex Mc = 2 ∧
      (Mc ⊓ normalizer (K2 : Set G)).relIndex Mc = 2 := by
  let K2 := K1.map (MulAut.conj t⁻¹).toMonoidHom
  let r : Mc := ⟨t⁻¹,hTM (inv_mem ht)⟩
  have h2 : K2 ≤ Mc := conj_smul_le_of_le h1 r
  have he : (K1.subgroupOf Mc).conjBy r = K2.subgroupOf Mc :=
    conj_smul_subgroupOf h1 r
  have hc2 : (K2.subgroupOf Mc).IsCComponent :=
    he ▸ hc.map_equiv (MulAut.conj r)
  have hj : K1 ⊔ K2 = Kz := by
    rw [sup_eq_closure_mul,←hprod,closure_eq]
  have hn : ((K1.subgroupOf Mc) ⊔ (K1.subgroupOf Mc).conjBy r).Normal := by
    rw [he,←subgroupOf_sup h1 h2,hj]
    exact normal_subgroupOf_of_le_normalizer hKN
  let := hn
  have hne : K1.subgroupOf Mc ≠ (K1.subgroupOf Mc).conjBy r := by
    intro hh
    have hm := mem_normalizer_iff_map_conj_eq.mpr hh.symm
    rw [←subgroupOf_normalizer_eq h1] at hm
    have hmi : t⁻¹ ∈ normalizer (K1 : Set G) := hm
    have hmt := (normalizer (K1 : Set G)).inv_mem hmi
    exact hnt (by simpa only [inv_inv] using hmt)
  have hi1 := hc.normalizer_index_two_of_normal_pair r hne
  have hi2 : (normalizer (K2.subgroupOf Mc : Set Mc)).index = 2 := by
    rw [←he]
    change (normalizer ((K1.subgroupOf Mc).map (MulAut.conj r).toMonoidHom : Set Mc)).index = 2
    rw [←map_equiv_normalizer_eq (K1.subgroupOf Mc) (MulAut.conj r),
      index_map_of_bijective (MulAut.conj r).bijective]
    exact hi1
  have hi (K : Subgroup G) (hK : K ≤ Mc)
      (h : (normalizer (K.subgroupOf Mc : Set Mc)).index = 2) :
      (Mc ⊓ normalizer (K : Set G)).relIndex Mc = 2 := by
    rw [inf_relIndex_left]
    change ((normalizer (K : Set G)).subgroupOf Mc).index = 2
    rwa [subgroupOf_normalizer_eq hK]
  exact ⟨h2,hc2,hj,hi K1 h1 hi1,hi K2 h2 hi2⟩

variable {G : Type*} [Group G] [Finite G]
variable (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hab : IsMulCommutative (conjugateSpanBy (localModule T M) Mc))
variable (J : Subgroup G) (hJ : J ∈ Chapter3.HStar (T : Subgroup G) M)
    (hs : Group.IsSolvable J)
    [IsElementaryAbelian 2 (conjugateSpanBy (localModule T M) J)]
    (a : LocalQuotientAction J (conjugateSpanBy (localModule T M) J) (centralInvolutions T))
    (f : ChapterD.RatioDecomposition.FactorData a.representation
      (ChapterD.Jhat a.representation)
      (subspaceCommutator a.representation ⊤ (pResidual 2 (J ⧸ pCore 2 J))))
    (d : ChapterD.RatioDecomposition.Decomposition f.representation)
    (π : (J ⧸ pCore 2 J) →* Equiv.Perm d.Index)
    (w : SourcePairCompatibility.QuinticOuterAction a f d π)


include hG hempty hM hu hmany hcard e hab hJ hs w

/-- The original central point is in the closure core. Thus maximal
 two-locality identifies the normalizer in either closure branch. -/
theorem source_quintic_closure_normalizer :
    normalizer (residualClosure J Mc : Set G) = Mc := by
  let K := residualClosure J Mc
  have hJMc : J ≤ Mc :=
    (source_rankTwo_f9_hypothesis hG T hempty hM hu hmany hcard e hab J hJ.1).H_centralizes.trans
      (InitialSource.centralizer_le_partner T hu)
  have hMc : Mc = centralizer (centralInvolutions T : Set G) :=
    (source_lemma_14_1_18 hG T hempty hM hu hmany hcard e).2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hZ : centralInvolutions T ≤ K :=
    ((source_factor_residual_point_core hG T hempty hM hu hmany hcard e hab
      J hJ hs a f d w.factor).trans (pCoreIn_le 2 _)).trans
      ((embedded_pResidual_mono 2 (actorPreimage_le J _)).trans (le_conjugateSpanBy _ _))
  have hKM : K ≤ Mc := conjugateSpanBy_le
    ((residual_le J).trans hJMc) Mc.le_normalizer
  have hZN : K ≤ normalizer (centralInvolutions T : Set G) :=
    (hKM.trans_eq hMc).trans (Subgroup.centralizer_le_normalizer _)
  have hZQ : centralInvolutions T ≤ K.pCoreIn 2 :=
    le_pCoreIn_of_normalizes ((IsElementaryAbelian.isPGroup 2
      (conjugateSpanBy (localModule T M) J)).to_le a.kernel_le) hZ hZN
  have hne : K.pCoreIn 2 ≠ ⊥ := by
    intro hb
    have hz := bot_unique (hb ▸ hZQ)
    have hc := plane_centralInvolutions_card T M hM.1.2 hcard e
    have hc0 : Nat.card (centralInvolutions T) = 1 := (eq_bot_iff_card _).mp hz
    omega
  have hMN : Mc ≤ normalizer (K : Set G) := le_normalizer_conjugateSpanBy _ _
  have hNQ : normalizer (K : Set G) ≤ normalizer (K.pCoreIn 2 : Set G) :=
    normalizer_le_normalizer_characteristic_image K (pCore 2 K)
  have hmax : IsMaximalTwoLocal Mc :=
    (show Mc ∈ maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) from
      hu ▸ Set.mem_singleton Mc).1
  exact le_antisymm (hNQ.trans (hmax.2 ⟨_,hne,isPGroup_pCoreIn 2 K,rfl⟩
    (hMN.trans hNQ))) hMN

/-- Construct the literal exchanged-factor interface without the index of
Jhat. In particular θ(C_G(Z)) = K_z and both component normalizers, their
Sylow index, intrinsic models and the second intersection core are proved. -/
theorem source_quintic_strict_factor_data
    (hne : residualClosure J Mc ≠ residual J) :
    Nonempty (ExchangedFactorData (T : Subgroup G) Mc J (centralInvolutions T)) := by
  obtain ⟨K1,h1,hc1,_hq,_hcl,_hi,⟨t,ht,hnt,hprod⟩,hm,hr5,_hr3,_hlayer⟩ :=
    source_quintic_strict_closure_layer hG T hempty hM hu hmany hcard e hab
      J hJ hs a f d π w hne
  let K2 := K1.map (MulAut.conj t⁻¹).toMonoidHom
  have hTM : (T : Subgroup G) ≤ Mc := AlternatingThree.sylow_le_partner T hu
  obtain ⟨h2,hc2,hj,hi1,hi2⟩ := component_pair_indices hTM h1 hc1 ht hnt
    (le_normalizer_conjugateSpanBy _ _) hprod
  have em1 := component_core_model h1 hc1 hm
  let ec := (MulAut.conj t⁻¹).subgroupMap K1
  have em2 : Nonempty ((K2 ⧸ pCore 2 K2) ≃* Theory.PSL2.SixteenWreathComponents.L) :=
    ⟨(QuotientGroup.congr _ _ ec (pCore_map_iso 2 ec)).symm.trans em1.some⟩
  have hg1 := component_five_generated h1 hc1 em1
  have hg2 := component_five_generated h2 hc2 em2
  have hne12 : K1 ≠ K2 := by
    intro he
    have hm : t⁻¹ ∈ normalizer (K1 : Set G) := mem_normalizer_iff_map_conj_eq.mpr he.symm
    exact hnt (inv_mem_iff.mp hm)
  have hnt2 : t ∉ normalizer (K2 : Set G) := by
    intro hn
    have he2 : K2.map (MulAut.conj t⁻¹).toMonoidHom = K2 :=
      mem_normalizer_iff_map_conj_eq.mp (inv_mem hn)
    exact hne12 (map_injective (MulAut.conj t⁻¹).injective he2.symm)
  have hMc : Mc = centralizer (centralInvolutions T : Set G) :=
    (source_lemma_14_1_18 hG T hempty hM hu hmany hcard e).2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hpoint : closure {x : G | x ∈ centralizer (centralInvolutions T : Set G) ∧
      orderOf x = 5} = residualClosure J Mc := by
    apply le_antisymm
    · apply (closure_le _).mpr
      intro x hx
      rw [hr5]
      have hxM : x ∈ Mc := hMc.ge hx.1
      refine ⟨⟨x,hxM⟩,mem_primeToResidual_of_pow (n := 1) ?_,rfl⟩
      apply Subtype.ext
      change x ^ 5 = 1
      rw [←hx.2,pow_orderOf_eq_one]
    · change K1 ⊔ K2 = residualClosure J Mc at hj
      rw [←hj]
      have hfactor (K : Subgroup G) (hK : K ≤ Mc)
          (hg : closure {x : G | x ∈ K ∧ orderOf x = 5} = K) :
          K ≤ closure {x : G | x ∈ centralizer (centralInvolutions T : Set G) ∧ orderOf x = 5} := by
        rw [←hg]
        apply Subgroup.closure_mono
        intro x hx
        exact ⟨hMc.le (hK hx.1),hx.2⟩
      exact sup_le (hfactor K1 h1 hg1) (hfactor K2 h2 hg2)
  exact ⟨{
    K1 := K1
    K2 := K2
    first_le := h1
    second_le := h2
    first_component := hc1
    second_component := hc2
    join_eq := hj
    first_model := em1
    second_model := em2
    first_generated := hg1
    second_generated := hg2
    exchanged := ⟨t,ht,hnt,rfl⟩
    first_index := hi1
    second_index := hi2
    sylow_index := normalizer_relIndex_eq_two_of_index_two_overgroup (T : Subgroup G)
      Mc (Mc ⊓ normalizer (K2 : Set G)) K2 hTM hi2 inf_le_right ⟨t,ht,hnt2⟩
    intersection_core := component_normalizer_intersection_core h2 hc2 hi2
    point_closure := hpoint
    closure_normalizer := source_quintic_closure_normalizer hG T hempty hM hu hmany hcard e hab
      J hJ hs a f d π w }⟩

end Singleton.QuinticNoIndex
end CFSG.Quasithin.Chapter14.Section06
