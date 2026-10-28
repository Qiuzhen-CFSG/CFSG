module

public import CFSG.Quasithin.Chapter12.Section04.SmallFusion.SLThreeSource.FixedBlockSpecializationProductsKernelReduction
public import CFSG.Quasithin.Chapter12.Section04.SmallFusion.SLThreeSource.MovingResidualConstructionCubic
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.LinearThreeInvolutoryLift
public import Theory.GroupTheory.Commutator.FourPlaneDisplacement
public import Theory.GroupTheory.PCoreCoverEquiv
public import Theory.GroupTheory.PCoreImage
public import Theory.SpecificGroups.PSL3Two.Parabolics.OddIndex

/-!
# Kernel centralization for the original fixed-line MS product

Write P = O₂(L), Q = C_T(V), A = L ∩ R, and F = [R,R]. The literal
index-seven MS stabilizer gives R/Q an elementary four-group image, so
F ≤ Q. Escape supplies MS3: if V ≤ F, then [L,F] ≤ V ≤ F makes the
characteristic subgroup F normal in LR, a contradiction.

If q ∈ Q acts nontrivially on P, the bound |P| ≤ 32 gives C_P(q) = V.
Every a ∈ A outside P squares into P but not V: otherwise the perfect
central cover L/V → SL₃(2) has a noncentral involutory lift and P = V.
Thus the displacement map A → V/E, a ↦ [a,q]E, has kernel P. Its image
has order four, while E = [A,V] ≤ F, forcing V ≤ F. This contradiction
proves [P,Q] = 1. The existing H¹ correction then gives Q = V C_T(L).

The marked fifth MS alternative and msQ = V remain the inputs produced by
qt-d-1246-l3-ms-specialization. Structural1222 and SLThreeAlternative1222
remain the authorized earlier-source premises. The parent
qt-d-1246-l3-ms-centralizer-products owns their final discharge and assembly
with the independent residual calculation. There is no kernel callback.

Source: Aschbacher--Smith 12.4.6, printed pp.813--814; C.1.13(b),
pp.124--125; C.1.31--34, pp.135--137; B.4.8(4), pp.91--92.
-/

public section
open Subgroup Theory.GroupTheory Representation
open scoped IsMulCommutative commutatorElement Pointwise

namespace CFSG.Quasithin.Chapter12.Section04.SmallFusion.SLThreeSource
open Section02 ChapterC
open Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} {D : ChosenModule T L V}
namespace LocalGeometry
variable (d : LocalGeometry D)

private theorem kernel_quotient_map
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (ext : SLThreeExtension D)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G)) :
    ∃ q : (L ⊔ d.R : Subgroup G) →* Matrix.PSL3Two.SL,
      Function.Surjective q ∧ q.ker = pCore 2 (L ⊔ d.R : Subgroup G) ∧
      ∀ l : L, q (inclusion le_sup_left l) =
        ext.quotientEquiv (QuotientGroup.mk' (pCore 2 L) l) := by
  let H := L ⊔ d.R
  have hcover : (H : Set G) ⊆ (L : Set G) * (H.pCoreIn 2 : Set G) := by
    intro g hg
    let : ((H.pCoreIn 2).subgroupOf H).Normal :=
      normal_subgroupOf_of_le_normalizer (H.le_normalizer.trans
        (normalizer_le_normalizer_characteristic_image H (pCore 2 H)))
    have hm : (⟨g,hg⟩ : H) ∈ L.subgroupOf H ⊔ (H.pCoreIn 2).subgroupOf H := by
      rw [← subgroupOf_sup le_sup_left (pCoreIn_le 2 H)]
      have he : L ⊔ H.pCoreIn 2 = H := by
        dsimp only [H]
        rw [d.ms_join_eq ext h hTV, ← join_eq_component_sup_core D ext hTV]
      rw [he, subgroupOf_self]
      trivial
    obtain ⟨l,hl,k,hk,he⟩ := mem_sup_of_normal_right.mp hm
    exact ⟨l,hl,k,hk,congrArg Subtype.val he⟩
  obtain ⟨e,he⟩ := exists_pCoreQuotientEquiv_of_cover (p := 2)
    (show L ≤ H from le_sup_left) hcover
  let a := e.symm.trans ext.quotientEquiv
  let q := a.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 H))
  refine ⟨q,a.surjective.comp (QuotientGroup.mk'_surjective _),?_,?_⟩
  · rw [MonoidHom.ker_comp_of_injective _ _ a.injective,QuotientGroup.ker_mk']
  · intro l
    change ext.quotientEquiv (e.symm (QuotientGroup.mk' (pCore 2 H)
      (inclusion le_sup_left l))) = _
    rw [← he l, e.symm_apply_apply]

private theorem index_seven_core_image
    {H : Type*} [Group H] [Finite H]
    (q : H →* Matrix.PSL3Two.SL) (hq : Function.Surjective q)
    (hk : IsPGroup 2 q.ker) (S : Sylow 2 H) (A : Subgroup H)
    (hSA : (S : Subgroup H) ≤ A) (hA : A.index = 7) :
    IsElementaryAbelian 2 ((A.pCoreIn 2).map q) ∧
      Nat.card ((A.pCoreIn 2).map q) = 4 := by
  let B := A.map q
  have hBi : B.index = 7 :=
    (A.index_map_eq hq ((hk.le_sylow_of_normal S).trans hSA)).trans hA
  have hBc : Nat.card B = 24 := by
    have hh := B.index_mul_card
    rw [hBi, Matrix.PSL3Two.card_SL] at hh
    omega
  have hBn : B ≠ ⊤ := by intro he; simp only [he,index_top] at hBi; omega
  have hBt : ¬ IsPGroup 2 B := by
    intro hp
    obtain ⟨n,hn⟩ := hp.exists_card_eq
    rw [hBc] at hn
    have hd : 3 ∣ 2 ^ n := hn ▸ (by decide : 3 ∣ 24)
    exact (by decide : ¬ 3 ∣ 2) (Nat.prime_three.dvd_of_dvd_pow hd)
  rw [map_pCoreIn_of_ker_isPGroup q hk A]
  exact Matrix.PSL3Two.odd_index_core_data B hBn (by rw [hBi]; decide) hBt

/-- The original point stabilizer identifies the literal radical image with an elementary four-group; the quotient agrees with the component marking. -/
theorem ms_radical_quotient_data
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (ext : SLThreeExtension D)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (e : (L ⧸ pCore 2 L) ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2))
    (hcase : FixedMSAlternative L d.R T e) :
    ∃ q : (L ⊔ d.R : Subgroup G) →* Matrix.PSL3Two.SL,
      Function.Surjective q ∧ q.ker = pCore 2 (L ⊔ d.R : Subgroup G) ∧
      (∀ l : L, q (inclusion le_sup_left l) =
        ext.quotientEquiv (QuotientGroup.mk' (pCore 2 L) l)) ∧
      IsElementaryAbelian 2 ((d.R.subgroupOf (L ⊔ d.R)).map q) ∧
      Nat.card ((d.R.subgroupOf (L ⊔ d.R)).map q) = 4 := by
  obtain ⟨q,hq,hk,hl⟩ := d.kernel_quotient_map h ext hTV
  obtain ⟨A,v,hv,hAH,hTA,hAi,hAR,_⟩ := hcase.2.2.2.2
  let H := L ⊔ d.R
  have hTH : (T : Subgroup G) ≤ H := by
    change (T : Subgroup G) ≤ L ⊔ d.R
    rw [d.ms_join_eq ext h hTV]
    exact le_sup_right
  have hmap : ((A.subgroupOf H).pCoreIn 2).map H.subtype = d.R := by
    rw [map_pCoreIn_of_injective 2 _ _ H.subtype_injective,
      map_subgroupOf_eq_of_le hAH,hAR]
  have hcore : (A.subgroupOf H).pCoreIn 2 = d.R.subgroupOf H := by
    apply map_injective H.subtype_injective
    rw [hmap,map_subgroupOf_eq_of_le (show d.R ≤ H from le_sup_right)]
  have hc := index_seven_core_image q hq (by rw [hk]; exact pCore_isPGroup)
    (T.subtype hTH) (A.subgroupOf H) (by
      rw [Sylow.coe_subtype]
      exact fun _ hx => hTA hx) hAi
  rw [hcore] at hc
  exact ⟨q,hq,hk,hl,hc⟩

/-- The derived subgroup of R is in the original ambient core C_T(V). -/
theorem ms_radical_commutator_le_core
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (ext : SLThreeExtension D)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (e : (L ⧸ pCore 2 L) ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2))
    (hcase : FixedMSAlternative L d.R T e) :
    ⁅d.R,d.R⁆ ≤ (T : Subgroup G) ⊓ centralizer (V : Set G) := by
  obtain ⟨q,hq,hk,hl,he,hc⟩ := d.ms_radical_quotient_data h ext hTV e hcase
  let := he
  have hm : (⁅d.R.subgroupOf (L ⊔ d.R),d.R.subgroupOf (L ⊔ d.R)⁆).map q = ⊥ := by
    rw [map_commutator,commutator_self_eq_bot_iff]
    infer_instance
  have hle : ⁅d.R.subgroupOf (L ⊔ d.R),d.R.subgroupOf (L ⊔ d.R)⁆ ≤
      pCore 2 (L ⊔ d.R : Subgroup G) := by
    rw [← hk, ← MonoidHom.comap_bot]
    exact map_le_iff_le_comap.mp hm.le
  have hh := map_mono (f := (L ⊔ d.R : Subgroup G).subtype) hle
  rw [map_commutator,map_subgroupOf_eq_of_le le_sup_right] at hh
  exact hh.trans (d.ms_core_eq ext h hTV).le

/-- The component intersection has exactly four cosets modulo O₂(L). -/
theorem ms_component_radical_index
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (ext : SLThreeExtension D)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (e : (L ⧸ pCore 2 L) ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2))
    (hcase : FixedMSAlternative L d.R T e) :
    (L.pCoreIn 2).relIndex (L ⊓ d.R) = 4 := by
  obtain ⟨q,hq,hk,hl,he,hc⟩ := d.ms_radical_quotient_data h ext hTV e hcase
  let H := L ⊔ d.R
  let π : L →* Matrix.PSL3Two.SL :=
    ext.quotientEquiv.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))
  have hπ : Function.Surjective π := ext.quotientEquiv.surjective.comp
    (QuotientGroup.mk'_surjective _)
  have hπk : π.ker = pCore 2 L := by
    rw [MonoidHom.ker_comp_of_injective _ _ ext.quotientEquiv.injective,
      QuotientGroup.ker_mk']
  have hkR : q.ker ≤ d.R.subgroupOf H := by
    intro x hx
    rw [hk] at hx
    have hx' : (x : G) ∈ H.pCoreIn 2 := mem_map_of_mem H.subtype hx
    rw [d.ms_core_eq ext h hTV] at hx'
    exact ⟨hx'.1, centralizer_le d.le_module hx'.2⟩
  have hm : (d.R.subgroupOf L).map π = (d.R.subgroupOf H).map q := by
    apply le_antisymm
    · rintro _ ⟨l,hlR,rfl⟩
      exact ⟨inclusion le_sup_left l,hlR,hl l⟩
    · rintro _ ⟨r,hr,rfl⟩
      obtain ⟨l,hel⟩ := hπ (q r)
      have hk' : (inclusion le_sup_left l)⁻¹ * r ∈ q.ker := by
        change q ((inclusion le_sup_left l)⁻¹ * r) = 1
        rw [map_mul,map_inv,hl l,← hel]
        exact inv_mul_cancel (π l)
      have hR : ((l : G)⁻¹ * (r : G)) ∈ d.R := hkR hk'
      have hlR : (l : G) ∈ d.R := by
        have hh := d.R.mul_mem hr (d.R.inv_mem hR)
        have hid : (r : G) * ((l : G)⁻¹ * (r : G))⁻¹ = (l : G) := by group
        exact hid ▸ hh
      exact ⟨l,hlR,hel⟩
  have hi := relIndex_ker (d.R.subgroupOf L) π
  rw [hπk,hm,hc] at hi
  have hi' := relIndex_map_map_of_injective (pCore 2 L) (d.R.subgroupOf L)
    L.subtype_injective
  rw [subgroupOf_map_subtype,inf_comm] at hi'
  exact hi'.trans hi

/-- Every element of the component intersection squares into O₂(L). -/
theorem ms_component_radical_square
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (ext : SLThreeExtension D)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (e : (L ⧸ pCore 2 L) ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2))
    (hcase : FixedMSAlternative L d.R T e)
    (a : G) (haL : a ∈ L) (haR : a ∈ d.R) : a ^ 2 ∈ L.pCoreIn 2 := by
  obtain ⟨q,hq,hk,hl,he,hc⟩ := d.ms_radical_quotient_data h ext hTV e hcase
  let := he
  have hm : q (inclusion le_sup_left (⟨a,haL⟩ : L)) ∈
      (d.R.subgroupOf (L ⊔ d.R)).map q := mem_map_of_mem q haR
  have hs := elemPow_eq_one_of_isElementaryAbelian (p := 2) _ hm
  rw [hl] at hs
  have hp : (⟨a,haL⟩ : L) ^ 2 ∈ pCore 2 L := by
    apply (QuotientGroup.eq_one_iff _).mp
    apply ext.quotientEquiv.injective
    change ext.quotientEquiv (QuotientGroup.mk' (pCore 2 L) ((⟨a,haL⟩ : L) ^ 2)) =
      ext.quotientEquiv 1
    simpa only [map_pow,map_one] using hs
  exact mem_map_of_mem L.subtype hp

/-- Each nontrivial radical actor has exactly the original plane as its displacement space. -/
theorem ms_component_actor_plane
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (ext : SLThreeExtension D)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hne : fixedSubgroup L V ≠ ⊥)
    (e : (L ⧸ pCore 2 L) ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2))
    (hcase : FixedMSAlternative L d.R T e)
    (a : G) (haL : a ∈ L) (haR : a ∈ d.R) (haP : a ∉ L.pCoreIn 2) :
    (∀ v ∈ V, ⁅a,v⁆ ∈ d.E) ∧ d.E ≤ ⁅zpowers a,V⁆ := by
  let _ := D.elementary
  let b := ext.quotientEquiv (QuotientGroup.mk' (pCore 2 L) ⟨a,haL⟩)
  have hb1 : b ≠ 1 := by
    intro he
    have hp : (⟨a,haL⟩ : L) ∈ pCore 2 L :=
      (QuotientGroup.eq_one_iff _).mp (ext.quotientEquiv.injective (he.trans ext.quotientEquiv.map_one.symm))
    exact haP (mem_map_of_mem L.subtype hp)
  have hb2 : b ^ 2 = 1 := by
    obtain ⟨x,hx,he⟩ := d.ms_component_radical_square h ext hTV e hcase a haL haR
    have hex : x = (⟨a,haL⟩ : L) ^ 2 := Subtype.ext he
    have hx' : (⟨a,haL⟩ : L) ^ 2 ∈ pCore 2 L := hex ▸ hx
    change (ext.quotientEquiv (QuotientGroup.mk' (pCore 2 L) ⟨a,haL⟩)) ^ 2 = 1
    have hqx : QuotientGroup.mk' (pCore 2 L) ((⟨a,haL⟩ : L) ^ 2) = 1 :=
      (QuotientGroup.eq_one_iff _).mpr hx'
    rw [← map_pow,← map_pow,hqx,map_one]
  have hb : orderOf b = 2 := orderOf_eq_prime hb2 hb1
  obtain ⟨hdis,hdim⟩ := SLThreeCommutatorSource.involution_linear_plane ext hne b hb
  have hact (v : Additive V) :
      ((ext.action b v).toMul : G) = a * (v.toMul : G) * a⁻¹ :=
    ext.conjugation ⟨a,haL⟩ v
  have hfixed (v : Additive V) :
      v ∈ BinaryOffender.fixedSpace ext.action (zpowers b) ↔
      (v.toMul : G) ∈ centralizer ({a} : Set G) := by
    rw [BinaryOffender.mem_fixedSpace_zpowers_iff,mem_centralizer_singleton_iff]
    constructor
    · intro hv
      have hh := hact v
      rw [hv] at hh
      exact (mul_inv_eq_iff_eq_mul.mp hh.symm).symm
    · intro hv
      apply Additive.toMul.injective
      apply Subtype.ext
      rw [hact,hv.symm,mul_inv_cancel_right]
  let C := V ⊓ centralizer ({a} : Set G)
  have hEC : d.E ≤ C := by
    intro w hw
    exact ⟨d.le_module hw,mem_centralizer_singleton_iff.mpr (haR.2 w hw)⟩
  have hCc : Nat.card C = 4 := by
    let f : C ≃ BinaryOffender.fixedSpace ext.action (zpowers b) := {
      toFun := fun v => ⟨Additive.ofMul ⟨v,v.property.1⟩,(hfixed _).mpr v.property.2⟩
      invFun := fun v => ⟨v.val.toMul,v.val.toMul.property,(hfixed _).mp v.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
    rw [Nat.card_congr f,Module.natCard_eq_pow_finrank (K := ZMod 2),
      Nat.card_zmod,hdim]
    norm_num
  have hCE : C = d.E := (eq_of_le_of_card_ge hEC (by rw [hCc,d.card_plane])).symm
  constructor
  · intro v hv
    let w : Additive V := ext.action b (Additive.ofMul ⟨v,hv⟩) - Additive.ofMul ⟨v,hv⟩
    have hw : w ∈ BinaryOffender.fixedSpace ext.action (zpowers b) := by
      rw [← hdis]
      exact ⟨Additive.ofMul ⟨v,hv⟩,rfl⟩
    have he : (w.toMul : G) = ⁅a,v⁆ := by
      change ((ext.action b (Additive.ofMul ⟨v,hv⟩)).toMul : G) / v = _
      rw [hact,div_eq_mul_inv]
      rfl
    rw [← hCE,← he]
    exact ⟨w.toMul.property,(hfixed w).mp hw⟩
  · intro v hv
    have hcv : v ∈ C := hCE.symm ▸ hv
    let w : Additive V := Additive.ofMul ⟨v,hcv.1⟩
    have hw : w ∈ LinearMap.range (ext.action b - LinearMap.id) :=
      hdis ▸ (hfixed w).mpr hcv.2
    obtain ⟨x,hx⟩ := hw
    have he := congrArg (fun y : Additive V => (y.toMul : G)) hx
    change ((ext.action b x).toMul : G) / (x.toMul : G) = v at he
    rw [hact,div_eq_mul_inv] at he
    exact he ▸ commutator_mem_commutator (mem_zpowers a) x.toMul.property

/-- The actual component-radical commutator on V is E. -/
theorem ms_component_radical_commutator_plane
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (ext : SLThreeExtension D)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hne : fixedSubgroup L V ≠ ⊥)
    (e : (L ⧸ pCore 2 L) ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2))
    (hcase : FixedMSAlternative L d.R T e) (hQ : msQ L d.R = V) :
    ⁅L ⊓ d.R,V⁆ = d.E := by
  let := d.ms_core_commutative h ext e hcase hQ
  apply le_antisymm
  · apply commutator_le.mpr
    intro a ha v hv
    by_cases hp : a ∈ L.pCoreIn 2
    · rw [commutatorElement_eq_one_iff_mul_comm.mpr
        (((L.pCoreIn 2).le_centralizer hp) v (D.le_componentCore hv)).symm]
      exact d.E.one_mem
    · exact (d.ms_component_actor_plane h ext hTV hne e hcase a ha.1 ha.2 hp).1 v hv
  · have hn : ¬ L ⊓ d.R ≤ L.pCoreIn 2 := by
      intro hh
      have hi := relIndex_eq_one.mpr hh
      rw [d.ms_component_radical_index h ext hTV e hcase] at hi
      omega
    obtain ⟨a,ha,hp⟩ := Set.not_subset.mp hn
    exact (d.ms_component_actor_plane h ext hTV hne e hcase a ha.1 ha.2 hp).2.trans
      (commutator_mono (zpowers_le.mpr ha) le_rfl)

/-- Escape through MS3 forbids V from lying in the derived subgroup of R. -/
theorem ms_module_not_le_radical_commutator
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (ext : SLThreeExtension D)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hne : fixedSubgroup L V ≠ ⊥)
    (hescape : ¬ normalizer (d.R : Set G) ≤ normalizer (L : Set G))
    (e : (L ⧸ pCore 2 L) ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2))
    (hcase : FixedMSAlternative L d.R T e) (hQ : msQ L d.R = V) :
    ¬ V ≤ ⁅d.R,d.R⁆ := by
  intro hVF
  have hFL : ⁅L,⁅d.R,d.R⁆⁆ ≤ ⁅d.R,d.R⁆ := by
    have hFQ := d.ms_radical_commutator_le_core h ext hTV e hcase
    have hh : ⁅(T : Subgroup G) ⊓ centralizer (V : Set G),L⁆ = V := by
      rw [← d.ms_core_eq ext h hTV]
      exact hQ
    rw [commutator_comm] at hh
    exact ((commutator_mono le_rfl hFQ).trans hh.le).trans hVF
  have hnorm : L ⊔ d.R ≤ normalizer ((⁅d.R,d.R⁆ : Subgroup G) : Set G) := sup_le
    (le_normalizer_iff_commutator_le_right.mpr hFL)
    (by
      rw [← d.R.map_subtype_commutator]
      exact d.R.le_normalizer.trans
        (normalizer_le_normalizer_characteristic_image d.R (_root_.commutator d.R)))
  have hf := d.ms_characteristic h structural hescape (_root_.commutator d.R)
    inferInstance (by
      rw [d.R.map_subtype_commutator]
      exact normal_subgroupOf_of_le_normalizer hnorm)
  have hbot : ⁅d.R,d.R⁆ = ⊥ := by rw [← d.R.map_subtype_commutator,hf,Subgroup.map_bot]
  have hVbot : V = ⊥ := le_bot_iff.mp (hbot ▸ hVF)
  exact hne (le_bot_iff.mp (inf_le_left.trans hVbot.le))

/-- The literal U(L) = V transport of the perfect-cover involutory-lift obstruction. -/
theorem ms_core_eq_module_of_square_mem
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (e : (L ⧸ pCore 2 L) ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2))
    (hQ : msQ L d.R = V)
    (x : G) (hxL : x ∈ L) (hxP : x ∉ L.pCoreIn 2) (hs : x ^ 2 ∈ V) :
    L.pCoreIn 2 = V := by
  let : Group.IsPerfect L := Chapter1.mem_L_isPerfect h.maximal_faithful.1.1
  have hx : (⟨x,hxL⟩ : L) ∉ pCore 2 L := fun hx =>
    hxP (mem_map_of_mem L.subtype hx)
  have hs' : (⟨x,hxL⟩ : L) ^ 2 ∈ blockU L := by
    have hh : x ^ 2 ∈ (blockU L).map L.subtype := (d.ms_blockU_eq hQ).symm ▸ hs
    obtain ⟨y, hy, he⟩ := hh
    have he' : y = (⟨x,hxL⟩ : L) ^ 2 := Subtype.ext he
    exact he' ▸ hy
  rw [pCoreIn, linearThree_core_eq_blockU_of_square_mem e _ hx hs', d.ms_blockU_eq hQ]

/-- The original component core centralizes C_T(V), including the order-four fixed-core branch. -/
theorem ms_core_centralization
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (marked : SLThreeAlternative1222.{u} KnownSimple.IsKnownSimple)
    (hmodel : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2)
    (hne : fixedSubgroup L V ≠ ⊥)
    (hescape : ¬ normalizer (d.R : Set G) ≤ normalizer (L : Set G))
    (e : (L ⧸ pCore 2 L) ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2))
    (hcase : FixedMSAlternative L d.R T e) (hQ : msQ L d.R = V) :
    L.pCoreIn 2 ≤ centralizer
      (((T : Subgroup G) ⊓ centralizer (V : Set G) : Subgroup G) : Set G) := by
  obtain ⟨ext⟩ := marked G T L V h D hmodel hne
  have hTV := ((structural G T L h).2.2 V D).1
  let _ := D.elementary
  let P := L.pCoreIn 2
  let Q := (T : Subgroup G) ⊓ centralizer (V : Set G)
  let A := L ⊓ d.R
  have hQR : Q ≤ d.R := inf_le_inf_left _ (centralizer_le d.le_module)
  have hVR : V ≤ d.R := le_inf D.le_sylow
    (V.le_centralizer.trans (centralizer_le d.le_module))
  have hcomm : ⁅L,Q⁆ = V := by
    change ⁅L,(T : Subgroup G) ⊓ centralizer (V : Set G)⁆ = V
    rw [commutator_comm,← d.ms_core_eq ext h hTV]
    exact hQ
  have hplane : ⁅A,V⁆ = d.E :=
    d.ms_component_radical_commutator_plane h ext hTV hne e hcase hQ
  have hEF : d.E ≤ ⁅d.R,d.R⁆ := by
    rw [← hplane]
    exact commutator_mono inf_le_right hVR
  have hFE := d.fixed_le_plane h structural marked hmodel hne hescape
  have hkernel := d.ms_kernel_commutator_le_fixed h ext hTV hQ
  apply le_centralizer_iff.mp
  intro q hq
  by_contra hn
  have hPq : ¬ P ≤ centralizer ({q} : Set G) := by
    intro hc
    apply hn
    intro p hp
    exact mem_centralizer_singleton_iff.mp (hc hp)
  have hVq : V ≤ centralizer ({q} : Set G) := by
    intro v hv
    exact mem_centralizer_singleton_iff.mpr (hq.2 v hv)
  have hc : P ⊓ centralizer ({q} : Set G) = V :=
    centralizer_inter_eq_of_card_le_twice P V D.le_componentCore q hVq hPq
      (by rw [module_card_sixteen ext hne]; exact d.ms_core_card_le_thirtyTwo h ext hne e hQ)
  have hker : ∀ a ∈ A, ⁅a,q⁆ ∈ d.E ↔ a ∈ P := by
    intro a ha
    constructor
    · intro hdelta
      by_contra haP
      have hs : a ^ 2 ∈ P := d.ms_component_radical_square h ext hTV e hcase a ha.1 ha.2
      have hsn : a ^ 2 ∉ V := by
        intro hsv
        have he := d.ms_core_eq_module_of_square_mem h e hQ a ha.1 haP hsv
        apply hPq
        change L.pCoreIn 2 ≤ _
        rw [he]
        exact hVq
      have hh : ⁅a ^ 2,q⁆ = 1 := by
        rw [pow_two,commutatorElement_mul_left_eq_conj_mul,
          (ha.2.2 _ hdelta).symm,mul_inv_cancel_right,← pow_two]
        exact elemPow_eq_one_of_isElementaryAbelian _ (d.le_module hdelta)
      have hm : a ^ 2 ∈ P ⊓ centralizer ({q} : Set G) :=
        ⟨hs,mem_centralizer_singleton_iff.mpr (commutatorElement_eq_one_iff_mul_comm.mp hh)⟩
      exact hsn (hc ▸ hm)
    · intro haP
      exact hFE (hkernel (commutator_mem_commutator haP hq))
  have hVF : V ≤ ⁅d.R,d.R⁆ := le_self_commutator_of_four_plane_displacement
    A P V d.E d.R hplane.le d.le_module hEF inf_le_right
    (module_card_sixteen ext hne) d.card_plane
    (d.ms_component_radical_index h ext hTV e hcase) q (hQR hq)
    (fun a ha => hcomm ▸ commutator_mem_commutator ha.1 hq) hker
  exact d.ms_module_not_le_radical_commutator h ext structural hTV hne hescape e hcase hQ hVF

/-- The first original fixed-line MS product, with its kernel premise discharged. -/
theorem ms_core_product
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (marked : SLThreeAlternative1222.{u} KnownSimple.IsKnownSimple)
    (hmodel : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2)
    (hne : fixedSubgroup L V ≠ ⊥)
    (hescape : ¬ normalizer (d.R : Set G) ≤ normalizer (L : Set G))
    (e : (L ⧸ pCore 2 L) ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2))
    (hcase : FixedMSAlternative L d.R T e) (hQ : msQ L d.R = V) :
    (T : Subgroup G) ⊓ centralizer (V : Set G) =
      V ⊔ ((T : Subgroup G) ⊓ centralizer (L : Set G)) := by
  obtain ⟨ext⟩ := marked G T L V h D hmodel hne
  exact d.ms_core_product_of_core_centralization h ext
    ((structural G T L h).2.2 V D).1 hne hQ
    (d.ms_core_centralization h structural marked hmodel hne hescape e hcase hQ)

end LocalGeometry
end CFSG.Quasithin.Chapter12.Section04.SmallFusion.SLThreeSource
