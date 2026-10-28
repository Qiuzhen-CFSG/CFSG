module
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.Constrained.Catalogue.SixApplications
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.ExceptionalRestrictions.Ahat6Centralizer
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.AutomorphismAction.CentralSylow
public import Theory.GroupTheory.TwoLocalCharacteristicControl
public import Theory.GroupAction.NormalizerGeneratingFixer

/-!
# Detecting the cubic center from the original A₆ seed

For an exceptional triple-cover block in the full original local family,
a central involution of T induces conjugation by a unique nonzero vector
of U(K). The vector is fixed by N_S(K), and its point centralizer lies in
the literal M_Z intersection. The proof uses Sylow cocycle averaging and
the absence of fixed vectors for the central cubic action.

This vector detects the entire central kernel of the actual FF map. Thus
K/O₂(K) maps isomorphically onto the original normalizer image, whose center
has order three. In particular, an ordinary A₆ FF image cannot reconstruct
as an exceptional block. With the independently owned whole-core
reconstruction, the ordinary image gives the complete six-block alternative.
The catalogue remainder keeps the cubic block, its C.2.7 input, MS pair,
and compatible original quotient markings. The exceptional parabolic offender
exclusion is still required; center detection alone does not exclude that row.

Original-marker applications retain both source primes and the earlier
15.1.14 residual premise. The later exchanged application uses the same maps.
AlternatingSixReconstructionInput remains explicit for its existing producer
qt-e-ms-small-a6-reconstruction and must be discharged in final assembly.

Source: Aschbacher--Smith 15.1.20(2b), 15.1.22(2), printed pp.1094--1100;
C.2.7(2--3), printed p.146.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
open scoped IsMulCommutative
open CFSG.Quasithin ChapterC
namespace CFSG.Quasithin.Chapter15.Section01.CaseIComponentData
open Section03 Section03.InitialSource ChapterA.Section05To06
universe u
variable {G : Type u} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V : Subgroup G}

private theorem short_sylow_fixer
    {K : Type*} [Group K] [Finite K] (hs : IsShort K)
    (P : Sylow 2 K) (a : MulAut K) (hf : ∀ x ∈ P, a x = x) :
    ∃ u : blockU K, ∀ x, a x = (u : K)⁻¹ * x * u := by
  let U := blockU K
  let := hs.elementary
  have hdcore (x : K) : a x * x⁻¹ ∈ pCore 2 K := by
    have hh := hs.centralizer_blockU.le
      (Theory.GroupAction.NormalizerGeneratingFixer.displacement_mem_centralizer U a
        (fun y hy => hf y (pCore_isPGroup.le_sylow_of_normal P (blockU_le_core hy)))
        x⁻¹ (by rw [normalizer_eq_top]; trivial))
    simpa only [inv_inv,map_inv,mul_inv_rev] using (pCore 2 K).inv_mem hh
  have hd (x : K) : a x * x⁻¹ ∈ U := by
    have he := DFunLike.congr_fun (hs.quotient_blockU_aut_eq_one a hdcore)
      (QuotientGroup.mk' U x)
    rw [quotientAut_apply_mk] at he
    simpa only [div_eq_mul_inv] using QuotientGroup.eq_iff_div_mem.mp he
  let c (x : K) : U := ⟨a x * x⁻¹,hd x⟩
  let ρ : K →* MulAut U := MulAut.conjNormal
  have hc (x y : K) : c (x*y) = c x * ρ x (c y) := by
    apply Subtype.ext
    change a (x*y)*(x*y)⁻¹ = (a x*x⁻¹)*(x*(a y*y⁻¹)*x⁻¹)
    simp only [map_mul,mul_inv_rev]
    group
  obtain ⟨u,hu⟩ := binary_cocycle_trivial_of_sylow ρ c hc
    (fun u => Subtype.ext (elemPow_eq_one_of_isElementaryAbelian (u : K) u.property)) P
    (fun x hx => Subtype.ext (by change a x*x⁻¹=1; rw [hf x hx,mul_inv_cancel]))
  refine ⟨u⁻¹,?_⟩
  intro x
  simp only [Subgroup.coe_inv,inv_inv]
  have hh := congrArg Subtype.val (hu x)
  change (x*(u : K)*x⁻¹)*(a x*x⁻¹) = (u : K) at hh
  have he : a x*x⁻¹ = (x*(u : K)*x⁻¹)⁻¹*(u : K) :=
    eq_inv_mul_iff_mul_eq.mpr hh
  calc
    a x = (a x*x⁻¹)*x := by group
    _ = ((x*(u : K)*x⁻¹)⁻¹*(u : K))*x := by rw [he]
    _ = (u : K)*x*(u : K)⁻¹ := by
      have hcomm : (x*(u : K)*x⁻¹)⁻¹*(u : K) = (u : K)*(x*(u : K)*x⁻¹)⁻¹ :=
        congrArg Subtype.val (mul_comm' (ρ x u)⁻¹ u)
      rw [hcomm]
      group

omit [Finite G] in
private theorem exceptional_six_fixed_trivial {K : Subgroup G} (hb : IsExceptionalAhat6Block K)
    {u : G} (hu : u ∈ (blockU K).map K.subtype)
    (hc : u ∈ centralizer (K : Set G)) : u = 1 := by
  obtain ⟨v,hv,rfl⟩ := hu
  have he := hb.fixed_coreCenter_eq_one (⟨v,hv⟩ : blockU K) (by
    intro k _
    exact Subtype.ext (hc k k.property))
  exact congrArg (fun x : blockU K => ((x : K) : G)) he

/-- A genuine nonzero fixed vector of the exceptional block, extracted from
an original central involution. Its point centralizer is contained in M_Z. -/
theorem localFamily_exceptionalSix_point (d : CaseIComponentData T M Mc V)
    (h : PreparedChosenModule T M V) (hTM : (T : Subgroup G) ≤ M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    {K : Subgroup G} (hK : K ∈ Chapter1.LIn d.G1 d.S)
    (hq : IsQuasisimple (K ⧸ pCore 2 K)) (hout : ¬ K ≤ d.MZ)
    (hb : IsExceptionalAhat6Block K) :
    ∃ z ∈ centralInvolutions T, z ≠ 1 ∧
      ∃ u : blockU K, u ≠ 1 ∧
        ((u : K) : G) * z ∈ centralizer (K : Set G) ∧
        ((u : K) : G) ∈ centralizer (d.normalizerSylow K : Set G) ∧
        K ⊓ centralizer ({((u : K) : G)} : Set G) ≤ d.MZ ⊓ K := by
  let U := (blockU K).map K.subtype
  obtain ⟨P,hP⟩ := ComponentModels.source20_sylow_intersection hK.2
  obtain ⟨_,_,hZR⟩ := d.localFamily_normalizer_setup h hTM hu hK hq hout hb.1.fitting
  have hMc : centralizer (centralInvolutions T : Set G) ≤ Mc :=
    (show Mc ∈ maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) from
      hu ▸ Set.mem_singleton Mc).2
  have hn : ¬ centralInvolutions T ≤ centralizer (K : Set G) := by
    intro hc
    exact hout (le_inf hK.1 ((le_centralizer_iff.mp hc).trans hMc))
  obtain ⟨z,hz,hzc⟩ := SetLike.not_le_iff_exists.mp hn
  have hz1 : z ≠ 1 := fun he => hzc (he ▸ one_mem _)
  have hzN : z ∈ normalizer (K : Set G) := (hZR hz).2
  let α := K.normalizerMonoidHom ⟨z,hzN⟩
  obtain ⟨u,huf⟩ := short_sylow_fixer hb.1 P α (by
    intro x hx
    apply Subtype.ext
    change z * (x : G) * z⁻¹ = (x : G)
    rw [←centralInvolutions_le_centralizer_sylow T hz x
      (d.S_le_T ((hP ▸ mem_map_of_mem K.subtype hx).1)),mul_inv_cancel_right])
  have huc : ((u : K) : G) * z ∈ centralizer (K : Set G) := by
    intro k hk
    have he := congrArg (fun x : K => (x : G)) (huf ⟨k,hk⟩)
    change z*k*z⁻¹ = ((u : K) : G)⁻¹*k*u at he
    calc
      k * (((u : K) : G)*z) = u * (((u : K) : G)⁻¹*k*u) * z := by group
      _ = u * (z*k*z⁻¹) * z := by rw [←he]
      _ = (((u : K) : G)*z)*k := by group
  have huU : ((u : K) : G) ∈ U := mem_map_of_mem K.subtype u.property
  have hu1 : u ≠ 1 := by
    intro he
    apply hzc
    simpa only [he,OneMemClass.coe_one,one_mul] using huc
  have huR : ((u : K) : G) ∈ centralizer (d.normalizerSylow K : Set G) := by
    intro r hr
    have hrN := hr.2
    have hrU : r ∈ normalizer (U : Set G) :=
      normalizer_le_normalizer_characteristic_image K (blockU K) hrN
    have hrz : r*z*r⁻¹ = z := by
      rw [centralInvolutions_le_centralizer_sylow T hz r (d.S_le_T hr.1),mul_inv_cancel_right]
    have hu' : r * ((u : K) : G) * r⁻¹ ∈ U :=
      (mem_normalizer_iff.mp hrU _).mp huU
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
    have hone := exceptional_six_fixed_trivial hb (U.mul_mem huU (U.inv_mem hu')) hd
    exact mul_inv_eq_iff_eq_mul.mp (mul_inv_eq_one.mp hone).symm
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
  refine ⟨z,hz,hz1,u,hu1,huc,huR,?_⟩
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

/-- The nonzero original fixed vector detects every nonidentity central
actor. Hence even the cubic center survives in the literal FF image. -/
theorem localFamily_exceptionalSix_coreToImage_bijective
    (d : CaseIComponentData T M Mc V)
    (h : PreparedChosenModule T M V) (hTM : (T : Subgroup G) ≤ M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    {K : Subgroup G} (hK : K ∈ Chapter1.LIn d.G1 d.S)
    (hout : ¬ K ≤ d.MZ) (hb : IsExceptionalAhat6Block K)
    (a : d.NormalizerAction K) : Function.Bijective a.coreToImage := by
  obtain ⟨z,hz,_,u,hu1,huc,_,_⟩ :=
    d.localFamily_exceptionalSix_point h hTM hu hK hb.2.1 hout hb
  have hZN := (d.localFamily_normalizer_setup h hTM hu hK hb.2.1 hout hb.1.fitting).2.2
  let H := K ⊔ d.normalizerSylow K
  let := hb.1.elementary
  refine ⟨(MonoidHom.ker_eq_bot_iff _).mp (bot_unique ?_),a.coreToImage_surjective⟩
  intro x hx
  by_contra hx1
  have hxne : x ≠ 1 := hx1
  have hxZ := a.coreToImage_ker_central hb.2.1 hx
  obtain ⟨k,hk⟩ := QuotientGroup.mk'_surjective (pCore 2 K) x
  have hki : d.toNormalizerImage K k = 1 := by
    rw [←a.coreToImage_mk,hk]
    exact hx
  have hkC : inclusion (show K ≤ H from le_sup_left) k ∈
      centralizer (d.normalizerModule K : Set H) :=
    (QuotientGroup.eq_one_iff _).mp (congrArg Subtype.val hki)
  have hkz : z * (k : G) = (k : G) * z :=
    congrArg Subtype.val (hkC ⟨z,mem_sup_right (hZN hz)⟩ (le_normalClosure hz))
  have hku : (k : G) * ((u : K) : G) = ((u : K) : G) * k := by
    apply mul_right_cancel (b := z)
    calc
      ((k : G) * ((u : K) : G)) * z = (k : G) * (((u : K) : G) * z) := mul_assoc _ _ _
      _ = (((u : K) : G) * z) * k := huc k k.property
      _ = (((u : K) : G) * k) * z := by rw [mul_assoc,hkz,←mul_assoc]
  let ρ := ExceptionalRestrictions.uRepresentation hb.1
  let v : Additive (blockU K) := Additive.ofMul u
  have hfix : ρ x v = v := by
    rw [←hk]
    apply Additive.toMul.injective
    apply Subtype.ext
    rw [ExceptionalRestrictions.uRepresentation_apply]
    apply Subtype.ext
    change (k : G) * ((u : K) : G) * (k : G)⁻¹ = ((u : K) : G)
    rw [hku,mul_inv_cancel_right]
  have hglobal := ExceptionalRestrictions.central_fixed_is_global hb x hxZ hxne v hfix
  have huC : (u : K) ∈ centralizer (Subgroup.upperCentralSeriesStep (pCore 2 K) : Set K) := by
    intro l _
    have hh := hglobal ⟨QuotientGroup.mk' (pCore 2 K) l,mem_top _⟩
    have he := congrArg (fun w : Additive (blockU K) => (w.toMul : K)) hh
    change ((ExceptionalRestrictions.uRepresentation hb.1
      (QuotientGroup.mk' (pCore 2 K) l) v).toMul : K) = (u : K) at he
    rw [ExceptionalRestrictions.uRepresentation_apply] at he
    exact mul_inv_eq_iff_eq_mul.mp he
  exact hu1 (hb.fixed_coreCenter_eq_one u huC)

/-- The actual exceptional block has the full cubic FF marking, including
its center of order three and its original A₆ central quotient. -/
theorem localFamily_exceptionalSix_marking
    (d : CaseIComponentData T M Mc V)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (h : PreparedChosenModule T M V)
    {K : Subgroup G} (hK : K ∈ Chapter1.LIn d.G1 d.S)
    (hout : ¬ K ≤ d.MZ) (hb : IsExceptionalAhat6Block K) :
    ∃ t : (K ⧸ pCore 2 K) ≃* d.normalizerImage K,
      (∀ k : K, t (QuotientGroup.mk' (pCore 2 K) k) = d.toNormalizerImage K k) ∧
      Nat.card (center (d.normalizerImage K)) = 3 ∧
      Nonempty ((d.normalizerImage K ⧸ center (d.normalizerImage K)) ≃*
        alternatingGroup (Fin 6)) := by
  have a := d.localFamily_normalizerAction hG hempty hM hJ hu h hK hb.2.1 hout hb.1.fitting
  let t := MulEquiv.ofBijective a.coreToImage
    (d.localFamily_exceptionalSix_coreToImage_bijective h hM.1.2 hu hK hout hb a)
  obtain ⟨e⟩ := hb.2.2.2.1
  refine ⟨t,fun _ => rfl,?_,?_⟩
  · rw [←Nat.card_congr (centerCongr t).toEquiv]
    exact hb.2.2.1
  · exact ⟨(QuotientGroup.congr _ _ t (Theory.GroupTheory.FixedElementary.map_center t)).symm.trans e⟩

/-- In particular an actual exceptional block cannot have the ordinary A₆
FF image. Its central covering kernel cannot be silently discarded. -/
theorem localFamily_not_exceptionalSix_of_six_image
    (d : CaseIComponentData T M Mc V)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (h : PreparedChosenModule T M V)
    {K : Subgroup G} (hK : K ∈ Chapter1.LIn d.G1 d.S)
    (hout : ¬ K ≤ d.MZ)
    (e : d.normalizerImage K ≃* alternatingGroup (Fin 6)) :
    ¬ IsExceptionalAhat6Block K := by
  intro hb
  obtain ⟨_,_,hc,_⟩ := d.localFamily_exceptionalSix_marking hG hempty hM hJ hu h hK hout hb
  rw [Nat.card_congr (centerCongr e).toEquiv,alternatingGroup.center_eq_bot (by simp),card_bot] at hc
  contradiction

open Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS

/-- The ordinary A₆ FF row cannot reconstruct as the exceptional triple
cover: the original central seed detects that cover's center. -/
theorem PreExclusionSource.constrained_six_block_of_reconstruction
    {d : CaseIComponentData T M Mc V} {h : PreparedChosenModule T M V} {p : ℕ}
    (s : d.PreExclusionSource h.normalized p)
    (ha : AlternatingSixReconstructionInput.{u} KnownSimple.IsKnownSimple)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hf : generalizedFitting d.L = pCore 2 d.L)
    (e : d.normalizerImage d.L ≃* alternatingGroup (Fin 6)) :
    IsAlternatingBlock d.L 6 := by
  let ec := (QuotientGroup.congr _ _ e (Theory.GroupTheory.FixedElementary.map_center e)).trans
    ((QuotientGroup.quotientMulEquivOfEq (alternatingGroup.center_eq_bot (by simp : 4 ≤ Nat.card (Fin 6)))).trans
      QuotientGroup.quotientBot)
  exact (s.constrained_six_blocks_of_reconstruction (h := h) ha hG hempty hM hJ hu hf ec).resolve_right
    (d.localFamily_not_exceptionalSix_of_six_image hG hempty hM hJ hu h
      ⟨d.L_component.1,s.local_component⟩ d.L_not_le_MZ e)

/-- The original ordinary FF row supplies the complete six-block catalogue
alternative after the independent whole-core reconstruction. -/
theorem PreExclusionSource.constrained_six_of_image_reconstruction
    {d : CaseIComponentData T M Mc V} {h : PreparedChosenModule T M V} {p : ℕ}
    (s : d.PreExclusionSource h.normalized p)
    (ha : AlternatingSixReconstructionInput.{u} KnownSimple.IsKnownSimple)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hfull : V = localModule T M)
    (hf : generalizedFitting d.L = pCore 2 d.L)
    (e : d.normalizerImage d.L ≃* alternatingGroup (Fin 6)) :
    IsAlternatingBlock d.L 6 ∧
      (∃ t : (d.L ⧸ pCore 2 d.L) ≃* alternatingGroup (Fin 6),
        ∀ k : d.L, t (QuotientGroup.mk' (pCore 2 d.L) k) = e (d.toNormalizerImage d.L k)) ∧
      d.ConstrainedAlternatives := by
  have hb := s.constrained_six_block_of_reconstruction (h := h) ha hG hempty hM hJ hu hf e
  obtain ⟨t,ht⟩ := s.constrained_six_core_marking (h := h) hG hempty hM hJ hu hb e
  obtain ⟨_,_,_,_,_,_,_,_,_,_,halt⟩ := s.constrained_six_of_block (h := h)
    hG hempty hM hJ hu hfull hb
  exact ⟨hb,⟨t,ht⟩,halt⟩

/-- The same literal cubic-center detection after exchanged selection. -/
theorem ExchangedSource.constrained_exceptionalSix_marking
    {d : CaseIComponentData T M Mc V} (s : d.ExchangedSource)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (h : PreparedChosenModule T M V) (hb : IsExceptionalAhat6Block d.L) :
    ∃ t : (d.L ⧸ pCore 2 d.L) ≃* d.normalizerImage d.L,
      (∀ k : d.L, t (QuotientGroup.mk' (pCore 2 d.L) k) = d.toNormalizerImage d.L k) ∧
      Nat.card (center (d.normalizerImage d.L)) = 3 ∧
      Nonempty ((d.normalizerImage d.L ⧸ center (d.normalizerImage d.L)) ≃*
        alternatingGroup (Fin 6)) :=
  d.localFamily_exceptionalSix_marking hG hempty hM hJ hu h
    ⟨d.L_component.1,s.local_component⟩ d.L_not_le_MZ hb

/-- The ordinary FF image is excluded after exchanged selection, using the
same original component and the independent whole-core reconstruction. -/
theorem ExchangedSource.not_constrained_six_image_of_reconstruction
    {d : CaseIComponentData T M Mc V} {h : PreparedChosenModule T M V} {p : ℕ}
    (x : d.ExchangedSource) (s : d.PreExclusionSource h.normalized p)
    (ha : AlternatingSixReconstructionInput.{u} KnownSimple.IsKnownSimple)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hfull : V = localModule T M)
    (hf : generalizedFitting d.L = pCore 2 d.L) :
    IsEmpty (d.normalizerImage d.L ≃* alternatingGroup (Fin 6)) := by
  refine ⟨fun e => ?_⟩
  exact x.not_constrained_six_block_of_preExclusion (h := h) s hG hempty hM hJ hu hfull
    (s.constrained_six_block_of_reconstruction (h := h) ha hG hempty hM hJ hu hf e)

open ChapterC.C27Source
open Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface

/-- The remaining exceptional row retains the whole two-core quotient in
the literal FF image, in addition to the original central-quotient marking. -/
theorem PreExclusionSource.constrained_catalogue_or_marked_cubic_six_of_reconstruction
    {d : CaseIComponentData T M Mc V} {h : PreparedChosenModule T M V} {p : ℕ}
    (s : d.PreExclusionSource h.normalized p)
    (ha : AlternatingSixReconstructionInput.{u} KnownSimple.IsKnownSimple)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hne : M ≠ Mc)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hfull : V = localModule T M)
    (hres : (pResidual 2 (centralizer (centralInvolutions T : Set G))).map
      (centralizer (centralInvolutions T : Set G)).subtype ≤
        centralizer (thompsonFixed T V : Set G))
    (hf : generalizedFitting d.L = pCore 2 d.L) :
    d.ConstrainedAlternatives ∨
      (IsExceptionalAhat6Block d.L ∧
        Input KnownSimple.IsKnownSimple d.G1 d.Q1 d.MZ d.L ∧
        SmallMSPair KnownSimple.IsKnownSimple d.L d.Q1 ∧
        ∃ q : (d.L ⧸ pCore 2 d.L) ≃* d.normalizerImage d.L,
          (∀ k : d.L, q (QuotientGroup.mk' (pCore 2 d.L) k) = d.toNormalizerImage d.L k) ∧
          Nat.card (center (d.normalizerImage d.L)) = 3 ∧
          ∃ e : (d.normalizerImage d.L ⧸ center (d.normalizerImage d.L)) ≃* alternatingGroup (Fin 6),
            ∃ t : (d.L ⧸ centralPreimage (pCore 2 d.L)) ≃* alternatingGroup (Fin 6),
              ∀ k : d.L, t (QuotientGroup.mk' (centralPreimage (pCore 2 d.L)) k) =
                e (QuotientGroup.mk' (center (d.normalizerImage d.L)) (d.toNormalizerImage d.L k))) := by
  rcases s.constrained_catalogue_or_exceptional_six_of_reconstruction (h := h)
    ha hG hempty hM hJ hu hne hmany hfull hres hf with hc | ⟨hb,hi,hms,e,t,ht⟩
  · exact Or.inl hc
  · obtain ⟨q,hq,hc,_⟩ := d.localFamily_exceptionalSix_marking hG hempty hM hJ hu h
      ⟨d.L_component.1,s.local_component⟩ d.L_not_le_MZ hb
    exact Or.inr ⟨hb,hi,hms,q,hq,hc,e,t,ht⟩

end CFSG.Quasithin.Chapter15.Section01.CaseIComponentData

namespace CFSG.Quasithin.Chapter15.Section01
open Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
open Section03 Section03.InitialSource ChapterA.Section05To06
open ChapterC.C27Source
universe u
variable {G : Type u} [Group G] [Finite G]

/-- At the original marker, every exceptional member of the full local
family retains its cubic center under the literal FF quotient map. -/
theorem PreparedChosenModule.source_preExclusion_exceptionalSix_marking
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
      ∀ K ∈ Chapter1.LIn d.G1 d.S, ¬ K ≤ d.MZ → IsExceptionalAhat6Block K →
        ∃ t : (K ⧸ pCore 2 K) ≃* d.normalizerImage K,
          (∀ k : K, t (QuotientGroup.mk' (pCore 2 K) k) = d.toNormalizerImage K k) ∧
          Nat.card (center (d.normalizerImage K)) = 3 ∧
          Nonempty ((d.normalizerImage K ⧸ center (d.normalizerImage K)) ≃*
            alternatingGroup (Fin 6)) := by
  obtain ⟨d,hZ,hr,s⟩ := h.component_of_preExclusionMarker
    hG T hempty hM hmany hJ hu hne hfull m hres
  exact ⟨d,hZ,hr,s,fun _ hK hout hb =>
    d.localFamily_exceptionalSix_marking hG hempty hM hJ hu h hK hout hb⟩

/-- The original ordinary A₆ image supplies the whole block and catalogue
alternative, conditional only on the independently owned reconstruction. -/
theorem PreparedChosenModule.source_preExclusion_constrained_six_of_image_reconstruction
    (ha : AlternatingSixReconstructionInput.{u} KnownSimple.IsKnownSimple)
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
        ∀ e : d.normalizerImage d.L ≃* alternatingGroup (Fin 6),
          IsAlternatingBlock d.L 6 ∧
          (∃ t : (d.L ⧸ pCore 2 d.L) ≃* alternatingGroup (Fin 6),
            ∀ k : d.L, t (QuotientGroup.mk' (pCore 2 d.L) k) = e (d.toNormalizerImage d.L k)) ∧
          d.ConstrainedAlternatives) := by
  obtain ⟨d,hZ,hr,s⟩ := h.component_of_preExclusionMarker
    hG T hempty hM hmany hJ hu hne hfull m hres
  exact ⟨d,hZ,hr,s,fun hf e => s.constrained_six_of_image_reconstruction (h := h)
    ha hG hempty hM hJ hu hfull hf e⟩

end CFSG.Quasithin.Chapter15.Section01
