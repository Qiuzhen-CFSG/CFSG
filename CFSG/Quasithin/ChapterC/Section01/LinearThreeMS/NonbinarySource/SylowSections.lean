module
public import CFSG.Quasithin.ChapterC.Section01.LinearThreeMS.NonbinarySource.NaturalBlock
public import Theory.GroupTheory.PResidual.CentralizerCorrection


/-!
# Actual Sylow-omega sections in the nonbinary MS rows

Let Q=[O₂(KR),K] and R≤S∈Syl₂(KR). For the doubled whole core, a
natural Z(Q), or a natural [Z(Q),K], write U for that actual section.
Odd-index averaging corrects every element of Ω₁Z(S) by an S-fixed
vector of U to an element centralizing K. The natural module has no
K-fixed vector, so uniqueness makes the correction S-fixed, even when
Q is nonabelian. Thus Ω₁Z(S) is the direct product of C_U(S) and its
K-fixed subgroup, and

  C_KR(Ω₁Z(S)) = C_K(C_U(S)) R.

All subgroups and the Sylow are the originals. The proof uses neither
upper Frattini-section models nor ambient centrality of C_Q(K). The
whole-section recognition and the inequality between R and the two-core
of this computed centralizer remain separate source obligations.
NonblockMSClassification and PointApplication apply these formulas to
their original configurations.
Source: Aschbacher--Smith C.1.34(2)--(4), printed pp.136--137; original
4.3.8--10, pp.616--617, and 11.1.5, pp.765--766.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.ChapterC.LinearThreeMS.NonbinarySource
open Chapter1.RadicalExclusions.ModelReduction.FullSieve
open SourceInterface
variable {G : Type*} [Group G] [Finite G] {K R : Subgroup G}
variable {n : ℕ} {F : Type} [Field F] [Finite F] [CharP F 2]
variable (h : LinearThreeMSPair KnownSimple.IsKnownSimple K R n F) (hn : 1 < n)

omit [Finite F] [CharP F 2] in
private theorem natural_fixed_zero (v : Fin 3 → F)
    (hv : ∀ g : SL(3,F), specialLinearNatural 3 g v = v) : v = 0 := by
  by_contra hv0
  have ha : (![1,0,0] : Fin 3 → F) ≠ 0 := by
    intro he
    have := congrFun he 0
    simp at this
  have hb : (![0,1,0] : Fin 3 → F) ≠ 0 := by
    intro he
    have := congrFun he 1
    simp at this
  obtain ⟨a,ha'⟩ := Matrix.SpecialLinearGroup.exists_mulVec_eq_three v ![1,0,0] hv0 ha
  obtain ⟨b,hb'⟩ := Matrix.SpecialLinearGroup.exists_mulVec_eq_three v ![0,1,0] hv0 hb
  have he : (![1,0,0] : Fin 3 → F) = ![0,1,0] := (ha'.symm.trans (hv a)).trans ((hv b).symm.trans hb')
  have := congrFun he 0
  simp at this

omit [Finite G] [Finite F] in
private theorem section_properties {W : Type*} [AddCommGroup W] [Module F W]
    (rho : Representation F SL(3,F) W)
    (hf : ∀ v, (∀ g, rho g v = v) → v = 0)
    (e : (K ⧸ pCore 2 K) ≃* SL(3,F)) {U : Subgroup G}
    (hm : HasSectionModel K U ⊥ (linearThreeActor e) rho) :
    IsMulCommutative U ∧ (∀ u ∈ U, u^2 = 1) ∧ U ⊓ centralizer (K : Set G) = ⊥ := by
  rw [HasSectionModel,bot_subgroupOf] at hm
  obtain ⟨_,hKU,_,hbot,a,ha⟩ := hm
  let := hbot
  let c : U ≃* Multiplicative W := QuotientGroup.quotientBot.symm.trans a
  refine ⟨IsMulCommutative.of_comm (fun x y => c.injective (by rw [map_mul,map_mul,mul_comm])),?_,?_⟩
  · intro u hu
    have he : (⟨u,hu⟩ : U)^2 = 1 := by
      apply c.injective
      rw [map_pow,map_one,pow_two]
      apply Multiplicative.toAdd.injective
      change (c ⟨u,hu⟩).toAdd + (c ⟨u,hu⟩).toAdd = 0
      rw [← two_smul F, show (2 : F) = 0 from by simpa using (CharP.cast_eq_zero F 2), zero_smul]
    exact congrArg Subtype.val he
  · apply bot_unique
    rintro u ⟨hu,huc⟩
    have he : (c ⟨u,hu⟩).toAdd = 0 := by
      apply hf
      intro g
      obtain ⟨k,hk⟩ := e.surjective.comp (QuotientGroup.mk'_surjective _) g
      have he := ha k ⟨u,hu⟩ ⟨u,hu⟩ (by
        rw [huc k k.property,mul_inv_cancel_right])
      change (c ⟨u,hu⟩).toAdd = rho (e (QuotientGroup.mk' _ k)) (c ⟨u,hu⟩).toAdd at he
      change e (QuotientGroup.mk' _ k) = g at hk
      rw [hk] at he
      exact he.symm
    exact congrArg Subtype.val (c.map_eq_one_iff.mp (Multiplicative.toAdd.injective he))

include h hn
omit [CharP F 2] in
private theorem sylow_correction {S U : Subgroup G}
    (hS : Chapter1.IsSylowIn 2 S (K ⊔ R))
    (hJU : K ⊔ R ≤ normalizer (U : Set G))
    (hc : IsMulCommutative U) (hexp : ∀ u ∈ U, u^2 = 1)
    (hfix : U ⊓ centralizer (K : Set G) = ⊥)
    (hZU : ⁅SourceInterface.centerIn (msQ K R),K⁆ ≤ U)
    (z : G) (hz : z ∈ SourceInterface.omegaCenterIn S) :
    ∃ u ∈ U ⊓ centralizer (S : Set G), u⁻¹*z ∈ centralizer (K : Set G) := by
  let J := K ⊔ R
  let N := J.pCoreIn 2
  have hSJ : S ≤ J := (Chapter1.isSylowIn_iff.mp hS).2.1
  have hNS : N ≤ S := by
    obtain ⟨P,hP⟩ := hS
    exact hP ▸ pCoreIn_le_sylow J P
  have hJK : J ≤ normalizer (K : Set G) :=
    (normal_subgroupOf_iff_le_normalizer (show K ≤ J from le_sup_left)).mp (component_normal h hn)
  have hKN : K ≤ normalizer (N : Set G) :=
    (le_sup_left : K ≤ J).trans (J.le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image J (pCore 2 J)))
  obtain ⟨P,hP⟩ := hS
  let := component_normal h hn
  obtain ⟨P₀,hP₀⟩ := P.exists_subgroupOf_eq_of_normal (K.subgroupOf J)
  let a : K.subgroupOf J ≃* K := subgroupOfEquivOfLe (show K ≤ J from le_sup_left)
  let PK := P₀.mapSurjective (f := a.toMonoidHom) a.surjective
  have hPK : (PK : Subgroup K).map K.subtype ≤ S := by
    rintro x ⟨k,hk,rfl⟩
    change k ∈ (P₀ : Subgroup (K.subgroupOf J)).map a.toMonoidHom at hk
    obtain ⟨l,hl,rfl⟩ := hk
    rw [hP₀] at hl
    exact hP ▸ mem_map_of_mem J.subtype hl
  obtain ⟨hzS,hzc,hze⟩ := (mem_omegaCenterIn_iff S z).mp hz
  have hzN : z ∈ N := by
    apply mem_map_of_mem J.subtype (x := ⟨z,hSJ hzS⟩)
    apply core_selfCentralizing h
    intro d hd
    exact Subtype.ext (hzc d (hNS (mem_map_of_mem J.subtype hd)))
  let := hc
  obtain ⟨u,hu,huc⟩ := fixed_correction_of_center_commutator K N U
    (component_twoPerfect h hn) (pCore_isPGroup.map J.subtype) hKN
    ((le_sup_left : K ≤ J).trans hJU) hexp hZU PK z hzN
    (centralizer_le (msQ_le_joinCore.trans hNS) hzc) (centralizer_le hPK hzc)
  refine ⟨u,⟨hu.1,?_⟩,huc⟩
  intro s hs
  let u' := s*u*s⁻¹
  let b := u⁻¹*z
  let b' := s*b*s⁻¹
  have hu' : u' ∈ U := (hJU (hSJ hs) u).mp hu.1
  have hb' : b' ∈ centralizer (K : Set G) :=
    ((normalizer_le_normalizer_centralizer K (hJK (hSJ hs))) b).mp huc
  have hp : u'*b' = u*b := by
    calc
      u'*b' = s*(u*b)*s⁻¹ := by dsimp [u',b']; group
      _ = s*z*s⁻¹ := by simp only [b,mul_inv_cancel_left]
      _ = z := by rw [hzc s hs,mul_inv_cancel_right]
      _ = u*b := (mul_inv_cancel_left u z).symm
  have hd : u⁻¹*u' = b*b'⁻¹ := by
    calc
      u⁻¹*u' = u⁻¹*(u'*b')*b'⁻¹ := by group
      _ = u⁻¹*(u*b)*b'⁻¹ := by rw [hp]
      _ = b*b'⁻¹ := by group
  have he : u⁻¹*u' = 1 := by
    apply hfix.le
    refine ⟨U.mul_mem (U.inv_mem hu.1) hu',?_⟩
    rw [hd]
    exact (centralizer _).mul_mem huc ((centralizer _).inv_mem hb')
  exact mul_inv_eq_iff_eq_mul.mp ((inv_mul_eq_one.mp he).symm : u' = u)


omit [CharP F 2] in
private theorem section_sylow_geometry {S U : Subgroup G}
    (hS : Chapter1.IsSylowIn 2 S (K ⊔ R)) (hRS : R ≤ S)
    (hUQ : U ≤ msQ K R) (hJU : K ⊔ R ≤ normalizer (U : Set G))
    (hc : IsMulCommutative U) (hexp : ∀ u ∈ U, u^2 = 1)
    (hfix : U ⊓ centralizer (K : Set G) = ⊥)
    (hZU : ⁅SourceInterface.centerIn (msQ K R),K⁆ ≤ U) :
    SourceInterface.omegaCenterIn S =
      (U ⊓ centralizer (S : Set G)) ⊔
        (SourceInterface.omegaCenterIn S ⊓ centralizer (K : Set G)) ∧
    (U ⊓ centralizer (S : Set G)) ⊓
      (SourceInterface.omegaCenterIn S ⊓ centralizer (K : Set G)) = ⊥ ∧
    (K ⊔ R) ⊓ centralizer (SourceInterface.omegaCenterIn S : Set G) =
      (K ⊓ centralizer ((U ⊓ centralizer (S : Set G) : Subgroup G) : Set G)) ⊔ R := by
  have hNS : (K ⊔ R).pCoreIn 2 ≤ S := by
    obtain ⟨P,hP⟩ := hS
    exact hP ▸ pCoreIn_le_sylow _ P
  have hWZ : U ⊓ centralizer (S : Set G) ≤ SourceInterface.omegaCenterIn S := by
    rintro u ⟨hu,huc⟩
    exact (mem_omegaCenterIn_iff S u).mpr ⟨hNS (msQ_le_joinCore (hUQ hu)),huc,hexp u hu⟩
  have hsplit : SourceInterface.omegaCenterIn S =
      (U ⊓ centralizer (S : Set G)) ⊔
        (SourceInterface.omegaCenterIn S ⊓ centralizer (K : Set G)) := by
    apply le_antisymm _ (sup_le hWZ inf_le_left)
    intro z hz
    obtain ⟨u,hu,huc⟩ := sylow_correction h hn hS hJU hc hexp hfix hZU z hz
    have hb := (SourceInterface.omegaCenterIn S).mul_mem
      ((SourceInterface.omegaCenterIn S).inv_mem (hWZ hu)) hz
    have hh := ((U ⊓ centralizer (S : Set G)) ⊔
      (SourceInterface.omegaCenterIn S ⊓ centralizer (K : Set G))).mul_mem
      (mem_sup_left hu) (mem_sup_right ⟨hb,huc⟩)
    simpa only [mul_inv_cancel_left] using hh
  have hcomp : K ⊓ centralizer (SourceInterface.omegaCenterIn S : Set G) =
      K ⊓ centralizer ((U ⊓ centralizer (S : Set G) : Subgroup G) : Set G) := by
    apply le_antisymm (inf_le_inf_left _ (centralizer_le hWZ))
    rintro k ⟨hk,hkU⟩
    refine ⟨hk,?_⟩
    intro z hz
    obtain ⟨u,hu,huc⟩ := sylow_correction h hn hS hJU hc hexp hfix hZU z hz
    have hh := (Commute.mul_left (show Commute u k from hkU u hu)
      (show Commute (u⁻¹*z) k from (huc k hk).symm)).eq
    simpa only [mul_inv_cancel_left] using hh
  refine ⟨hsplit,bot_unique ((le_inf (inf_le_left.trans inf_le_left)
    (inf_le_right.trans inf_le_right)).trans_eq hfix),?_⟩
  have hRC : R ≤ centralizer (SourceInterface.omegaCenterIn S : Set G) := by
    intro r hr z hz
    exact (((mem_omegaCenterIn_iff S z).mp hz).2.1 r (hRS hr)).symm
  apply le_antisymm
  · rintro x ⟨hx,hxc⟩
    obtain ⟨k,hk,r,hr,rfl⟩ := product h hn x hx
    have hkc : k ∈ centralizer (SourceInterface.omegaCenterIn S : Set G) := by
      have hh := (centralizer _).mul_mem hxc ((centralizer _).inv_mem (hRC hr))
      simpa only [mul_inv_cancel_right] using hh
    exact Subgroup.mul_mem_sup (hcomp.le ⟨hk,hkc⟩) hr
  · apply sup_le
    · intro k hk
      exact ⟨mem_sup_left hk.1,(hcomp.ge hk).2⟩
    · exact le_inf le_sup_right hRC

omit [CharP F 2] in
private theorem join_normalizes_core : K ⊔ R ≤ normalizer (msQ K R : Set G) := by
  rw [←commutator_map_eq_msQ]
  let := component_normal h hn
  let J := K ⊔ R
  have hn : (⁅pCore 2 J,K.subgroupOf J⁆ : Subgroup J).Normal := inferInstance
  exact (normal_subgroupOf_iff_le_normalizer (map_subtype_le _)).mp (by
    simpa only [subgroupOf,comap_map_eq_self_of_injective (K ⊔ R).subtype_injective] using hn)

omit [CharP F 2] in
private theorem join_normalizes_center :
    K ⊔ R ≤ normalizer (SourceInterface.centerIn (msQ K R) : Set G) :=
  (join_normalizes_core h hn).trans
    (normalizer_le_normalizer_characteristic_image (msQ K R) (center (msQ K R)))

omit [CharP F 2] in
omit [CharP F 2] in
private theorem join_normalizes_center_commutator :
    K ⊔ R ≤ normalizer (⁅SourceInterface.centerIn (msQ K R),K⁆ : Subgroup G) := by
  have hJK := (normal_subgroupOf_iff_le_normalizer (show K ≤ K ⊔ R from le_sup_left)).mp
    (component_normal h hn)
  intro j hj
  apply mem_normalizer_iff_map_conj_eq.mpr
  rw [map_commutator,mem_normalizer_iff_map_conj_eq.mp (join_normalizes_center h hn hj),
    mem_normalizer_iff_map_conj_eq.mp (hJK hj)]

omit [CharP F 2] in
private theorem center_commutator_le_center :
    ⁅SourceInterface.centerIn (msQ K R),K⁆ ≤ SourceInterface.centerIn (msQ K R) :=
  le_normalizer_iff_commutator_le_left.mp ((le_sup_left : K ≤ K ⊔ R).trans
    (join_normalizes_center h hn))

/-- In the doubled whole-core row, the actual Sylow-omega centralizer is the
product of R with the component fixer of the Sylow-fixed part of the core. -/
theorem doubled_sylow_section
    {S : Subgroup G} (hS : Chapter1.IsSylowIn 2 S (K ⊔ R)) (hRS : R ≤ S)
    (e : (K ⧸ pCore 2 K) ≃* SL(3,F))
    (hm : HasSectionModel K (msQ K R) ⊥ (linearThreeActor e)
      ((specialLinearNatural (k := F) 3).prod (specialLinearNatural (k := F) 3))) :
    SourceInterface.omegaCenterIn S =
      (msQ K R ⊓ centralizer (S : Set G)) ⊔
        (SourceInterface.omegaCenterIn S ⊓ centralizer (K : Set G)) ∧
    (msQ K R ⊓ centralizer (S : Set G)) ⊓
      (SourceInterface.omegaCenterIn S ⊓ centralizer (K : Set G)) = ⊥ ∧
    (K ⊔ R) ⊓ centralizer (SourceInterface.omegaCenterIn S : Set G) =
      (K ⊓ centralizer ((msQ K R ⊓ centralizer (S : Set G) : Subgroup G) : Set G)) ⊔ R := by
  obtain ⟨hc,hexp,hfix⟩ := section_properties _
    (fun v hv => Prod.ext (natural_fixed_zero v.1 (fun g => congrArg Prod.fst (hv g)))
      (natural_fixed_zero v.2 (fun g => congrArg Prod.snd (hv g)))) e hm
  exact section_sylow_geometry h hn hS hRS le_rfl (join_normalizes_core h hn)
    hc hexp hfix ((center_commutator_le_center h hn).trans (map_subtype_le _))

/-- The centralizer formula on the literal join and chosen Sylow. -/
theorem doubled_sylow_centralizer
    {S : Subgroup G} (hS : Chapter1.IsSylowIn 2 S (K ⊔ R)) (hRS : R ≤ S)
    (e : (K ⧸ pCore 2 K) ≃* SL(3,F))
    (hm : HasSectionModel K (msQ K R) ⊥ (linearThreeActor e)
      ((specialLinearNatural (k := F) 3).prod (specialLinearNatural (k := F) 3))) :
    (K ⊔ R) ⊓ centralizer (SourceInterface.omegaCenterIn S : Set G) =
      (K ⊓ centralizer ((msQ K R ⊓ centralizer (S : Set G) : Subgroup G) : Set G)) ⊔ R :=
  (doubled_sylow_section h hn hS hRS e hm).2.2

/-- The natural whole-center row determines the actual Sylow-omega centralizer
without a model for Q/Z(Q). -/
theorem natural_center_sylow_section
    {S : Subgroup G} (hS : Chapter1.IsSylowIn 2 S (K ⊔ R)) (hRS : R ≤ S)
    (e : (K ⧸ pCore 2 K) ≃* SL(3,F))
    (hm : HasSectionModel K (SourceInterface.centerIn (msQ K R)) ⊥ (linearThreeActor e)
      (specialLinearNatural (k := F) 3)) :
    SourceInterface.omegaCenterIn S =
      (SourceInterface.centerIn (msQ K R) ⊓ centralizer (S : Set G)) ⊔
        (SourceInterface.omegaCenterIn S ⊓ centralizer (K : Set G)) ∧
    (SourceInterface.centerIn (msQ K R) ⊓ centralizer (S : Set G)) ⊓
      (SourceInterface.omegaCenterIn S ⊓ centralizer (K : Set G)) = ⊥ ∧
    (K ⊔ R) ⊓ centralizer (SourceInterface.omegaCenterIn S : Set G) =
      (K ⊓ centralizer ((SourceInterface.centerIn (msQ K R) ⊓
        centralizer (S : Set G) : Subgroup G) : Set G)) ⊔ R := by
  obtain ⟨hc,hexp,hfix⟩ := section_properties _ natural_fixed_zero e hm
  exact section_sylow_geometry h hn hS hRS (map_subtype_le _) (join_normalizes_center h hn)
    hc hexp hfix (center_commutator_le_center h hn)

/-- The centralizer formula on the literal join and chosen Sylow. -/
theorem natural_center_sylow_centralizer
    {S : Subgroup G} (hS : Chapter1.IsSylowIn 2 S (K ⊔ R)) (hRS : R ≤ S)
    (e : (K ⧸ pCore 2 K) ≃* SL(3,F))
    (hm : HasSectionModel K (SourceInterface.centerIn (msQ K R)) ⊥ (linearThreeActor e)
      (specialLinearNatural (k := F) 3)) :
    (K ⊔ R) ⊓ centralizer (SourceInterface.omegaCenterIn S : Set G) =
      (K ⊓ centralizer ((SourceInterface.centerIn (msQ K R) ⊓
        centralizer (S : Set G) : Subgroup G) : Set G)) ⊔ R :=
  (natural_center_sylow_section h hn hS hRS e hm).2.2

/-- The fourth row needs only its natural central commutator. The fixed factor
of Z(Q) need not centralize the original ambient group. -/
theorem natural_center_commutator_sylow_section
    {S : Subgroup G} (hS : Chapter1.IsSylowIn 2 S (K ⊔ R)) (hRS : R ≤ S)
    (e : (K ⧸ pCore 2 K) ≃* SL(3,F))
    (hm : HasSectionModel K ⁅SourceInterface.centerIn (msQ K R),K⁆ ⊥ (linearThreeActor e)
      (specialLinearNatural (k := F) 3)) :
    SourceInterface.omegaCenterIn S =
      (⁅SourceInterface.centerIn (msQ K R),K⁆ ⊓ centralizer (S : Set G)) ⊔
        (SourceInterface.omegaCenterIn S ⊓ centralizer (K : Set G)) ∧
    (⁅SourceInterface.centerIn (msQ K R),K⁆ ⊓ centralizer (S : Set G)) ⊓
      (SourceInterface.omegaCenterIn S ⊓ centralizer (K : Set G)) = ⊥ ∧
    (K ⊔ R) ⊓ centralizer (SourceInterface.omegaCenterIn S : Set G) =
      (K ⊓ centralizer ((⁅SourceInterface.centerIn (msQ K R),K⁆ ⊓
        centralizer (S : Set G) : Subgroup G) : Set G)) ⊔ R := by
  obtain ⟨hc,hexp,hfix⟩ := section_properties _ natural_fixed_zero e hm
  exact section_sylow_geometry h hn hS hRS
    ((center_commutator_le_center h hn).trans (map_subtype_le _))
    (join_normalizes_center_commutator h hn) hc hexp hfix le_rfl

/-- The centralizer formula on the literal join and chosen Sylow. -/
theorem natural_center_commutator_sylow_centralizer
    {S : Subgroup G} (hS : Chapter1.IsSylowIn 2 S (K ⊔ R)) (hRS : R ≤ S)
    (e : (K ⧸ pCore 2 K) ≃* SL(3,F))
    (hm : HasSectionModel K ⁅SourceInterface.centerIn (msQ K R),K⁆ ⊥ (linearThreeActor e)
      (specialLinearNatural (k := F) 3)) :
    (K ⊔ R) ⊓ centralizer (SourceInterface.omegaCenterIn S : Set G) =
      (K ⊓ centralizer ((⁅SourceInterface.centerIn (msQ K R),K⁆ ⊓
        centralizer (S : Set G) : Subgroup G) : Set G)) ⊔ R :=
  (natural_center_commutator_sylow_section h hn hS hRS e hm).2.2

end CFSG.Quasithin.ChapterC.LinearThreeMS.NonbinarySource
