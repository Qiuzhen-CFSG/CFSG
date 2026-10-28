module
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.Constrained.Catalogue.LocalComponentBlocks
-- Intentional continuation of the same finite block calculations.
import all CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.Constrained.Catalogue.BinaryThreeBlock
import all CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.Constrained.Catalogue.SixGeometry

/-!
# The literal rank-two block centralizers in the original local family

For a binary-three or ordinary six-point block K, all automorphisms fixing
its original Sylow subgroup form a group of order at most two. The original
central-involution seed acts nontrivially, so its image is that entire group.
The natural-module point stabilizer is maximal. Sylow detection through the
central two-group kernel lifts fixation modulo Z(K) to actual fixation,
identifying M_Z ∩ K with C_K(Z).

Every Sylow fixer is inner by an element of U(K). Thus the same subgroup
is exactly C_K(C_{U(K)}(S ∩ K)), retaining the full central attachment of U(K).
The C-component constructors discharge the block premises on the original
KQ₁. The A₆ reconstruction input remains explicit with its existing producer.
The original marker and later exchanged application preserve all literal
subgroups and quotient maps. G₂ marked-parabolic geometry and final full
15.1.20(2)/15.1.22 assembly remain separate obligations of this catalogue.

The two import-all edges deliberately continue the existing finite block
proofs internally, without changing their public interfaces.
Source: Aschbacher--Smith 15.1.20(2b), printed pp.1094--1095;
15.1.22(**), printed p.1099; A.1.39 and B.3.
-/

public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender Stellmacher
namespace CFSG.Quasithin.Chapter15.Section01.CaseIComponentData
open ChapterC ChapterC.C27Source
open Chapter1.RadicalExclusions.ModelReduction FullSieve FullSieve.SourceInterface
open Section03 Section03.InitialSource ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V : Subgroup G}

private theorem fixed_of_central_displacement {A : Type*} [Group A] [Finite A]
    (hZ : IsPGroup 2 (center A)) (P : Sylow 2 A) (a : MulAut A)
    (ha : ∀ x ∈ P, a x = x) {x : A} (hx : a x * x⁻¹ ∈ center A) : a x = x := by
  let q := QuotientGroup.mk' (center A)
  let C := (q.comp a.toMonoidHom).eqLocus q
  have hPC : (P : Subgroup A) ≤ C := by
    intro y hy
    change q (a y) = q y
    rw [ha y hy]
  have he : q.comp (a.toMonoidHom.comp C.subtype) = q.comp C.subtype := by
    ext y
    exact y.property
  have hkernel : q.ker = center A := QuotientGroup.ker_mk' _
  have hh := MonoidHom.eq_of_central_pGroup_kernel_of_sylow q hkernel.le
    (hkernel.symm ▸ hZ) (a.toMonoidHom.comp C.subtype) C.subtype he (P.subtype hPC)
    (fun y hy => ha y (show (y : A) ∈ P from hy))
  have hxC : x ∈ C := by
    change q (a x) = q x
    exact QuotientGroup.eq_iff_div_mem.mpr (by simpa only [div_eq_mul_inv] using hx)
  exact DFunLike.congr_fun hh ⟨x,hxC⟩

private theorem inner_of_sylow_fixer
    {A W : Type*} [Group A] [CommGroup W] {ρ : A →* MulAut W}
    {K : Subgroup G} (hs : IsShort K) (hq : IsQuasisimple (K ⧸ pCore 2 K))
    (m : BlockModuleModel K ρ) (hρ : Function.Injective ρ)
    (P : Sylow 2 K) (a : MulAut K) (ha : ∀ x ∈ P, a x = x) :
    ∃ u : blockU K, a = MulAut.conj (u : K) := by
  let := hq.toIsPerfect
  let : Group.IsPerfect K := hs.twoPerfect.isPerfect_of_surjective_pGroup_kernel
    (QuotientGroup.mk' (pCore 2 K)) (QuotientGroup.mk'_surjective _) (by
      rw [QuotientGroup.ker_mk']; exact pCore_isPGroup)
  obtain ⟨u,hu,_⟩ := hs.automorphism_eq_conj_of_central_sylow m hρ P a (by
    intro x hx
    rw [ha x hx,mul_inv_cancel]
    exact one_mem _)
  exact ⟨u,hu⟩

private theorem localFamily_centralizing_of_small_fixers
    (d : CaseIComponentData T M Mc V)
    (h : PreparedChosenModule T M V) (hTM : (T : Subgroup G) ≤ M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    {K : Subgroup G} (hK : K ∈ Chapter1.LIn d.G1 d.S)
    (hq : IsQuasisimple (K ⧸ pCore 2 K)) (hout : ¬ K ≤ d.MZ)
    (hf : generalizedFitting K = pCore 2 K)
    (hbound : ∀ (P : Sylow 2 K) (B : Subgroup (MulAut K)),
      (∀ a ∈ B, ∀ x ∈ P, a x * x⁻¹ ∈ center K) → Nat.card B ≤ 2)
    (hparabolic : ∀ (P : Sylow 2 K) (a : MulAut K), a ≠ 1 →
      (∀ x ∈ P, a x * x⁻¹ ∈ center K) →
      ∃ J : Subgroup K, IsCoatom J ∧ ∀ x ∈ J, a x * x⁻¹ ∈ center K)
    (hinner : ∀ (P : Sylow 2 K) (a : MulAut K), (∀ x ∈ P, a x = x) →
      ∃ u : blockU K, a = MulAut.conj (u : K)) :
    d.MZ ⊓ K = K ⊓ centralizer (centralInvolutions T : Set G) ∧
      IsCoatom ((d.MZ ⊓ K).subgroupOf K) ∧
      d.MZ ⊓ K = K ⊓ centralizer
        (((blockU K).map K.subtype ⊓ centralizer (d.S ⊓ K : Set G) : Subgroup G) : Set G) := by
  obtain ⟨P,hP⟩ := ComponentModels.source20_sylow_intersection hK.2
  have hZN := (d.localFamily_normalizer_setup h hTM hu hK hq hout hf).2.2
  let f : centralInvolutions T →* MulAut K := K.normalizerMonoidHom.comp
    ((centralInvolutions T).inclusion (hZN.trans inf_le_right))
  let B := fixingSubgroup (MulAut K) (P : Set K)
  have hfix (a : MulAut K) (ha : a ∈ B) (x : K) (hx : x ∈ P) : a x = x :=
    (mem_fixingSubgroup_iff _).mp ha x hx
  have hmod (a : MulAut K) (ha : a ∈ B) (x : K) (hx : x ∈ P) :
      a x * x⁻¹ ∈ center K := by rw [hfix a ha x hx,mul_inv_cancel]; exact one_mem _
  have hfB (z : centralInvolutions T) : f z ∈ B := by
    apply (mem_fixingSubgroup_iff _).mpr
    intro x hx
    apply Subtype.ext
    change (z : G) * (x : G) * (z : G)⁻¹ = x
    rw [←centralInvolutions_le_centralizer_sylow T z.property x
      (d.S_le_T (hP ▸ mem_map_of_mem K.subtype hx).1),mul_inv_cancel_right]
  have hMc := centralizer_le_partner T hu
  have hn : ¬ centralInvolutions T ≤ centralizer (K : Set G) := by
    intro hh
    exact hout (le_inf hK.1 ((le_centralizer_iff.mp hh).trans hMc))
  obtain ⟨z,hz,hzc⟩ := SetLike.not_le_iff_exists.mp hn
  have hzne : f ⟨z,hz⟩ ≠ 1 := by
    intro he
    apply hzc
    intro x hx
    have hh := congrArg (fun a : MulAut K => (a ⟨x,hx⟩ : G)) he
    change z * x * z⁻¹ = x at hh
    exact (mul_inv_eq_iff_eq_mul.mp hh).symm
  let : Nontrivial B := ⟨⟨⟨f ⟨z,hz⟩,hfB ⟨z,hz⟩⟩,1,
    fun he => hzne (congrArg Subtype.val he)⟩⟩
  have hc : Nat.card B = 2 := by
    have hle := hbound P B hmod
    have hlt := Finite.one_lt_card (α := B)
    omega
  obtain ⟨a,ha,ha_unique⟩ := (Nat.card_eq_two_iff' (1 : B)).mp hc
  have ha0 : (a : MulAut K) ≠ 1 := fun hh => ha (Subtype.ext hh)
  obtain ⟨J,hJ,hJfix⟩ := hparabolic P a ha0 (hmod a a.property)
  have hZ : IsPGroup 2 (center K) := pCore_isPGroup.to_le
    ((center_le_centralizer (pCore 2 K : Set K)).trans
      (hf ▸ centralizer_generalizedFitting_le K))
  have hJC : J ≤ (centralizer (centralInvolutions T : Set G)).comap K.subtype := by
    intro x hx z hz
    have hm : f ⟨z,hz⟩ x * x⁻¹ ∈ center K := by
      by_cases he : f ⟨z,hz⟩ = 1
      · rw [he]; simp
      · have he' : (⟨f ⟨z,hz⟩,hfB ⟨z,hz⟩⟩ : B) = a :=
          ha_unique _ (fun hh => he (congrArg Subtype.val hh))
        have he0 : f ⟨z,hz⟩ = (a : MulAut K) := congrArg Subtype.val he'
        rw [he0]
        exact hJfix x hx
    have hh := fixed_of_central_displacement hZ P (f ⟨z,hz⟩)
      (hfix _ (hfB ⟨z,hz⟩)) hm
    have he := congrArg Subtype.val hh
    change z * (x : G) * z⁻¹ = x at he
    exact mul_inv_eq_iff_eq_mul.mp he
  have hC : K ⊓ centralizer (centralInvolutions T : Set G) ≤ d.MZ ⊓ K := by
    intro x hx
    exact ⟨⟨hK.1 hx.1,hMc hx.2⟩,hx.1⟩
  have hJM : J ≤ (d.MZ ⊓ K).subgroupOf K :=
    fun x hx => hC ⟨x.property,hJC hx⟩
  have hnot : (d.MZ ⊓ K).subgroupOf K ≠ ⊤ := by
    intro he
    apply hout
    intro k hk
    exact ((show (⟨k,hk⟩ : K) ∈ (d.MZ ⊓ K).subgroupOf K from he ▸ mem_top _)).1
  have he : (d.MZ ⊓ K).subgroupOf K = J := (hJ.le_iff_eq hnot).mp hJM
  have hEq : d.MZ ⊓ K = K ⊓ centralizer (centralInvolutions T : Set G) := by
    refine le_antisymm ?_ hC
    intro x hx
    exact ⟨hx.2,hJC (he ▸ (show (⟨x,hx.2⟩ : K) ∈ (d.MZ ⊓ K).subgroupOf K from hx))⟩
  have hJa (x : K) (hx : (x : G) ∈ d.MZ ⊓ K) : (a : MulAut K) x = x := by
    have he' : (⟨f ⟨z,hz⟩,hfB ⟨z,hz⟩⟩ : B) = a :=
      ha_unique _ (fun hh => hzne (congrArg Subtype.val hh))
    have he0 : f ⟨z,hz⟩ = (a : MulAut K) := congrArg Subtype.val he'
    rw [←he0]
    apply Subtype.ext
    change z * (x : G) * z⁻¹ = x
    rw [(hEq.le hx).2 z hz,mul_inv_cancel_right]
  obtain ⟨u,hu⟩ := hinner P a (hfix a a.property)
  have huFix : ((u : K) : G) ∈ centralizer (d.S ⊓ K : Set G) := by
    intro y hy
    change y ∈ d.S ⊓ K at hy
    obtain ⟨x,hx,rfl⟩ := hP.symm ▸ hy
    have hh := hfix a a.property x hx
    rw [hu] at hh
    exact (mul_inv_eq_iff_eq_mul.mp (congrArg Subtype.val hh)).symm
  refine ⟨hEq,he ▸ hJ,le_antisymm ?_ ?_⟩
  · intro x hx
    refine ⟨hx.2,?_⟩
    rintro y ⟨⟨v,hv,rfl⟩,hy⟩
    let b := MulAut.conj v
    have hb : b ∈ B := by
      apply (mem_fixingSubgroup_iff _).mpr
      intro t ht
      apply Subtype.ext
      change (v : G) * (t : G) * (v : G)⁻¹ = t
      have hyt : (t : G) * (v : G) = (v : G) * (t : G) :=
        hy t (show (t : G) ∈ d.S ⊓ K from hP ▸ mem_map_of_mem K.subtype ht)
      rw [←hyt,mul_inv_cancel_right]
    have hbfix : b ⟨x,hx.2⟩ = ⟨x,hx.2⟩ := by
      by_cases hb1 : b = 1
      · rw [hb1]; rfl
      · have he' : (⟨b,hb⟩ : B) = a :=
          ha_unique _ (fun hh => hb1 (congrArg Subtype.val hh))
        have he0 : b = (a : MulAut K) := congrArg Subtype.val he'
        rw [he0]
        exact hJa ⟨x,hx.2⟩ hx
    exact mul_inv_eq_iff_eq_mul.mp (congrArg Subtype.val hbfix)
  · intro x hx
    have hxa : (a : MulAut K) ⟨x,hx.1⟩ = ⟨x,hx.1⟩ := by
      rw [hu]
      apply Subtype.ext
      change ((u : K) : G) * x * ((u : K) : G)⁻¹ = x
      rw [hx.2 u ⟨mem_map_of_mem K.subtype u.property,huFix⟩,mul_inv_cancel_right]
    apply hC
    refine ⟨hx.1,?_⟩
    intro z hz
    have hzfix : f ⟨z,hz⟩ ⟨x,hx.1⟩ = ⟨x,hx.1⟩ := by
      by_cases hz1 : f ⟨z,hz⟩ = 1
      · rw [hz1]; rfl
      · have he' : (⟨f ⟨z,hz⟩,hfB ⟨z,hz⟩⟩ : B) = a :=
          ha_unique _ (fun hh => hz1 (congrArg Subtype.val hh))
        have he0 : f ⟨z,hz⟩ = (a : MulAut K) := congrArg Subtype.val he'
        rw [he0]
        exact hxa
    exact mul_inv_eq_iff_eq_mul.mp (congrArg Subtype.val hzfix)

/-- The general binary-three local block has the maximal centralizer of the
original central-involution seed, retaining its full central attachment. -/
theorem localFamily_binaryThree_seed_centralizer
    (d : CaseIComponentData T M Mc V)
    (h : PreparedChosenModule T M V) (hTM : (T : Subgroup G) ≤ M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    {K : Subgroup G} (hK : K ∈ Chapter1.LIn d.G1 d.S)
    (hq : IsQuasisimple (K ⧸ pCore 2 K)) (hout : ¬ K ≤ d.MZ)
    (hb : IsSL3EvenBlock K 1) :
    d.MZ ⊓ K = K ⊓ centralizer (centralInvolutions T : Set G) ∧
      IsCoatom ((d.MZ ⊓ K).subgroupOf K) ∧
      d.MZ ⊓ K = K ⊓ centralizer
        (((blockU K).map K.subtype ⊓ centralizer (d.S ⊓ K : Set G) : Subgroup G) : Set G) :=
by
  apply d.localFamily_centralizing_of_small_fixers h hTM hu hK hq hout hb.2.1.fitting
    (binaryThree_sylow_fixers hb) (binaryThree_fixer_parabolic hb)
  obtain ⟨F,_,_,_,ρ,⟨m⟩,hρ⟩ := hb.2.2
  have hρi : Function.Injective ρ := by
    intro g j he
    apply Matrix.SpecialLinearGroup.toLin'_injective
    apply LinearEquiv.ext
    intro w
    have hh := congrArg (fun k : MulAut (Multiplicative (Fin 3 → F)) =>
      (k (Multiplicative.ofAdd w)).toAdd) he
    simp only [hρ] at hh
    exact hh
  exact inner_of_sylow_fixer hb.2.1 hq m hρi

/-- The same maximal-centralizer identity for every ordinary six-point
local block, with no replacement of K by the selected component. -/
theorem localFamily_six_seed_centralizer
    (d : CaseIComponentData T M Mc V)
    (h : PreparedChosenModule T M V) (hTM : (T : Subgroup G) ≤ M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    {K : Subgroup G} (hK : K ∈ Chapter1.LIn d.G1 d.S)
    (hq : IsQuasisimple (K ⧸ pCore 2 K)) (hout : ¬ K ≤ d.MZ)
    (hb : IsAlternatingBlock K 6) :
    d.MZ ⊓ K = K ⊓ centralizer (centralInvolutions T : Set G) ∧
      IsCoatom ((d.MZ ⊓ K).subgroupOf K) ∧
      d.MZ ⊓ K = K ⊓ centralizer
        (((blockU K).map K.subtype ⊓ centralizer (d.S ⊓ K : Set G) : Subgroup G) : Set G) :=
by
  apply d.localFamily_centralizing_of_small_fixers h hTM hu hK hq hout hb.2.1.fitting
    (SixGeometry.six_sylow_fixers hb) (SixGeometry.six_fixer_parabolic hb)
  obtain ⟨ρ,⟨m⟩,hρ⟩ := hb.2.2
  have hρi : Function.Injective ρ := by
    intro g j he
    apply Subtype.ext
    apply BinaryPermutation.naturalRepresentation_injective (Fin 6) (by decide)
    apply LinearMap.ext
    intro w
    have hh := congrArg (fun k : MulAut (Multiplicative (BinaryPermutation.natural (Fin 6))) =>
      (k (Multiplicative.ofAdd w)).toAdd) he
    simp only [hρ] at hh
    exact hh
  exact inner_of_sylow_fixer hb.2.1 hq m hρi

end CFSG.Quasithin.Chapter15.Section01.CaseIComponentData


namespace CFSG.Quasithin.Chapter15.Section01.CaseIComponentData
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender Stellmacher
open ChapterC ChapterC.C27Source
open Chapter1.RadicalExclusions.ModelReduction FullSieve FullSieve.SourceInterface
open Section03 Section03.InitialSource ChapterA.Section05To06
open Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
universe u
variable {G : Type u} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V : Subgroup G} {p : ℕ}

/-- Reconstruct the general binary-three C-component and prove both literal
maximal-centralizer identities on that same K. -/
theorem PreExclusionSource.localComponent_binaryThree_geometry
    {d : CaseIComponentData T M Mc V} {h : PreparedChosenModule T M V}
    (s : d.PreExclusionSource h.normalized p)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    {K : Subgroup G} (hK : K ∈ Chapter1.LIn d.G1 d.S)
    (hc : K ∈ Chapter1.cComponentsIn d.G1)
    (hq : IsQuasisimple (K ⧸ pCore 2 K)) (hout : ¬ K ≤ d.MZ)
    (hf : generalizedFitting K = pCore 2 K)
    (e : d.normalizerImage K ≃* Matrix.PSL3Two.SL) :
    IsSL3EvenBlock K 1 ∧
      (∃ t : (K ⧸ pCore 2 K) ≃* Matrix.PSL3Two.SL,
        ∀ k : K, t (QuotientGroup.mk' (pCore 2 K) k) = e (d.toNormalizerImage K k)) ∧
      d.MZ ⊓ K = K ⊓ centralizer (centralInvolutions T : Set G) ∧
      IsCoatom ((d.MZ ⊓ K).subgroupOf K) ∧
      d.MZ ⊓ K = K ⊓ centralizer
        (((blockU K).map K.subtype ⊓ centralizer (d.S ⊓ K : Set G) : Subgroup G) : Set G) := by
  obtain ⟨hb,ht⟩ := s.localComponent_binaryThree_block (h := h)
    hG hempty hM hJ hu hK hc hq hout hf e
  exact ⟨hb,ht,d.localFamily_binaryThree_seed_centralizer h hM.1.2 hu hK hq hout hb⟩

/-- Both A₆ covering outcomes yield the ordinary block and its full literal
centralizers after the original exceptional-offender exclusion. -/
theorem PreExclusionSource.localComponent_six_geometry_of_reconstruction
    {d : CaseIComponentData T M Mc V} {h : PreparedChosenModule T M V}
    (s : d.PreExclusionSource h.normalized p)
    (ha : AlternatingSixReconstructionInput.{u} KnownSimple.IsKnownSimple)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    {K : Subgroup G} (hK : K ∈ Chapter1.LIn d.G1 d.S)
    (hc : K ∈ Chapter1.cComponentsIn d.G1)
    (hq : IsQuasisimple (K ⧸ pCore 2 K)) (hout : ¬ K ≤ d.MZ)
    (hf : generalizedFitting K = pCore 2 K)
    (e : (d.normalizerImage K ⧸ center (d.normalizerImage K)) ≃* alternatingGroup (Fin 6)) :
    IsAlternatingBlock K 6 ∧
      (∃ t : (K ⧸ centralPreimage (pCore 2 K)) ≃* alternatingGroup (Fin 6),
        ∀ k : K, t (QuotientGroup.mk' (centralPreimage (pCore 2 K)) k) =
          e (QuotientGroup.mk' (center (d.normalizerImage K)) (d.toNormalizerImage K k))) ∧
      d.MZ ⊓ K = K ⊓ centralizer (centralInvolutions T : Set G) ∧
      IsCoatom ((d.MZ ⊓ K).subgroupOf K) ∧
      d.MZ ⊓ K = K ⊓ centralizer
        (((blockU K).map K.subtype ⊓ centralizer (d.S ⊓ K : Set G) : Subgroup G) : Set G) := by
  obtain ⟨hb,ht⟩ := s.localComponent_six_block_of_reconstruction (h := h) ha
    hG hempty hM hJ hu hK hc hq hout hf e
  exact ⟨hb,ht,d.localFamily_six_seed_centralizer h hM.1.2 hu hK hq hout hb⟩

end CFSG.Quasithin.Chapter15.Section01.CaseIComponentData

namespace CFSG.Quasithin.Chapter15.Section01
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender Stellmacher
open ChapterC Section03 Section03.InitialSource ChapterA.Section05To06
open Chapter1.RadicalExclusions.ModelReduction FullSieve FullSieve.SourceInterface
open Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
universe u
variable {G : Type u} [Group G] [Finite G]

/-- Original-marker application of the additional rank-two centralizer
clauses. The component restriction is exactly the extra hypothesis in
15.1.20(2b); the original local family and its literal maps are unchanged. -/
theorem PreparedChosenModule.source_preExclusion_localComponent_centralizers
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
      ∀ K ∈ Chapter1.LIn d.G1 d.S, K ∈ Chapter1.cComponentsIn d.G1 →
        IsQuasisimple (K ⧸ pCore 2 K) → ¬ K ≤ d.MZ →
        generalizedFitting K = pCore 2 K →
        (Nonempty (d.normalizerImage K ≃* Matrix.PSL3Two.SL) ∨
          Nonempty ((d.normalizerImage K ⧸ center (d.normalizerImage K)) ≃*
            alternatingGroup (Fin 6))) →
        (IsSL3EvenBlock K 1 ∨ IsAlternatingBlock K 6) ∧
        d.MZ ⊓ K = K ⊓ centralizer (centralInvolutions T : Set G) ∧
        IsCoatom ((d.MZ ⊓ K).subgroupOf K) ∧
        d.MZ ⊓ K = K ⊓ centralizer
          (((blockU K).map K.subtype ⊓ centralizer (d.S ⊓ K : Set G) : Subgroup G) : Set G) := by
  obtain ⟨d,hZ,hr,s⟩ := h.component_of_preExclusionMarker
    hG T hempty hM hmany hJ hu hne hfull m hres
  refine ⟨d,hZ,hr,s,?_⟩
  intro K hK hc hq hout hf he
  rcases he with he | he
  · obtain ⟨e⟩ := he
    obtain ⟨hb,_,hh⟩ := s.localComponent_binaryThree_geometry (h := h)
      hG hempty hM hJ hu hK hc hq hout hf e
    exact ⟨Or.inl hb,hh⟩
  · obtain ⟨e⟩ := he
    obtain ⟨hb,_,hh⟩ := s.localComponent_six_geometry_of_reconstruction (h := h) ha
      hG hempty hM hJ hu hK hc hq hout hf e
    exact ⟨Or.inr hb,hh⟩

end CFSG.Quasithin.Chapter15.Section01

namespace CFSG.Quasithin.Chapter15.Section01.CaseIComponentData
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender Stellmacher
open ChapterC Section03 Section03.InitialSource ChapterA.Section05To06
open Chapter1.RadicalExclusions.ModelReduction FullSieve FullSieve.SourceInterface
open Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
universe u
variable {G : Type u} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V : Subgroup G}

/-- Later exchanged selection consumes the same full centralizer statements
on its original selected component; earlier prime-five arguments do not use it. -/
theorem ExchangedSource.constrained_rankTwo_block_centralizers
    {d : CaseIComponentData T M Mc V} {h : PreparedChosenModule T M V}
    (s : d.ExchangedSource) (sp : d.PreExclusionSource h.normalized 3)
    (ha : AlternatingSixReconstructionInput.{u} KnownSimple.IsKnownSimple)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hf : generalizedFitting d.L = pCore 2 d.L)
    (he : Nonempty (d.normalizerImage d.L ≃* Matrix.PSL3Two.SL) ∨
      Nonempty ((d.normalizerImage d.L ⧸ center (d.normalizerImage d.L)) ≃*
        alternatingGroup (Fin 6))) :
    (IsSL3EvenBlock d.L 1 ∨ IsAlternatingBlock d.L 6) ∧
      d.ML = d.L ⊓ centralizer (centralInvolutions T : Set G) ∧
      IsCoatom (d.ML.subgroupOf d.L) ∧
      d.ML = d.L ⊓ centralizer
        (((blockU d.L).map d.L.subtype ⊓ centralizer (d.SL : Set G) : Subgroup G) : Set G) := by
  have hK : d.L ∈ Chapter1.LIn d.G1 d.S := ⟨d.L_component.1,s.local_component⟩
  rcases he with he | he
  · obtain ⟨e⟩ := he
    obtain ⟨hb,_,hh⟩ := sp.localComponent_binaryThree_geometry (h := h)
      hG hempty hM hJ hu hK d.L_component s.quasisimple d.L_not_le_MZ hf e
    exact ⟨Or.inl hb,hh⟩
  · obtain ⟨e⟩ := he
    obtain ⟨hb,_,hh⟩ := sp.localComponent_six_geometry_of_reconstruction (h := h) ha
      hG hempty hM hJ hu hK d.L_component s.quasisimple d.L_not_le_MZ hf e
    exact ⟨Or.inr hb,hh⟩

end CFSG.Quasithin.Chapter15.Section01.CaseIComponentData
