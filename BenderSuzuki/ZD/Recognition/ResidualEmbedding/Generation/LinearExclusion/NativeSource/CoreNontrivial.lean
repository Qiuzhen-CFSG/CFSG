module

public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearExclusion.NativeSource.CoreGrowth
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearExclusion.NativeSource.TwoCentralObstruction
public import BenderSuzuki.ZD.Recognition.MinimalReduction.Radical.Fusion
public import Theory.GroupTheory.DoubleCoverCentralizer.NormalTwoCentral
public import Theory.GroupTheory.NormalSubgroupCoreQuotient

/-!
# Nontriviality of the linear centralizer two-core

If O₂(J)=1, fusion puts every involution of V in A and source 15.3 forces
V=A. Thus M/A has trivial two-core. The even normal subgroup C₀/A contains
an ambient two-central involution. Source (15D) lifts its conjugacy class to
an involution of J, contradicting the quotient centralizer-index bound.

This proves GLS IV, Chapter 2, Lemma 15.4 from the original source context.
-/

noncomputable section
namespace BenderSuzuki.ZD.LinearExclusion
open Subgroup Theory.GroupTheory PFAppendixIII PFchapter1section1
open Theory.GroupTheory.DoubleCoverCentralizer
universe u
variable {G : Type u} [Group G] [Finite G] {Z : Set G} {M : Subgroup G}
  {z t : G} {n : ℕ} (d : Context Z M z t n)
include d
local notation "A" => closure (Z ∩ (M : Set G))
local notation "L" => residualGenerated M z t
local notation "D" => residualPairStabilizer M t
local notation "J" => centralizer (L : Set G)
local notation "C₀" => (M ⊓ centralizer (A : Set G) : Subgroup G)
local notation "V" => Subgroup.map M.subtype (pCore 2 M)

private theorem point_core_eq_of_centralizer_core_trivial (hJ : pCore 2 J = ⊥) : V = A := by
  apply d.point_twoCore_eq_distinguished_of_involutions d.twoCore_growth
  intro v hv hi
  by_contra ha
  have hiz : PFAppendixIII.IsInvolution (v : G) :=
    BenderSuzuki.IsInvolution.map_of_injective hi M.subtype M.subtype_injective
  have hvZ : (v : G) ∉ Z := fun hz => ha (subset_closure ⟨hz, v.property⟩)
  obtain ⟨w, hwD, hw⟩ := d.counting.nondistinguished_fusion v hiz hvZ
  obtain ⟨g, hg⟩ := isConj_iff.mp hw
  have hwi : PFAppendixIII.IsInvolution w := by
    rw [← hg]
    exact BenderSuzuki.IsInvolution.map_of_injective hiz
      (MulAut.conj g).toMonoidHom (MulAut.conj g).injective
  obtain ⟨S, hSM, hf⟩ := d.reduction.fusion
  obtain ⟨m, hm⟩ := involution_fusion_in_subgroup S hSM hf hiz hwi
    v.property ((show D ≤ M from inf_le_left) hwD) hw
  have hwV : w ∈ V := ⟨m * v * m⁻¹,
    Subgroup.Normal.conj_mem (inferInstance : (pCore 2 M).Normal) v hv m, hm⟩
  have hbot := d.pair_inf_point_twoCore_le_centralizer_twoCore ⟨hwD, hwV⟩
  rw [hJ, Subgroup.map_bot] at hbot
  exact hwi.ne_one (mem_bot.mp hbot)

/-- The original centralizer J has nontrivial two-core (source Lemma 15.4). -/
public theorem Context.centralizer_twoCore_ne_bot : pCore 2 J ≠ ⊥ := by
  intro hJ
  have hVA := point_core_eq_of_centralizer_core_trivial d hJ
  let : ((A).subgroupOf M).Normal := distinguishedClosure_normal d.minimal.disconnected
  let : ((A).subgroupOf C₀).Normal :=
    normal_subgroupOf_of_le_normalizer (by
      rw [distinguishedClosure_normalizer d.minimal.disconnected]
      exact inf_le_left)
  let qM := QuotientGroup.mk' ((A).subgroupOf M)
  let qC := QuotientGroup.mk' ((A).subgroupOf C₀)
  let f : C₀ →* M ⧸ (A).subgroupOf M :=
    qM.comp (inclusion (show C₀ ≤ M from inf_le_left))
  have hk : f.ker = (A).subgroupOf C₀ := by
    ext c
    exact QuotientGroup.eq_one_iff (inclusion (show C₀ ≤ M from inf_le_left) c)
  let N := f.range
  have hN : N = ((C₀).subgroupOf M).map qM := by
    ext v
    constructor
    · rintro ⟨c, rfl⟩
      exact ⟨inclusion (show C₀ ≤ M from inf_le_left) c, c.property, rfl⟩
    · rintro ⟨m, hm, rfl⟩
      exact ⟨⟨m, hm⟩, rfl⟩
  let : ((C₀).subgroupOf M).Normal := d.centralizer_normal
  let : N.Normal := hN ▸ (inferInstance : ((C₀).subgroupOf M).Normal).map
    qM (QuotientGroup.mk'_surjective _)
  let e : (C₀ ⧸ (A).subgroupOf C₀) ≃* N :=
    (QuotientGroup.quotientMulEquivOfEq hk.symm).trans
      (QuotientGroup.quotientKerEquivRange f)
  have he (c : C₀) : (e (qC c) : M ⧸ (A).subgroupOf M) = f c := rfl
  have hqM : pCore 2 (M ⧸ (A).subgroupOf M) = ⊥ :=
    d.distinguished_quotient_twoCore_eq_bot_of_point_core_eq hVA
  have hqN : pCore 2 N = ⊥ := by
    rw [pCore_eq_comap_of_normal, hqM, MonoidHom.comap_bot]
    exact N.subtype.ker_eq_bot N.subtype_injective
  have hqC : pCore 2 (C₀ ⧸ (A).subgroupOf C₀) = ⊥ := by
    apply map_injective (f := e.toMonoidHom) e.injective
    rw [pCore_map_iso, hqN, Subgroup.map_bot]
  let j : J →* N := f.rangeRestrict.comp (inclusion d.centralizer_le_distinguished_centralizer)
  have hj : Function.Injective j := by
    apply (MonoidHom.ker_eq_bot_iff _).mp
    apply eq_bot_iff.mpr
    intro x hx
    have hxA : (x : G) ∈ A := by
      have hh : f (inclusion d.centralizer_le_distinguished_centralizer x) = 1 :=
        congrArg Subtype.val hx
      have hmem : inclusion d.centralizer_le_distinguished_centralizer x ∈ f.ker := hh
      rwa [hk] at hmem
    have hxD : (x : G) ∈ D :=
      centralizer_residualGenerated_le_pair d.minimal.disconnected d.z_mem d.z_mem_M x.property
    exact mem_bot.mpr (Subtype.ext (mem_bot.mp
      ((disjoint_iff.mp d.distinguished_disjoint_pair_source).le ⟨hxA, hxD⟩)))
  have hEven : 2 ∣ Nat.card N :=
    (even_iff_two_dvd.mp d.centralizer_even).trans (card_dvd_of_injective j hj)
  obtain ⟨v, hvN, hvi, hvt⟩ := exists_twoCentral_involution_in_normal N hEven
  let w : C₀ ⧸ (A).subgroupOf C₀ := e.symm ⟨v, hvN⟩
  have hw : PFAppendixIII.IsInvolution w := by
    have hw2 : orderOf w = 2 := by simpa [w] using hvi
    exact ⟨fun h => by rw [h, orderOf_one] at hw2; omega,
      hw2 ▸ pow_orderOf_eq_one w⟩
  have hwcore : w ∉ pCore 2 (C₀ ⧸ (A).subgroupOf C₀) := by
    rw [hqC]
    exact fun hh => hw.ne_one (mem_bot.mp hh)
  obtain ⟨x, hxi, hconj⟩ := d.centralizer_quotient_involution_conjugate_lift w hw hwcore
  obtain ⟨a, ha⟩ := isConj_iff.mp hconj
  let xm : M := ⟨x, (d.centralizer_le_distinguished_centralizer x.property).1⟩
  have hxm : PFAppendixIII.IsInvolution xm :=
    BenderSuzuki.IsInvolution.map_of_injective hxi
      (inclusion (d.centralizer_le_distinguished_centralizer.trans inf_le_left))
      (inclusion_injective _)
  apply d.centralizer_involution_image_not_twoCentral xm x.property hxm
  have ht := hvt.map (MulAut.conj (e a : M ⧸ (A).subgroupOf M))
  have hh := congrArg (fun b => (e b : M ⧸ (A).subgroupOf M)) ha
  have hwe : (e w : M ⧸ (A).subgroupOf M) = v := by
    exact congrArg Subtype.val (e.apply_symm_apply ⟨v, hvN⟩)
  change TwoCentral ((e a : M ⧸ (A).subgroupOf M) * v *
    (e a : M ⧸ (A).subgroupOf M)⁻¹) at ht
  have hh' : (e a : M ⧸ (A).subgroupOf M) * v *
      (e a : M ⧸ (A).subgroupOf M)⁻¹ = qM xm := by
    have hxe : (e (qC (inclusion d.centralizer_le_distinguished_centralizer x)) :
        M ⧸ (A).subgroupOf M) = qM xm := rfl
    change (e (a * w * a⁻¹) : M ⧸ (A).subgroupOf M) =
      (e (qC (inclusion d.centralizer_le_distinguished_centralizer x)) :
        M ⧸ (A).subgroupOf M) at hh
    simpa only [map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv, hwe, hxe] using hh
  exact hh' ▸ ht

end BenderSuzuki.ZD.LinearExclusion
