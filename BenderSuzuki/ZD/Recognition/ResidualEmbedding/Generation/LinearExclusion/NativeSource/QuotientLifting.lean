module

public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearExclusion.Centralizer.EmbeddingNormalizers.NormalizerControl
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearExclusion.Centralizer.TwoStructure.Reduction
public import Theory.GroupTheory.CentralCoprimeLiftUnique
public import Theory.GroupAction.PrimeOrderConjugation
public import Theory.GroupTheory.Involution.OddRotation

/-!
# The central quotient in the linear two-core argument

Write A for the distinguished closure, C₀=C_M(A), and J=C_G(L). For every
nontrivial odd subgroup Y of J, source normalizer control and the pointwise
root centralizer identify N_C₀(Y) with A N_J(Y). The central elementary
kernel A does not change odd torsion or its normalizers. Thus the normalizer
of the image of Y in the literal quotient C₀/A lies in the image of J.
Every involution in this normalizer lifts to an actual involution of J.

These are the lifting assertions used in equation (15D) of GLS IV,
Chapter 2, Lemma 15.4, refs/KGroup/GLS4/Chapter2.tex. No nontriviality of
O₂(J), order-two conclusion, or odd supplement is assumed.
-/

noncomputable section
namespace BenderSuzuki.ZD.LinearExclusion
open Subgroup Theory.GroupTheory PFAppendixIII PFchapter1section1
open scoped Pointwise
universe u

private theorem normalizer_odd_preimage
    {E Q : Type*} [Group E] [Group Q] [Finite E]
    (q : E →* Q) (hc : q.ker ≤ center E) (hp : IsPGroup 2 q.ker)
    (Y : Subgroup E) (ho : Odd (Nat.card Y)) {g : E}
    (hg : q g ∈ normalizer (Y.map q : Set Q)) : g ∈ normalizer (Y : Set E) := by
  have forward (a : E) (ha : q a ∈ normalizer (Y.map q : Set Q))
      (y : E) (hy : y ∈ Y) : a * y * a⁻¹ ∈ Y := by
    have hm : q (a * y * a⁻¹) ∈ Y.map q := by
      simpa only [map_mul, map_inv] using
        (mem_normalizer_iff.mp ha (q y)).mp (mem_map_of_mem q hy)
    obtain ⟨v, hv, he⟩ := hm
    have hyN : y ^ Nat.card Y = 1 := by
      exact congrArg Subtype.val (pow_card_eq_one' (x := (⟨y, hy⟩ : Y)))
    have hvN : v ^ Nat.card Y = 1 := by
      exact congrArg Subtype.val (pow_card_eq_one' (x := (⟨v, hv⟩ : Y)))
    have hpow : (a * y * a⁻¹) ^ Nat.card Y = 1 := by
      simpa only [map_pow, MulAut.conj_apply, map_one] using
        congrArg (MulAut.conj a) hyN |>.trans (map_one (MulAut.conj a))
    have heq := q.eq_of_map_eq_of_pow_eq_one_of_central_pgroup_ker
      hc hp ho.coprime_two_left he.symm hpow hvN
    exact heq ▸ hv
  rw [mem_normalizer_iff]
  intro y
  refine ⟨forward g hg y, ?_⟩
  intro hy
  have hi : q g⁻¹ ∈ normalizer (Y.map q : Set Q) := by
    rw [map_inv]
    exact (normalizer (Y.map q : Set Q)).inv_mem hg
  simpa only [inv_inv, inv_mul_cancel_left, mul_inv_cancel_right, mul_assoc, inv_mul_cancel, mul_one] using
    forward g⁻¹ hi (g * y * g⁻¹) hy

variable {G : Type u} [Group G] [Finite G] {Z : Set G} {M : Subgroup G}
  {z t : G} {n : ℕ} (d : Context Z M z t n)
include d
local notation "A" => closure (Z ∩ (M : Set G))
local notation "L" => residualGenerated M z t
local notation "D" => residualPairStabilizer M t
local notation "J" => (centralizer (L : Set G) : Subgroup G)
local notation "C₀" => (M ⊓ centralizer (A : Set G) : Subgroup G)

private theorem distinguished_le_centralizer : A ≤ C₀ := by
  refine le_inf distinguishedClosure_le ?_
  apply le_centralizer_iff_isMulCommutative.mpr
  let := d.distinguished_elementary_card.1
  infer_instance

public theorem Context.centralizer_le_distinguished_centralizer : J ≤ C₀ :=
  le_inf ((centralizer_residualGenerated_le_pair d.minimal.disconnected d.z_mem
    d.z_mem_M).trans inf_le_left) (centralizer_le d.distinguished_le)

omit [Finite G] d in
private theorem distinguished_central_in_centralizer : (A).subgroupOf C₀ ≤ center C₀ := by
  intro a ha
  apply mem_center_iff.mpr
  intro c
  exact Subtype.ext (mem_centralizer_iff.mp c.property.2 a ha).symm

/-- The actual centralizer normalizer, before passing to the quotient. -/
public theorem Context.odd_subgroup_normalizer_in_distinguished_centralizer
    (Y : Subgroup G) (hYJ : Y ≤ J) (hY : Y ≠ ⊥) :
    C₀ ⊓ normalizer (Y : Set G) = A ⊔ (J ⊓ normalizer (Y : Set G)) := by
  have hAN : A ≤ normalizer (Y : Set G) :=
    (le_centralizer_iff.mp (hYJ.trans (centralizer_le d.distinguished_le))).trans
      (Subgroup.centralizer_le_normalizer (Y : Set G))
  have hAJ : J ≤ normalizer (A : Set G) :=
    (centralizer_le d.distinguished_le).trans (Subgroup.centralizer_le_normalizer (A : Set G))
  apply le_antisymm
  · intro x hx
    have hxAJ : x ∈ A ⊔ J := d.normalizer_inf_centralizer_eq ▸
      (show x ∈ normalizer (L : Set G) ⊓ centralizer (A : Set G) from
        ⟨d.normalizer_control_of_le_centralizer Y hYJ hY hx.2, hx.1.2⟩)
    rw [← SetLike.mem_coe, coe_mul_of_right_le_normalizer_left A J hAJ] at hxAJ
    obtain ⟨a, ha, j, hj, he⟩ := hxAJ
    have hjN : j ∈ normalizer (Y : Set G) := by
      have h := (normalizer (Y : Set G)).mul_mem
        ((normalizer (Y : Set G)).inv_mem (hAN ha)) hx.2
      rw [← he, inv_mul_cancel_left] at h
      exact h
    rw [← he]
    have hleft : A ≤ A ⊔ (J ⊓ normalizer (Y : Set G)) := le_sup_left
    have hright : J ⊓ normalizer (Y : Set G) ≤ A ⊔ (J ⊓ normalizer (Y : Set G)) := le_sup_right
    exact (A ⊔ (J ⊓ normalizer (Y : Set G))).mul_mem (hleft ha) (hright ⟨hj, hjN⟩)
  · exact sup_le (le_inf (distinguished_le_centralizer d) hAN)
      (le_inf (inf_le_left.trans (d.centralizer_le_distinguished_centralizer)) inf_le_right)

private theorem centralizer_quotient_injective_on_J
    {Q : Type*} [Group Q] (q : C₀ →* Q)
    (hk : q.ker = (A).subgroupOf C₀) :
    Function.Injective (q.comp (inclusion (d.centralizer_le_distinguished_centralizer))) := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply eq_bot_iff.mpr
  intro j hj
  have ha : (j : G) ∈ A := by
    have hmem : inclusion (d.centralizer_le_distinguished_centralizer) j ∈ q.ker := hj
    rwa [hk] at hmem
  have hs : (j : G) ^ 2 = 1 := congrArg Subtype.val
    (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      d.distinguished_elementary_card.1.exponent_dvd_p ⟨j, ha⟩)
  by_cases he : (j : G) = 1
  · exact mem_bot.mpr (Subtype.ext he)
  have hi : PFAppendixIII.IsInvolution (j : G) := ⟨he, hs⟩
  have hzJ := (isInvolution_iff_mem_Z_in_proper_residualGenerated
    d.minimal.disconnected d.reduction d.z_mem d.z_mem_M d.t_mem d.t_not_mem_M
    d.proper (d.distinguished_le ha)).mp hi
  exact (not_mem_Z_of_mem_residualPairStabilizer d.minimal.disconnected d.t_not_mem_M
    ((centralizer_residualGenerated_le_pair d.minimal.disconnected d.z_mem d.z_mem_M)
      j.property) hzJ).elim

private theorem quotient_normalizer_le_image_J
    {Q : Type*} [Group Q] (q : C₀ →* Q) (hq : Function.Surjective q)
    (hk : q.ker = (A).subgroupOf C₀)
    (Y : Subgroup G) (hYJ : Y ≤ J) (hY : Y ≠ ⊥) (ho : Odd (Nat.card Y)) :
    normalizer ((Y.subgroupOf C₀).map q : Set Q) ≤ ((J).subgroupOf C₀).map q := by
  intro v hv
  obtain ⟨c, rfl⟩ := hq v
  have hp : IsPGroup 2 q.ker := by
    rw [hk]
    exact (IsPGroup.of_card d.distinguished_elementary_card.2).of_equiv
      (subgroupOfEquivOfLe (distinguished_le_centralizer d)).symm
  have hc : q.ker ≤ center C₀ := hk ▸ distinguished_central_in_centralizer (Z := Z) (M := M)
  have hYo : Odd (Nat.card (Y.subgroupOf C₀)) := by
    rw [Nat.card_congr (subgroupOfEquivOfLe
      (hYJ.trans (d.centralizer_le_distinguished_centralizer))).toEquiv]
    exact ho
  have hcN := normalizer_odd_preimage q hc hp (Y.subgroupOf C₀) hYo hv
  have hcNG : (c : G) ∈ normalizer (Y : Set G) := by
    rw [mem_normalizer_iff] at hcN ⊢
    intro y
    constructor
    · intro hy
      exact (hcN ⟨y, hYJ.trans (d.centralizer_le_distinguished_centralizer) hy⟩).mp hy
    · intro hy
      have hyC : y ∈ C₀ := by
        have hh := (C₀).mul_mem ((C₀).mul_mem ((C₀).inv_mem c.property)
          (hYJ.trans (d.centralizer_le_distinguished_centralizer) hy)) c.property
        simpa only [inv_mul_cancel_left, mul_inv_cancel_right, mul_assoc, inv_mul_cancel, mul_one] using hh
      exact (hcN ⟨y, hyC⟩).mpr hy
  have hxAJ : (c : G) ∈ A ⊔ J := d.normalizer_inf_centralizer_eq ▸
    (show (c : G) ∈ normalizer (L : Set G) ⊓ centralizer (A : Set G) from
      ⟨d.normalizer_control_of_le_centralizer Y hYJ hY hcNG, c.property.2⟩)
  have hn : J ≤ normalizer (A : Set G) :=
    (centralizer_le d.distinguished_le).trans (Subgroup.centralizer_le_normalizer (A : Set G))
  rw [← SetLike.mem_coe, coe_mul_of_right_le_normalizer_left A J hn] at hxAJ
  obtain ⟨a, ha, j, hj, he⟩ := hxAJ
  let ac : C₀ := ⟨a, distinguished_le_centralizer d ha⟩
  let jc : C₀ := ⟨j, d.centralizer_le_distinguished_centralizer hj⟩
  have hqa : q ac = 1 := by
    apply show ac ∈ q.ker → q ac = 1 from id
    rw [hk]
    exact ha
  have hprod : ac * jc = c := Subtype.ext he
  refine ⟨jc, hj, ?_⟩
  rw [← hprod, map_mul, hqa, one_mul]

/-- The normalizer of an odd subgroup's image lies in the actual image of J
in C₀/A, the source equality needed in (15D). -/
public theorem Context.centralizer_quotient_odd_normalizer
    (Y : Subgroup G) (hYJ : Y ≤ J) (hY : Y ≠ ⊥) (ho : Odd (Nat.card Y)) :
    let : ((A).subgroupOf C₀).Normal :=
      normal_subgroupOf_of_le_normalizer (by
        rw [distinguishedClosure_normalizer d.minimal.disconnected]
        exact inf_le_left)
    let q := QuotientGroup.mk' ((A).subgroupOf C₀)
    normalizer ((Y.subgroupOf C₀).map q : Set (C₀ ⧸ (A).subgroupOf C₀)) ≤
      ((J).subgroupOf C₀).map q := by
  let : ((A).subgroupOf C₀).Normal :=
    normal_subgroupOf_of_le_normalizer (by
        rw [distinguishedClosure_normalizer d.minimal.disconnected]
        exact inf_le_left)
  exact quotient_normalizer_le_image_J d (QuotientGroup.mk' _) (QuotientGroup.mk'_surjective _)
    (QuotientGroup.ker_mk' _) Y hYJ hY ho

/-- Every involution in this quotient normalizer has an involution lift in J,
with the literal quotient map and subtype inclusion. -/
public theorem Context.centralizer_quotient_involution_lift
    (Y : Subgroup G) (hYJ : Y ≤ J) (hY : Y ≠ ⊥) (ho : Odd (Nat.card Y)) :
    let : ((A).subgroupOf C₀).Normal :=
      normal_subgroupOf_of_le_normalizer (by
        rw [distinguishedClosure_normalizer d.minimal.disconnected]
        exact inf_le_left)
    let q := QuotientGroup.mk' ((A).subgroupOf C₀)
    ∀ v : C₀ ⧸ (A).subgroupOf C₀, PFAppendixIII.IsInvolution v →
      v ∈ normalizer ((Y.subgroupOf C₀).map q : Set (C₀ ⧸ (A).subgroupOf C₀)) →
      ∃ j : J, PFAppendixIII.IsInvolution j ∧ q (inclusion (d.centralizer_le_distinguished_centralizer) j) = v := by
  let : ((A).subgroupOf C₀).Normal :=
    normal_subgroupOf_of_le_normalizer (by
        rw [distinguishedClosure_normalizer d.minimal.disconnected]
        exact inf_le_left)
  let q := QuotientGroup.mk' ((A).subgroupOf C₀)
  dsimp only
  intro v hi hv
  obtain ⟨c, hcJ, he⟩ := d.centralizer_quotient_odd_normalizer Y hYJ hY ho hv
  let j : J := ⟨c, hcJ⟩
  let f := q.comp (inclusion (d.centralizer_le_distinguished_centralizer))
  have hf : Function.Injective f := centralizer_quotient_injective_on_J d q (QuotientGroup.ker_mk' _)
  have hj : f j = v := he
  refine ⟨j, ⟨?_, ?_⟩, he⟩
  · intro heq
    exact hi.ne_one (hj.symm.trans (heq ▸ f.map_one))
  · apply hf
    rw [map_pow, hj, hi.sq_eq_one, map_one]

private theorem quotient_involution_conjugate_lift
    {Q : Type u} [Group Q] [Finite Q] (q : C₀ →* Q) (hq : Function.Surjective q)
    (hk : q.ker = (A).subgroupOf C₀) {v : Q}
    (hv : PFAppendixIII.IsInvolution v) (hvcore : v ∉ pCore 2 Q) :
    ∃ j : J, PFAppendixIII.IsInvolution j ∧
      IsConj v (q (inclusion d.centralizer_le_distinguished_centralizer j)) := by
  let f := q.comp (inclusion d.centralizer_le_distinguished_centralizer)
  have hf : Function.Injective f := centralizer_quotient_injective_on_J d q hk
  obtain ⟨p, hp, hp2, y, hyo, hvi⟩ :=
    involution_outside_twoCore_inverts_odd_prime v hv hvcore
  let JQ := ((J).subgroupOf C₀).map q
  have hindex : JQ.index ∣ (2 ^ n) ^ 3 := by
    apply dvd_trans (((J).subgroupOf C₀).index_map_dvd hq)
    change (J).relIndex C₀ ∣ (2 ^ n) ^ 3
    exact d.centralizer_index_dvd
  have hpindex : ¬ p ∣ JQ.index := by
    intro hpJ
    have hptwo := hp.dvd_of_dvd_pow (hp.dvd_of_dvd_pow (hpJ.trans hindex))
    exact hp2 ((Nat.dvd_prime Nat.prime_two).mp hptwo |>.resolve_left hp.ne_one)
  obtain ⟨g, hg⟩ := Theory.GroupAction.exists_conjugate_mem_of_prime_order
    JQ hp hyo hpindex
  let e := MulAut.conj g⁻¹
  let w := e v
  let x := e y
  obtain ⟨c, hcJ, hc⟩ := hg
  let j : J := ⟨c, hcJ⟩
  have hjx : f j = x := by
    change q c = x
    simpa only [x, e, MulAut.conj_apply, inv_inv] using hc
  have hxorder : orderOf x = p := (orderOf_injective e.toMonoidHom e.injective y).trans hyo
  have hjorder : orderOf j = p := by
    rw [← orderOf_injective f hf j, hjx, hxorder]
  let Y := zpowers (j : G)
  have hYJ : Y ≤ J := zpowers_le.mpr j.property
  have hYorder : Nat.card Y = p := by
    rw [Nat.card_zpowers]
    exact orderOf_submonoid j |>.symm ▸ hjorder
  have hY : Y ≠ ⊥ := by
    intro hb
    have hh := hYorder
    rw [hb, card_bot] at hh
    exact hp.ne_one hh.symm
  have hYodd : Odd (Nat.card Y) := hYorder.symm ▸ hp.odd_of_ne_two hp2
  have hYsub : Y.subgroupOf C₀ = zpowers c := by
    apply map_injective (C₀).subtype_injective
    rw [map_subgroupOf_eq_of_le (hYJ.trans d.centralizer_le_distinguished_centralizer),
      MonoidHom.map_zpowers]
    rfl
  have hYimage : (Y.subgroupOf C₀).map q = zpowers x := by
    rw [hYsub, MonoidHom.map_zpowers]
    congr 1
  have hw : PFAppendixIII.IsInvolution w :=
    BenderSuzuki.IsInvolution.map_of_injective hv e.toMonoidHom e.injective
  have hInv : w * x * w⁻¹ = x⁻¹ := by
    have hh : v * y * v⁻¹ = y⁻¹ := by
      simpa only [rightConjugateElem, hv.inv_eq_self] using hvi
    simpa only [map_mul, map_inv] using congrArg e hh
  have hwN : w ∈ normalizer ((Y.subgroupOf C₀).map q : Set Q) := by
    rw [hYimage]
    exact theorem4b_mem_normalizer_zpowers_of_inverts hw hInv
  obtain ⟨a, haJ, ha⟩ := quotient_normalizer_le_image_J d q hq hk Y hYJ hY hYodd hwN
  let k : J := ⟨a, haJ⟩
  have hkimage : f k = w := ha
  have hki : PFAppendixIII.IsInvolution k := by
    refine ⟨?_, ?_⟩
    · intro hke
      exact hw.ne_one (hkimage.symm.trans (hke ▸ f.map_one))
    · apply hf
      rw [map_pow, hkimage, hw.sq_eq_one, map_one]
  refine ⟨k, hki, ?_⟩
  apply isConj_iff.mpr
  refine ⟨g⁻¹, ?_⟩
  exact hkimage.symm

/-- Baer–Suzuki and the source index (15B) put every quotient involution
outside its two-core in the conjugacy class of an actual involution of J.
This proves the lifting step (15D), retaining only the earlier quotient
2-core premise when it is applied to an arbitrary nonidentity involution. -/
public theorem Context.centralizer_quotient_involution_conjugate_lift :
    let : ((A).subgroupOf C₀).Normal :=
      normal_subgroupOf_of_le_normalizer (by
        rw [distinguishedClosure_normalizer d.minimal.disconnected]
        exact inf_le_left)
    let q := QuotientGroup.mk' ((A).subgroupOf C₀)
    ∀ v : C₀ ⧸ (A).subgroupOf C₀, PFAppendixIII.IsInvolution v → v ∉ pCore 2 _ →
      ∃ j : J, PFAppendixIII.IsInvolution j ∧
        IsConj v (q (inclusion d.centralizer_le_distinguished_centralizer j)) := by
  let : ((A).subgroupOf C₀).Normal :=
    normal_subgroupOf_of_le_normalizer (by
      rw [distinguishedClosure_normalizer d.minimal.disconnected]
      exact inf_le_left)
  dsimp only
  intro v hv hcore
  exact quotient_involution_conjugate_lift d (QuotientGroup.mk' _)
    (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _) hv hcore

end BenderSuzuki.ZD.LinearExclusion
