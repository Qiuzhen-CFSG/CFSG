module
public import Theory.GroupAction.FixedLineIndecomposability
public import Theory.GroupAction.CoprimeHall
public import Theory.GroupAction.NormalizingActor
public import Theory.GroupAction.FiveActionMinimalOrder
public import Theory.GroupTheory.Fitting.Centralizer
public import Theory.PPrimeCore
public import Theory.GroupTheory.Fitting.Core
public import Theory.GroupTheory.PCoreSurjective

/-!
# Two-core size from a binary fixed line

A faithful finite binary action whose two-subgroup fixes precisely a globally
fixed line has trivial odd core: coprime splitting would otherwise give two
nontrivial invariant summands, each containing that line. In a solvable actor
with order divisible by five, Fitting self-centralization then makes a
five-subgroup act nontrivially on the two-core. Orbit counting forces the
latter to have at least sixteen elements.

For an action with two-group kernel, lifting the intrinsic two-core multiplies
this bound by the kernel order. The original quintic parabolic acts on its
abelian closure with that closure contained in the kernel, yielding its
Sylow bound in the Suzuki quotient branch before path recognition.
Source application: Aschbacher--Smith 14.2.6 and14.2.20--21, pp.982,988--989;
the five-action bound is the elementary argument in Parrott (1972), p.672.
-/

public section
namespace Theory.GroupAction
open Subgroup
open scoped IsMulCommutative


/-- The faithful fixed-line action has trivial odd core. -/
theorem oddCore_eq_bot_of_fixed_line {R V : Type*} [Group R] [Finite R] [Group V] [Finite V]
    [IsElementaryAbelian 2 V] [MulDistribMulAction R V]
    (hfaith : Function.Injective (MulDistribMulAction.toMulAut R V))
    (S : Subgroup R) (hS : IsPGroup 2 S)
    (hfixed : Nat.card (FixedPoints.subgroup S V) = 2)
    (hline : ∀ r : R, ∀ v ∈ FixedPoints.subgroup S V, r • v = v) :
    pPrimeCore 2 R = ⊥ := by
  let O := pPrimeCore 2 R
  let C := FixedPoints.subgroup O V
  let W := commutatorAction O V
  have hN : (⊤ : Subgroup R) ≤ normalizer (O : Set R) := by
    rw [normalizer_eq_top]
  let hC := fixedPoints_isInvariant_of_normalizing_actor (V := V) ⊤ O hN
  let hW := commutatorAction_isInvariant_of_normalizing_actor (V := V) ⊤ O hN
  have hcop : Nat.Coprime (Nat.card O) (Nat.card V) := by
    obtain ⟨n, hn⟩ := (IsElementaryAbelian.isPGroup 2 V).exists_card_eq
    rw [hn]
    exact pPrimeCore_coprime_card.symm.pow_right n
  have hd : IsCompl C W :=
    isCompl_fixedPointSubgroup_commutatorAction_of_solvable_coprime_of_isMulCommutative
      (G := V) (A := O) (Group.isSolvable_of_comm fun x y => mul_comm x y) hcop inferInstance
  have hCne : C ≠ ⊥ := by
    intro hc
    have hh : FixedPoints.subgroup S V ≤ C := fun v hv o => hline o v hv
    have hf := bot_unique (hh.trans hc.le)
    rw [hf, card_bot] at hfixed
    omega
  have hw : W = ⊥ :=
    (invariant_disjoint_of_fixed_line S hS hfixed C W
      (fun r v hv => (hC.invariant ⟨r, mem_top r⟩ v).mp hv)
      (fun r v hv => (hW.invariant ⟨r, mem_top r⟩ v).mp hv) hd.disjoint).resolve_left hCne
  have hc : C = ⊤ := by simpa only [hw, sup_bot_eq] using hd.sup_eq_top
  apply bot_unique
  intro o ho
  apply hfaith
  ext v
  have hv : v ∈ C := hc ▸ mem_top v
  simpa [MulDistribMulAction.toMulAut_apply] using hv ⟨o, ho⟩

/-- A solvable group with trivial odd core and order divisible by five has a two-core of order at least sixteen. -/
theorem sixteen_le_twoCore_of_five_dvd {R : Type*} [Group R] [Finite R]
    (hsolv : Group.IsSolvable R) (hodd : pPrimeCore 2 R = ⊥)
    (hfive : 5 ∣ Nat.card R) : 16 ≤ Nat.card (pCore 2 R) := by
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 5 hfive
  let P := zpowers x
  let K := pCore 2 R
  let : MulDistribMulAction P K := conjMulDistribMulActionOfLeNormalizer P K (by
    rw [normalizer_eq_top]; exact le_top)
  have hP : Nat.card P = 5 := by rw [Nat.card_zpowers, hx]
  have hc : centralizer (K : Set R) ≤ K := by
    change centralizer (pCore 2 R : Set R) ≤ pCore 2 R
    rw [← Fitting_eq_pcore R 2 hodd]
    exact centralizer_fittingSubgroup_le_fittingSubgroup_of_solvable hsolv
  apply Theory.GroupAction.sixteen_le_card_of_five_action_nontrivial hP pCore_isPGroup
  intro hfix
  have hxC : x ∈ centralizer (K : Set R) := by
    intro k hk
    have hh : (⟨k,hk⟩ : K) ∈ FixedPoints.subgroup P K := hfix ▸ mem_top _
    have he := congrArg Subtype.val (hh ⟨x,mem_zpowers x⟩)
    change x*k*x⁻¹=k at he
    exact (mul_inv_eq_iff_eq_mul.mp he).symm
  have hxK := hc hxC
  have hd : 5 ∣ Nat.card K := by
    have ho : orderOf (⟨x,hxK⟩ : K) = 5 :=
      (orderOf_injective K.subtype K.subtype_injective _).symm.trans hx
    simpa only [ho] using orderOf_dvd_natCard (⟨x,hxK⟩ : K)
  obtain ⟨n, hn⟩ := (pCore_isPGroup (p := 2) (G := R)).exists_card_eq
  rw [hn] at hd
  exact (by decide : ¬ 5 ∣ 2) ((Nat.Prime.dvd_of_dvd_pow (by decide)) hd)

/-- Lifting the action image multiplies the sixteen bound by the two-group kernel. -/
theorem core_lower_of_fixed_line {H V : Type*} [Group H] [Finite H]
    [Group V] [Finite V] [IsElementaryAbelian 2 V] [MulDistribMulAction H V]
    (hsolv : Group.IsSolvable H)
    (S : Sylow 2 H)
    (hfixed : Nat.card (FixedPoints.subgroup S V) = 2)
    (hline : ∀ h : H, ∀ v ∈ FixedPoints.subgroup S V, h • v = v)
    (hker : IsPGroup 2 (MulDistribMulAction.toMulAut H V).ker)
    (hfive : 5 ∣ Nat.card H) :
    16 * Nat.card (MulDistribMulAction.toMulAut H V).ker ≤ Nat.card (pCore 2 H) := by
  let f := MulDistribMulAction.toMulAut H V
  let R := f.range
  let q : H →* R := f.rangeRestrict
  let P := S.mapSurjective f.rangeRestrict_surjective
  have hkerq : IsPGroup 2 q.ker := by
    change IsPGroup 2 f.rangeRestrict.ker
    rw [MonoidHom.ker_rangeRestrict]
    exact hker
  have hf : Function.Injective (MulDistribMulAction.toMulAut R V) := by
    intro a b hab
    apply Subtype.ext
    exact hab
  have hfix : FixedPoints.subgroup P V = FixedPoints.subgroup S V := by
    ext v
    constructor
    · intro hv s
      exact hv ⟨q s, mem_map_of_mem q s.property⟩
    · intro hv r
      obtain ⟨s, hs, he⟩ := r.property
      have hh := hv ⟨s, hs⟩
      change (r : R) • v = v
      rw [←he]
      exact hh
  have hlineR : ∀ r : R, ∀ v ∈ FixedPoints.subgroup P V, r • v = v := by
    intro r v hv
    rw [hfix] at hv
    obtain ⟨h, rfl⟩ := f.rangeRestrict_surjective r
    exact hline h v hv
  have hodd := oddCore_eq_bot_of_fixed_line hf (P : Subgroup R) P.isPGroup'
    (by rwa [hfix]) hlineR
  have hRsolv : Group.IsSolvable R := by
    let := hsolv
    exact Group.isSolvable_of_surjective f.rangeRestrict_surjective
  have hRfive : 5 ∣ Nat.card R := by
    have hh := q.ker.card_mul_index
    rw [index_ker, q.range_eq_top_of_surjective f.rangeRestrict_surjective, card_top] at hh
    have hdiv : 5 ∣ Nat.card q.ker * Nat.card R := hh.symm ▸ hfive
    apply (Nat.Prime.dvd_mul (by decide)).mp hdiv |>.resolve_left
    obtain ⟨n, hn⟩ := hkerq.exists_card_eq
    rw [hn]
    exact fun h => (by decide : ¬ 5 ∣ 2) ((Nat.Prime.dvd_of_dvd_pow (by decide)) h)
  have hsize := sixteen_le_twoCore_of_five_dvd hRsolv hodd hRfive
  rw [q.card_pCore_of_ker_isPGroup f.rangeRestrict_surjective hkerq]
  have hkcard : Nat.card q.ker = Nat.card f.ker := by
    change Nat.card f.rangeRestrict.ker = Nat.card f.ker
    rw [MonoidHom.ker_rangeRestrict]
  rw [hkcard, mul_comm (Nat.card f.ker)]
  exact Nat.mul_le_mul_right _ hsize

end Theory.GroupAction
