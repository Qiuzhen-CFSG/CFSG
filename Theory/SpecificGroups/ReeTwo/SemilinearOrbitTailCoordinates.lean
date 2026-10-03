module

public import Theory.SpecificGroups.ReeTwo.SemilinearExtensionData
public import Theory.SpecificGroups.ReeTwo.OrbitFrameAlgebra
public import Theory.GroupAction.FiveOrbitBinaryCoordinates

/-!
# Intrinsic coordinates on the root-displacement tail

The residual abelianization is elementary of order sixteen, with fixed-point-free
five-action. Four consecutive points in the seed orbit give binary coordinates.
Root displacement modulo the center defines an equivariant homomorphism out of
this abelianization: class-two commutator identities give multiplicativity and
the root centralizes the residual derived subgroup.

Its kernel is trivial by invariant simplicity. Otherwise the root commutators
would all be central, contradicting the derived and central orders 32 and 2.
The image therefore has order sixteen and is exactly the derived subgroup's
image modulo the center. Transporting the orbit basis proves the intrinsic
root-tail coordinates without any frame relations or recognition hypothesis.

Sources: Parrott, *A characterization of the Tits' simple group* (1972),
pp.672–674; Thompson VI, p.630. The right-commutator convention is that of
Shinoda (1975), (2.3), pp.81–82.
-/

public section
namespace ReeTwo
open Subgroup
open scoped IsMulCommutative commutatorElement

private theorem rightComm_mul_left {H : Type*} [Group H]
    (hc : ∀ x y : H, rightComm x y ∈ center H) (x y t : H) :
    rightComm (x*y) t = rightComm x t * rightComm y t := by
  have hh := mem_center_iff.mp (hc x t) y
  calc
    _ = y⁻¹ * rightComm x t * y * rightComm y t := by simp [rightComm, mul_assoc]
    _ = _ := by rw [mul_assoc y⁻¹, ← hh]; simp

variable {K A : Type*} [Group K] [Group A] [Finite K] [Finite A]

private theorem residual_quotient_data
    {ρ : A →* MulAut K} {R : Subgroup K} {t z : K} {b : R} {σ : MulAut K}
    (h : SemilinearExtensionData ρ R t z b σ)
    [MulDistribMulAction A K] [IsInvariant A K R]
    (haction : ∀ a x, a • x = ρ a x) :
    let _ := quotientMulDistribMulAction (A := A) (commutator R)
      (isInvariant_of_characteristic (commutator R))
    IsElementaryAbelian 2 (R ⧸ commutator R) ∧
      Nat.card (R ⧸ commutator R) = 16 ∧
      FixedPoints.subgroup A (R ⧸ commutator R) = ⊥ := by
  let _ : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp := IsPGroup.of_card (p := 2) (n := 9) h.residual_card
  let _ : Fact (IsPGroup 2 R) := ⟨hp⟩
  let _ : Group.IsNilpotent R := hp.isNilpotent
  have hfixed : FixedPoints.subgroup A R ≤ center R := by
    intro x hx
    exact h.fixed_central x (fun a => by
      rw [← haction]
      exact congrArg Subtype.val (hx a))
  obtain ⟨_, _, hPhi, hUpper, _, hDcard⟩ := Theory.GroupAction.parrott_twoGroup_structure
    hp h.residual_card h.residual_class.ge h.actor_card hfixed
  let _ := quotientMulDistribMulAction (A := A) (commutator R)
    (isInvariant_of_characteristic (commutator R))
  refine ⟨?_, ?_, ?_⟩
  · let _ := isElementaryAbelian_quotient_frattini (R := R) (p := 2)
    let e := QuotientGroup.quotientMulEquivOfEq hPhi
    refine { is_comm := ⟨fun x y => e.injective ?_⟩, exponent_dvd_p := ?_ }
    · simpa only [map_mul] using (mul_comm (e x) (e y))
    · exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr (fun x => by
        apply e.injective
        simpa only [map_pow, map_one] using Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
          (IsElementaryAbelian.exponent_dvd_p 2 (R ⧸ frattini R)) (e x))
  · have hc := (commutator R).index_mul_card
    change Nat.card (R ⧸ commutator R) * Nat.card (commutator R) = Nat.card R at hc
    rw [hDcard, h.residual_card] at hc
    omega
  · have hZ : center R ≤ commutator R := by
      rw [hUpper]
      simpa only [Subgroup.upperCentralSeries_one] using
        Subgroup.upperCentralSeries_mono R (show 1 ≤ 2 by decide)
    rw [fixedPoints_subgroup_quotient_eq_map_of_solvable_coprime
      (inferInstance : Group.IsSolvable R) (by rw [h.actor_card, h.residual_card]; decide)
      (commutator R) (isInvariant_of_characteristic (commutator R)),
      Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
    exact hfixed.trans hZ

private theorem displacement_coordinates
    {ρ : A →* MulAut K} {R : Subgroup K} {t z : K} {b : R} {σ : MulAut K}
    (h : SemilinearExtensionData ρ R t z b σ)
    [MulDistribMulAction A K] [IsInvariant A K R]
    (haction : ∀ a x, a • x = ρ a x) :
    ∃ F : (R ⧸ commutator R) →* (K ⧸ center K),
      (∀ x : R, F (QuotientGroup.mk' (commutator R) x) =
        rightComm (QuotientGroup.mk' (center K) x) (QuotientGroup.mk' (center K) t)) ∧
      Function.Injective F ∧ F.range = (commutator K).map (QuotientGroup.mk' (center K)) := by
  let D := commutator K
  let q := QuotientGroup.mk' (center K)
  let _ : IsElementaryAbelian 2 D := by
    change IsElementaryAbelian 2 (commutator K)
    rw [← h.derived_eq]
    exact h.derived_elementary
  have hDZ : ⁅D, (⊤ : Subgroup K)⁆ = center K := by
    change ⁅commutator K, (⊤ : Subgroup K)⁆ = center K
    rw [← h.derived_eq, h.derived_commutator, h.center_eq]
  obtain ⟨hc, _⟩ := centralQuotient_rightComm_laws D le_rfl hDZ.le
  let f : R →* (K ⧸ center K) := {
    toFun x := rightComm (q x) (q t)
    map_one' := by simp [rightComm]
    map_mul' x y := by
      change rightComm (q ((x : K) * y)) (q t) = _
      rw [map_mul, rightComm_mul_left hc] }
  have hrc (x : K) : q (rightComm x t) = rightComm (q x) (q t) := by
    simp only [rightComm, map_mul, map_inv]
  have hkill : commutator R ≤ f.ker := by
    intro x hx
    have hh := mem_centralizer_iff.mp h.root_centralizes (x : K) (mem_map_of_mem R.subtype hx)
    change rightComm (q x) (q t) = 1
    rw [← hrc]
    have hr : rightComm (x : K) t = 1 := by
      simp only [rightComm]
      calc
        _ = (t * (x : K))⁻¹ * ((x : K) * t) := by group
        _ = 1 := by rw [hh]; simp
    rw [hr, map_one]
  let F := QuotientGroup.lift (commutator R) f hkill
  have hF (x : R) : F (QuotientGroup.mk' (commutator R) x) = rightComm (q x) (q t) := rfl
  let _ := quotientMulDistribMulAction (A := A) (commutator R)
    (isInvariant_of_characteristic (commutator R))
  let _ := quotientMulDistribMulAction (A := A) (center K)
    (isInvariant_of_characteristic (center K))
  obtain ⟨hVE, hVcard, hVfix⟩ := residual_quotient_data h haction
  have hequiv (a : A) (x : R ⧸ commutator R) : F (a • x) = a • F x := by
    induction x using QuotientGroup.induction_on with | H x =>
      change rightComm (q (a • (x : K))) (q t) = a • rightComm (q x) (q t)
      have ht : a • q t = q t := by
        change q (a • t) = q t
        rw [haction, h.root_fixed]
      simp only [rightComm, smul_mul', smul_inv', ht]
      rfl
  let _ : IsInvariant A (R ⧸ commutator R) F.ker := ⟨fun a x => by
    change F x = 1 ↔ F (a • x) = 1
    rw [hequiv]
    exact ⟨fun hx => by rw [hx, smul_one],
      fun hx => smul_left_cancel a (hx.trans (smul_one a).symm)⟩⟩
  have hker : F.ker = ⊥ := by
    rcases invariant_eq_bot_or_top_of_five_actor h.actor_card hVcard hVfix F.ker with he | he
    · exact he
    · have hzero (x : R) : rightComm (q x) (q t) = 1 := by
        exact show QuotientGroup.mk' (commutator R) x ∈ F.ker from he ▸ mem_top _
      have hle : D ≤ center K := by
        change commutator K ≤ center K
        rw [← h.derived_eq, ← h.root_commutator]
        apply Subgroup.commutator_le.mpr
        intro x hx y hy
        apply (QuotientGroup.eq_one_iff _).mp
        change q ⁅x,y⁆ = 1
        rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
        have hxt : Commute (q x) (q t) := by
          have hh := hzero ⟨x,hx⟩
          change (q x)⁻¹ * (q t)⁻¹ * q x * q t = 1 at hh
          have he := congrArg (fun w => q t * q x * w) hh
          change q x * q t = q t * q x
          simpa only [mul_assoc, mul_inv_cancel_left, mul_one] using he
        obtain ⟨n, rfl⟩ := mem_zpowers_iff.mp hy
        rw [map_zpow]
        exact (hxt.zpow_right n).eq
      have hbnd := Nat.card_le_card_of_injective (Subgroup.inclusion hle)
        (Subgroup.inclusion_injective hle)
      have hd : Nat.card D = 32 := by
        change Nat.card (commutator K) = 32
        rw [← h.derived_eq]
        exact h.derived_card
      have hz : Nat.card (center K) = 2 := h.center_eq.symm ▸ h.center_card
      omega
  have hinj : Function.Injective F := (MonoidHom.ker_eq_bot_iff F).mp hker
  have hmem (x : K) : rightComm x t ∈ D := by
    simpa only [D, rightComm, commutatorElement_def, _root_.commutator_def, inv_inv] using
      (Subgroup.commutator_mem_commutator (Subgroup.mem_top x⁻¹) (Subgroup.mem_top t⁻¹))
  have hle : F.range ≤ D.map q := by
    rintro _ ⟨x,rfl⟩
    induction x using QuotientGroup.induction_on with | H x =>
      change rightComm (q x) (q t) ∈ D.map q
      rw [← hrc]
      exact mem_map_of_mem q (hmem x)
  have hZle : center K ≤ D := hDZ.symm.le.trans (commutator_le_left _ _)
  have hcard : Nat.card (D.map q) = 16 := by
    let fq := q.comp D.subtype
    have hkerq : fq.ker = (center K).subgroupOf D := by
      ext x
      exact QuotientGroup.eq_one_iff (x : K)
    have hrange : fq.range = D.map q := by simp [fq, MonoidHom.range_comp]
    have he := fq.ker.index_mul_card
    rw [Subgroup.index_ker, hrange, hkerq] at he
    have hz := Nat.card_congr (subgroupOfEquivOfLe hZle).toEquiv
    have hd : Nat.card D = 32 := by
      change Nat.card (commutator K) = 32
      rw [← h.derived_eq]
      exact h.derived_card
    have hcZ : Nat.card (center K) = 2 := h.center_eq.symm ▸ h.center_card
    rw [hz, hd, hcZ] at he
    omega
  have hFcard : Nat.card F.range = 16 := by
    rw [← Nat.card_congr (Equiv.ofBijective F.rangeRestrict
      ⟨fun _ _ he => hinj (congrArg Subtype.val he), F.rangeRestrict_surjective⟩)]
    exact hVcard
  refine ⟨F, hF, hinj, ?_⟩
  exact eq_of_le_of_card_ge hle (by rw [hFcard, hcard])

/-- The first four root displacements give unique binary coordinates on the
image of the derived subgroup modulo the center; the fifth residual orbit
point is the product of the first four modulo the derived subgroup. -/
theorem SemilinearExtensionData.orbitTailCoordinates
    {ρ : A →* MulAut K} {R : Subgroup K} {t z : K} {b : R} {σ : MulAut K}
    (h : SemilinearExtensionData ρ R t z b σ) (g : A) (hg : g ≠ 1) :
    let q := QuotientGroup.mk' (center K)
    let B := fun n : ℕ => ρ (g ^ n) (b : K)
    let u := fun i : Fin 4 => q (B i.val)
    let d := fun i : Fin 4 => rightComm (u i) (q t)
    B 4 / (B 0 * B 1 * B 2 * B 3) ∈ commutator K ∧
      Function.Injective (binaryWord4 d) ∧
      ∀ x : K, x ∈ commutator K → ∃ e : Fin 4 → Fin 2, q x = binaryWord4 d e := by
  let _ : MulDistribMulAction A K := MulDistribMulAction.compHom K ρ
  let _ : IsInvariant A K R := ⟨fun a x => (h.invariant a x).symm⟩
  have haction : ∀ a x, a • x = ρ a x := fun _ _ => rfl
  let _ := quotientMulDistribMulAction (A := A) (commutator R)
    (isInvariant_of_characteristic (commutator R))
  obtain ⟨hVE, hVcard, hVfix⟩ := residual_quotient_data h haction
  let _ := hVE
  let p := QuotientGroup.mk' (commutator R)
  have hb : p b ≠ 1 := by
    intro hh
    exact h.seed_outside ((QuotientGroup.eq_one_iff b).mp hh)
  obtain ⟨hrel, hcoord⟩ := Theory.GroupAction.five_orbit_binary_coordinates h.actor_card hVcard hVfix (p b) hb g hg
  change Function.Bijective (binaryWord4 (fun i : Fin 4 => g ^ i.val • p b)) at hcoord
  obtain ⟨F, hF, hinj, hrange⟩ := displacement_coordinates h haction
  let q := QuotientGroup.mk' (center K)
  let v := fun i : Fin 4 => g ^ i.val • p b
  let d := fun i : Fin 4 => rightComm (q (ρ (g ^ i.val) (b : K))) (q t)
  have hmap (e : Fin 4 → Fin 2) : F (binaryWord4 v e) = binaryWord4 d e := by
    have hv (i : Fin 4) : F (v i) = d i := hF (g ^ i.val • b)
    simp only [binaryWord4, map_mul, map_pow, hv]
  refine ⟨?_, ?_, ?_⟩
  · have hh : (g ^ 4 • b) / (b * (g • b) * (g ^ 2 • b) * (g ^ 3 • b)) ∈ commutator R := by
      apply QuotientGroup.eq_iff_div_mem.mp
      change p (g ^ 4 • b) = p (b * (g • b) * (g ^ 2 • b) * (g ^ 3 • b))
      simp only [map_mul]
      exact hrel
    have hm := mem_map_of_mem R.subtype hh
    rw [h.derived_eq] at hm
    change ρ (g ^ 4) (b : K) /
      ((b : K) * ρ g (b : K) * ρ (g ^ 2) (b : K) * ρ (g ^ 3) (b : K)) ∈ commutator K at hm
    simpa only [pow_zero, map_one, MulAut.one_apply, pow_one] using hm
  · intro e f hef
    apply hcoord.injective
    apply hinj
    exact (hmap e).trans (hef.trans (hmap f).symm)
  · intro x hx
    have hm : q x ∈ F.range := hrange.symm ▸ mem_map_of_mem q hx
    obtain ⟨w, hw⟩ := hm
    obtain ⟨e, he⟩ := hcoord.surjective w
    refine ⟨e, ?_⟩
    calc
      q x = F w := hw.symm
      _ = F (binaryWord4 v e) := congrArg F he.symm
      _ = binaryWord4 d e := hmap e

end ReeTwo
