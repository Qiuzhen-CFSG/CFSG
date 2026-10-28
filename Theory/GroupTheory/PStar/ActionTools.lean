module

public import Theory.GroupTheory.PStar.Basic
public import Theory.GroupTheory.PPerfectHom
public import Theory.GroupAction.Lemmas
public import Theory.GroupAction.NormalComplement

/-!
# Tools for p-star action decomposition

The action commutator K of a p-star group is p-perfect. Indeed, modulo
O^p(K), its image is a normal p-subgroup and hence central. Each action
displacement is then a homomorphism from the p-perfect ambient group to
that central p-group, so vanishes. If K has a central Sylow subgroup,
Burnside transfer makes K a p'-group. In this case the p-group fixed-point
congruence applied to each coset proves the required fixed supplement.

These facts supply an alternative induction for GLS II, Chapter B, 5.5:
apply 5.4 to K itself, instead of selecting a minimal normal subgroup.
The same-prime invariant Sylow exists by Sylow's third theorem and the
p-group fixed-point congruence.
-/

public section

open Subgroup
open scoped Pointwise
namespace Theory.GroupTheory
variable {p : ℕ} {G A : Type*} [Group G] [Finite G] [Group A]
  [Fact p.Prime] [MulDistribMulAction A G]

/-- Action commutators in finite p-star groups are p-perfect. The acting group
need not be a p-group. -/
theorem IsPStar.isPPerfect_commutatorAction (hG : IsPStar p G) :
    IsPPerfect p (commutatorAction A G) := by
  let K := commutatorAction A G
  let _ : K.Normal := commutatorAction_normal
  let R := (pResidual p K).map K.subtype
  let q := QuotientGroup.mk' R
  let B := K.map q
  have hpB : IsPGroup p B := by
    rintro ⟨y, k, hk, rfl⟩
    obtain ⟨n, hn⟩ := isPGroup_quotient_pResidual (G := K) p
      (QuotientGroup.mk' (pResidual p K) ⟨k, hk⟩)
    refine ⟨n, Subtype.ext ?_⟩
    change q k ^ p ^ n = 1
    rw [← map_pow]
    apply (QuotientGroup.eq_one_iff _).mpr
    refine mem_map.mpr ⟨(⟨k, hk⟩ : K) ^ p ^ n, ?_, rfl⟩
    apply (QuotientGroup.eq_one_iff _).mp
    change QuotientGroup.mk' (pResidual p K) ((⟨k, hk⟩ : K) ^ p ^ n) = 1
    rwa [map_pow]
  have hB : B.Normal := inferInstance
  have hc : B ≤ center (G ⧸ R) := (hG.quotient R).normal_pSubgroup_le_center B hpB
  have hdmem (a : A) (g : G) : q (g⁻¹ * (a • g)) ∈ B :=
    mem_map_of_mem q (subset_closure ⟨a, g, mem_top g, rfl⟩)
  have hdisp (a : A) (g : G) : g⁻¹ * (a • g) ∈ R := by
    let d : G →* B := {
      toFun g := ⟨q (g⁻¹ * (a • g)), hdmem a g⟩
      map_one' := by apply Subtype.ext; simp
      map_mul' := by
        intro x y
        apply Subtype.ext
        change q ((x * y)⁻¹ * (a • (x * y))) =
          q (x⁻¹ * (a • x)) * q (y⁻¹ * (a • y))
        have hcomm := mem_center_iff.mp (hc (hdmem a x)) (q y)⁻¹
        simp only [map_mul, map_inv] at hcomm
        simp only [mul_inv_rev, smul_mul', map_mul, map_inv]
        calc
          _ = (q y)⁻¹ * ((q x)⁻¹ * q (a • x)) * q (a • y) := by group
          _ = ((q x)⁻¹ * q (a • x)) * (q y)⁻¹ * q (a • y) := by rw [hcomm]
          _ = _ := by group }
    have hd := ((pResidual_eq_top_iff p G).mp hG.1).hom_eq_one_of_isPGroup hpB d
    apply (QuotientGroup.eq_one_iff _).mp
    exact congrArg (fun f : G →* B => (f g : G ⧸ R)) hd
  have hKR : K ≤ R := (closure_le _).mpr (by
    rintro x ⟨a, g, _, rfl⟩
    exact hdisp a g)
  apply (pResidual_eq_top_iff p K).mp
  apply top_unique
  intro x _
  obtain ⟨y, hy, he⟩ := hKR x.property
  exact (Subtype.ext he : y = x) ▸ hy

end Theory.GroupTheory

namespace Theory.GroupTheory.PStarAction

/-- A p-group action stabilizes a Sylow subgroup at the same prime. -/
theorem exists_invariant_sylow_same_prime {p : ℕ} {G A : Type*} [Group G] [Finite G]
    [Group A] [Fact p.Prime] [MulDistribMulAction A G] (hA : IsPGroup p A) :
    ∃ P : Sylow p G, IsInvariant A G (P : Subgroup G) := by
  obtain ⟨P, hP⟩ := hA.nonempty_fixed_point_of_prime_not_dvd_card (Sylow p G)
    (not_dvd_card_sylow p G)
  refine ⟨P, ⟨fun a g => ?_⟩⟩
  have he (a : A) : a • (P : Subgroup G) = (P : Subgroup G) := by
    simpa only [Sylow.pointwise_smul_def] using congrArg Sylow.toSubgroup (hP a)
  constructor
  · intro hg
    have := Subgroup.smul_mem_pointwise_smul g a (P : Subgroup G) hg
    simpa only [he a] using this
  · intro hg
    have := Subgroup.smul_mem_pointwise_smul (a • g) a⁻¹ (P : Subgroup G) hg
    simpa only [he a⁻¹, inv_smul_smul] using this

/-- A p-perfect group with a central Sylow p-subgroup has order prime to p. -/
theorem coprime_card_of_central_sylow {p : ℕ} {G : Type*} [Group G] [Finite G]
    [Fact p.Prime] (hG : IsPPerfect p G) (P : Sylow p G)
    (hP : (P : Subgroup G) ≤ center G) : Nat.Coprime p (Nat.card G) := by
  obtain ⟨N, hN, hc, hq⟩ :=
    exists_normal_coprime_subgroup_and_pgroup_quotient_of_sylow_le_center_normalizer p P
      (fun x hx => ⟨P.toSubgroup.le_normalizer hx, fun y _ => mem_center_iff.mp (hP hx) y⟩)
  have ht := hG N hN hq
  simpa only [ht, Nat.card_congr Subgroup.topEquiv.toEquiv] using hc

/-- If the action commutator has order prime to the actor prime, each coset
contains a fixed point. This requires no solvability hypothesis. -/
theorem commutator_sup_fixed_eq_top_of_coprime {p : ℕ} {G A : Type*} [Group G] [Finite G]
    [Group A] [Fact p.Prime] [MulDistribMulAction A G] (hA : IsPGroup p A)
    (hcop : Nat.Coprime p (Nat.card (commutatorAction A G))) :
    commutatorAction A G ⊔ fixedPointSubgroup A G = ⊤ := by
  let K := commutatorAction A G
  let _ : K.Normal := commutatorAction_normal
  let q := QuotientGroup.mk' K
  have hq (a : A) (g : G) : q (a • g) = q g := by
    have hd : g⁻¹ * (a • g) ∈ K := subset_closure ⟨a, g, mem_top g, rfl⟩
    have he : q (g⁻¹ * (a • g)) = 1 := (QuotientGroup.eq_one_iff _).mpr hd
    exact (inv_mul_eq_one.mp (by simpa only [map_mul, map_inv] using he)).symm
  apply top_unique
  intro x _
  let T := {g : G // q g = q x}
  let e : K ≃ T := {
    toFun k := ⟨x * k, by
      have hk : q (k : G) = 1 := (QuotientGroup.eq_one_iff _).mpr k.property
      rw [map_mul, hk, mul_one]⟩
    invFun y := ⟨x⁻¹ * y, by
      apply (QuotientGroup.eq_one_iff _).mp
      change q (x⁻¹ * (y : G)) = 1
      rw [map_mul, map_inv, y.property, inv_mul_cancel]⟩
    left_inv k := Subtype.ext (by simp)
    right_inv y := Subtype.ext (by simp) }
  let _ : MulAction A T := {
    smul a y := ⟨a • (y : G), (hq a y).trans y.property⟩
    one_smul y := Subtype.ext (one_smul A (y : G))
    mul_smul a b y := Subtype.ext (mul_smul a b (y : G)) }
  have hT : ¬ p ∣ Nat.card T := by
    rw [← Nat.card_congr e]
    exact (Fact.out : p.Prime).coprime_iff_not_dvd.mp hcop
  obtain ⟨y, hy⟩ := hA.nonempty_fixed_point_of_prime_not_dvd_card T hT
  have hyfix : (y : G) ∈ fixedPointSubgroup A G := fun a => congrArg Subtype.val (hy a)
  have hk : (y : G)⁻¹ * x ∈ K := by
    apply (QuotientGroup.eq_one_iff _).mp
    change q ((y : G)⁻¹ * x) = 1
    rw [map_mul, map_inv, y.property, inv_mul_cancel]
  have hm := (K ⊔ fixedPointSubgroup A G).mul_mem
    ((show fixedPointSubgroup A G ≤ K ⊔ fixedPointSubgroup A G from le_sup_right) hyfix)
    ((show K ≤ K ⊔ fixedPointSubgroup A G from le_sup_left) hk)
  simpa only [mul_inv_cancel_left] using hm

end Theory.GroupTheory.PStarAction
