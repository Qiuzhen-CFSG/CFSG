module

public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Recognition.NormalReduction.Minimal
public import Theory.GroupTheory.SolvableNormalAbelian
public import Theory.GroupTheory.SolvableRadical.AbelianCharacteristic.Elementary
public import Theory.Representation.NormalPSubgroupKernel
public import Theory.GroupAction.OddInversePairDisplacement
public import Mathlib.LinearAlgebra.GeneralLinearGroup.Basic
public import Mathlib.GroupTheory.FixedPointFree

/-!
# Small-prime minimal normal actors in 15.3.58

The characteristic elementary subgroup of a solvable minimal normal group
is the whole group. A normal two-group acts trivially in binary irreducible
degree, contradicting faithfulness. For a normal three-group, the three-free
centralizer makes conjugation by the marked involution fixed-point-free,
hence inversion. The inverse-pair norm identity identifies the kernel and
range of the involution displacement; rank-nullity gives degree twice rank.
With the source degree and rank this forces s = 0.

All normality is relative to the acting group. No classification theorem or
solvability conclusion is an input.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), p.1149;
compare D.2.11, p.183.
-/

public section
open Subgroup
open scoped IsMulCommutative

namespace CFSG.Quasithin.Chapter15.Section03.Nonabelian.Recognition.NormalReduction
variable {G : Type*} [Group G] [Finite G]

/-- A solvable minimal normal subgroup is elementary abelian for an actual prime. -/
theorem minimalNormal_solvable_elementary (K : Subgroup G) (hK : IsMinimalNormal K) [Group.IsSolvable K] :
    ∃ p : ℕ, p.Prime ∧ IsElementaryAbelian p K := by
  let : K.Normal := hK.1
  let : Nontrivial K := (Subgroup.nontrivial_iff_ne_bot K).mpr hK.2.1
  obtain ⟨A, hAchar, hAcomm, hAne⟩ := Group.exists_nontrivial_abelian_characteristic K
  let := hAchar
  let := hAcomm
  obtain ⟨p, hp, E, hEA, hEchar, hEelem, hEne⟩ :=
    Subgroup.exists_elementaryAbelian_characteristic_le A hAne
  let : Fact p.Prime := ⟨hp⟩
  let := hEchar
  let := hEelem
  have hn : (E.map K.subtype).Normal := inferInstance
  have hne : E.map K.subtype ≠ ⊥ := fun he =>
    hEne ((Subgroup.map_eq_bot_iff_of_injective E K.subtype_injective).mp he)
  have heq : E.map K.subtype = K :=
    (hK.2.2 _ hn (Subgroup.map_subtype_le E)).resolve_left hne
  exact ⟨p, hp, heq ▸ IsElementaryAbelian.map K.subtype⟩

/-- Faithful binary irreducibility excludes the characteristic-two case. -/
theorem minimalNormal_not_twoGroup {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    [FiniteDimensional (ZMod 2) W]
    (ρ : Representation (ZMod 2) G W) (hρ : ρ.IsIrreducible)
    (hf : Function.Injective ρ) (K : Subgroup G) (hK : IsMinimalNormal K) :
    ¬ IsPGroup 2 K := by
  let := hK.1
  let := hρ
  intro hp
  have hle := Representation.normal_p_subgroup_le_ker ρ K hp
  rw [(MonoidHom.ker_eq_bot_iff ρ).mpr hf] at hle
  exact hK.2.1 (le_bot_iff.mp hle)
end CFSG.Quasithin.Chapter15.Section03.Nonabelian.Recognition.NormalReduction

namespace CFSG.Quasithin.Chapter15.Section03.Nonabelian.Recognition.NormalReduction
variable {G : Type*} [Group G] [Finite G]

/-- A normal p-subgroup is inverted by an involution whose centralizer has order prime to p. -/
theorem normal_pGroup_inverted_of_centralizer {p : ℕ} [Fact p.Prime] (K : Subgroup G) [K.Normal]
    (hK : IsPGroup p K) (v : G) (hv : v ^ 2 = 1)
    (hC : ¬ p ∣ Nat.card (Subgroup.centralizer ({v} : Set G))) :
    ∀ k : K, v * (k : G) * v⁻¹ = (k : G)⁻¹ := by
  let a := K.normalizerMonoidHom ⟨v, by simp [Subgroup.normalizer_eq_top]⟩
  have hf : MonoidHom.FixedPointFree a := by
    intro k hk
    by_contra hne
    have hk' : v * (k : G) * v⁻¹ = k := congrArg Subtype.val hk
    have hc : (k : G) ∈ Subgroup.centralizer ({v} : Set G) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact (mul_inv_eq_iff_eq_mul.mp hk').symm
    have hd := orderOf_dvd_natCard (⟨k, hc⟩ : Subgroup.centralizer ({v} : Set G))
    rw [← Subgroup.orderOf_coe] at hd
    have hp := hK.dvd_orderOf hne
    rw [← Subgroup.orderOf_coe] at hp
    exact hC (hp.trans hd)
  have ha : Function.Involutive a := by
    intro k
    apply Subtype.ext
    change v * (v * (k : G) * v⁻¹) * v⁻¹ = k
    have h := hv
    rw [pow_two] at h
    calc
      _ = (v * v) * (k : G) * (v * v)⁻¹ := by group
      _ = k := by rw [h]; simp
  intro k
  exact congrArg Subtype.val (congrFun (hf.coe_eq_inv_of_involutive ha) k)

/-- An inverted odd normal subgroup with no fixed vectors forces the whole degree to be twice the involution rank. -/
theorem finrank_eq_twice_displacement_of_inverted_normal {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    [FiniteDimensional (ZMod 2) W]
    (ρ : Representation (ZMod 2) G W) (hρ : ρ.IsIrreducible)
    (hf : Function.Injective ρ) (K : Subgroup G) [K.Normal] (hne : K ≠ ⊥)
    (hodd : Odd (Nat.card K)) (v : G) (hv : IsInvolution v)
    (hinv : ∀ k : K, v * (k : G) * v⁻¹ = (k : G)⁻¹) :
    Module.finrank (ZMod 2) W =
      2 * Module.finrank (ZMod 2) (LinearMap.range (ρ v - LinearMap.id)) := by
  let := hρ
  let : IsElementaryAbelian 2 (Multiplicative W) := {
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr (by
      intro x
      change (2 : ℕ) • x.toAdd = 0
      rw [← Nat.cast_smul_eq_nsmul (ZMod 2)]
      exact zero_smul (ZMod 2) x.toAdd) }
  let f : G →* MulAut (Multiplicative W) := {
    toFun g := (LinearMap.GeneralLinearGroup.toLinearEquiv (ρ.asGroupHom g)).toAddEquiv.toMultiplicative
    map_one' := by ext w; exact congrArg Multiplicative.ofAdd (LinearMap.congr_fun ρ.map_one w.toAdd)
    map_mul' g h := by ext w; exact congrArg Multiplicative.ofAdd (LinearMap.congr_fun (ρ.map_mul g h) w.toAdd) }
  let := MulDistribMulAction.compHom (Multiplicative W) f
  have hfixed : FixedPoints.subgroup K (Multiplicative W) = ⊥ := by
    apply bot_unique
    intro w hw
    change w.toAdd = 0
    by_contra hn
    have hnfix : Representation.invariants (ρ.comp K.subtype) ≠ ⊥ := by
      intro hb
      have hw' : w.toAdd ∈ Representation.invariants (ρ.comp K.subtype) := fun k =>
        congrArg Multiplicative.toAdd (hw k)
      rw [hb] at hw'
      exact hn hw'
    have hle := Representation.le_ker_of_normal_invariants_ne_bot ρ K hnfix
    rw [(MonoidHom.ker_eq_bot_iff ρ).mpr hf] at hle
    exact hne (le_bot_iff.mp hle)
  have hkr : LinearMap.ker (ρ v - LinearMap.id) = LinearMap.range (ρ v - LinearMap.id) := by
    ext w
    change ρ v w - w = 0 ↔ ∃ u, ρ v u - u = w
    rw [sub_eq_zero]
    have he := OddInversePairDisplacement.fixed_iff_exists_displacement K hodd v hv hinv
      hfixed (Multiplicative.ofAdd w)
    change ρ v w = w ↔ ∃ u : Multiplicative W, -u.toAdd + ρ v u.toAdd = w at he
    constructor
    · intro hw
      obtain ⟨u, hu⟩ := he.mp hw
      exact ⟨u.toAdd, by simpa only [sub_eq_add_neg, add_comm] using hu⟩
    · rintro ⟨u, hu⟩
      apply he.mpr
      refine ⟨Multiplicative.ofAdd u, ?_⟩
      change -u + ρ v u = w
      rw [add_comm]
      simpa only [sub_eq_add_neg] using hu
  have hd := LinearMap.finrank_range_add_finrank_ker (ρ v - LinearMap.id)
  rw [hkr] at hd
  omega
end CFSG.Quasithin.Chapter15.Section03.Nonabelian.Recognition.NormalReduction

namespace CFSG.Quasithin.Chapter15.Section03.Nonabelian.Recognition.NormalReduction
variable {G W : Type*} [Group G] [Finite G] [AddCommGroup W]
    [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]

/-- The three-group case would give degree four and hence s = 0. -/
theorem minimalNormal_not_threeGroup
    (ρ : Representation (ZMod 2) G W) (hρ : ρ.IsIrreducible)
    (hf : Function.Injective ρ) (K : Subgroup G) (hK : IsMinimalNormal K)
    (v : G) (hv : IsInvolution v) (s : ℕ) (hs : 0 < s)
    (hC : ¬ 3 ∣ Nat.card (Subgroup.centralizer ({v} : Set G)))
    (hrank : Module.finrank (ZMod 2) (LinearMap.range (ρ v - LinearMap.id)) = 2)
    (hdim : Module.finrank (ZMod 2) W = 2 * (s + 2)) :
    ¬ IsPGroup 3 K := by
  let := hK.1
  intro hthree
  have hinv := normal_pGroup_inverted_of_centralizer K hthree v hv.2 hC
  have hodd : Odd (Nat.card K) := by
    obtain ⟨n, hn⟩ := hthree.exists_card_eq
    rw [hn]
    exact Odd.pow (by decide : Odd 3)
  have hd := finrank_eq_twice_displacement_of_inverted_normal ρ hρ hf K hK.2.1 hodd v hv hinv
  rw [hrank, hdim] at hd
  omega

/-- The remaining solvable minimal normal actor is elementary abelian of prime exponent greater than three. -/
theorem minimalNormal_solvable_prime_gt_three
    (ρ : Representation (ZMod 2) G W) (hρ : ρ.IsIrreducible)
    (hf : Function.Injective ρ) (K : Subgroup G) (hK : IsMinimalNormal K)
    [Group.IsSolvable K]
    (v : G) (hv : IsInvolution v) (s : ℕ) (hs : 0 < s)
    (hC : ¬ 3 ∣ Nat.card (Subgroup.centralizer ({v} : Set G)))
    (hrank : Module.finrank (ZMod 2) (LinearMap.range (ρ v - LinearMap.id)) = 2)
    (hdim : Module.finrank (ZMod 2) W = 2 * (s + 2)) :
    ∃ p : ℕ, p.Prime ∧ 3 < p ∧ IsElementaryAbelian p K := by
  obtain ⟨p, hp, hE⟩ := minimalNormal_solvable_elementary K hK
  let := hE
  have h2 : p ≠ 2 := by
    rintro rfl
    exact minimalNormal_not_twoGroup ρ hρ hf K hK (IsElementaryAbelian.isPGroup 2 K)
  have h3 : p ≠ 3 := by
    rintro rfl
    exact minimalNormal_not_threeGroup ρ hρ hf K hK v hv s hs hC hrank hdim
      (IsElementaryAbelian.isPGroup 3 K)
  exact ⟨p, hp, by have := hp.two_le; omega, hE⟩
end CFSG.Quasithin.Chapter15.Section03.Nonabelian.Recognition.NormalReduction

