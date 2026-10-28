module

public import Theory.SpecificGroups.PSL3.EvenInnerCentralizers.Decomposition
public import Theory.GroupTheory.QuaternionCentralProductResidualRecognition.Residual
public import Theory.PGroupCore
public import Theory.NumberTheory.BinarySignedTorus
public import Mathlib.GroupTheory.Complement
public import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-!
# Cores and residuals of the marked binary PSL₃ centralizer

For the actual highest-root centralizer, the faithful unitriangular image is a
normal Sylow two-subgroup. The diagonal torus complements it, with the cube-root
scalar kernel retained; hence its index is `(2 ^ n - 1) / 3` in the source range.

For `n > 3`, an actual field unit of prime order greater than three acts with
nontrivial cubic weights on both simple roots. Odd torus elements lie in the
two-residual, their scalar commutators supply the simple roots, and commutators
of these roots supply the center. Thus the two-residual is the whole centralizer.
The same actor supplies the required prime-to-p residual containment. Transport
uses the genuine equivalence from the top subgroup, not just equality of orders.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
manuscript of 1 March 2004, the inner linear case in the proof of 16.4.8,
printed p.1188. Arbitrary-involution conjugacy and ambient prime rank are separate.
-/

public section

open Matrix.PSL3Even.UnipotentGeometry
open Subgroup
namespace Matrix.PSL3.EvenInnerCentralizers.MarkedInvariants
variable (F : Type*) [Field F]

/-- The actual unitriangular image is normal in the marked centralizer. -/
theorem unipotent_normal [CharP F 2] : (unipotentInCentralizer F).range.Normal := by
  constructor
  rintro x ⟨u, rfl⟩ g
  obtain ⟨a, v, rfl⟩ := centralizer_factorization F g
  have he : (torus F a * unipotentInCentralizer F v) * unipotentInCentralizer F u *
      (torus F a * unipotentInCentralizer F v)⁻¹ =
      torus F a * unipotentInCentralizer F (v * u * v⁻¹) * (torus F a)⁻¹ := by
    simp only [map_mul, map_inv]
    group
  rw [he, torus_conjugate]
  exact ⟨_, rfl⟩

/-- Exactly the cube roots of unity vanish in the projective torus. -/
theorem torus_ker : (torus F).ker = (powMonoidHom 3 : Fˣ →* Fˣ).ker := by
  ext a
  exact torus_eq_one_iff F a

/-- The projective torus order, retaining the scalar divisor. -/
theorem torus_card [Finite F] :
    Nat.card (torus F).range = (Nat.card F - 1) / (Nat.card F - 1).gcd 3 := by
  rw [← Subgroup.index_ker, torus_ker, IsCyclic.index_powMonoidHom_ker, Nat.card_units]

/-- Faithfulness of the unitriangular embedding gives its order. -/
theorem unipotent_card [Finite F] :
    Nat.card (unipotentInCentralizer F).range = Nat.card F ^ 3 := by
  rw [← Nat.card_congr (MonoidHom.ofInjective (unipotentInCentralizer_injective F)).toEquiv,
    card_U]

/-- The unitriangular image is a two-group over a binary field. -/
theorem unipotent_isTwoGroup [Finite F] {n : ℕ} (hF : Nat.card F = 2 ^ n) :
    IsPGroup 2 (unipotentInCentralizer F).range := by
  apply IsPGroup.of_card (n := n * 3)
  rw [unipotent_card, hF, pow_mul]

/-- The multiplicative group of a binary field has odd order. -/
theorem units_odd {n : ℕ} (hF : Nat.card F = 2 ^ n) (hn : 0 < n) :
    Odd (Nat.card Fˣ) := by
  rw [Nat.card_units, hF, Nat.odd_iff]
  have hp : 0 < (2:ℕ)^n := pow_pos (by decide) _
  have hd := Nat.mod_eq_zero_of_dvd (dvd_pow_self 2 (Nat.ne_of_gt hn))
  omega

private theorem binary_char [Finite F] {n : ℕ} (hF : Nat.card F = 2 ^ n)
    (hn : 0 < n) : ringChar F = 2 := by
  let := Fintype.ofFinite F
  apply FiniteField.even_card_iff_char_two.mpr
  rw [← Nat.card_eq_fintype_card, hF]
  exact Nat.mod_eq_zero_of_dvd (dvd_pow_self 2 (Nat.ne_of_gt hn))

/-- The actual torus and unitriangular image are complementary subgroups. -/
theorem torus_complement [Finite F] {n : ℕ}
    (hF : Nat.card F = 2 ^ n) (hn : 0 < n) :
    (torus F).range.IsComplement' (unipotentInCentralizer F).range := by
  let : CharP F 2 := ringChar.of_eq (binary_char F hF hn)
  have hc : Nat.Coprime (Nat.card (torus F).range)
      (Nat.card (unipotentInCentralizer F).range) := by
    rw [unipotent_card, hF, ← pow_mul]
    exact ((units_odd F hF hn).of_dvd_nat (Subgroup.card_range_dvd (torus F))).coprime_two_right.pow_right _
  refine ⟨Subgroup.mul_injective_of_disjoint (Subgroup.disjoint_of_coprime_natCard hc), ?_⟩
  intro g
  obtain ⟨a, u, he⟩ := centralizer_factorization F g
  exact ⟨(⟨torus F a, ⟨a, rfl⟩⟩, ⟨unipotentInCentralizer F u, ⟨u, rfl⟩⟩), he.symm⟩

/-- The unitriangular index is the source quotient order. -/
theorem unipotent_index [Finite F] {n : ℕ}
    (hF : Nat.card F = 2 ^ n) (hn : 0 < n) (hmod : 2 ^ n % 3 = 1) :
    (unipotentInCentralizer F).range.index = (2 ^ n - 1) / 3 := by
  rw [(torus_complement F hF hn).index_eq_card, torus_card, hF]
  have hd : 3 ∣ 2 ^ n - 1 := Nat.dvd_of_mod_eq_zero (by omega)
  rw [Nat.gcd_eq_right hd]

/-- The two-core is exactly the faithfully embedded unitriangular group. -/
theorem twoCore_eq_unipotent [Finite F] {n : ℕ}
    (hF : Nat.card F = 2 ^ n) (hn : 0 < n) :
    pCore 2 (centralizer F) = (unipotentInCentralizer F).range := by
  let : CharP F 2 := ringChar.of_eq (binary_char F hF hn)
  let := unipotent_normal F
  have hu := unipotent_isTwoGroup F hF
  have ho : Odd (unipotentInCentralizer F).range.index := by
    rw [(torus_complement F hF hn).index_eq_card]
    exact (units_odd F hF hn).of_dvd_nat (Subgroup.card_range_dvd (torus F))
  exact le_antisymm (pCore_isPGroup.le_sylow_of_normal (hu.toSylow (by simpa using ho.not_two_dvd_nat)))
    (le_sSup ⟨inferInstance, hu⟩)

/-- The marked centralizer modulo its two-core has order `(2 ^ n - 1) / 3`. -/
theorem twoCore_index [Finite F] {n : ℕ}
    (hF : Nat.card F = 2 ^ n) (hn : 0 < n) (hmod : 2 ^ n % 3 = 1) :
    (pCore 2 (centralizer F)).index = (2 ^ n - 1) / 3 := by
  rw [twoCore_eq_unipotent F hF hn, unipotent_index F hF hn hmod]

/-- Only the marked centralizer is counted: a cubic two-part times the projective torus. -/
theorem centralizer_card [Finite F] {n : ℕ}
    (hF : Nat.card F = 2 ^ n) (hn : 0 < n) (hmod : 2 ^ n % 3 = 1) :
    Nat.card (centralizer F) = 2 ^ (n * 3) * ((2 ^ n - 1) / 3) := by
  rw [← (unipotentInCentralizer F).range.card_mul_index,
    unipotent_card, hF, unipotent_index F hF hn hmod, pow_mul]

private theorem exists_prime_actor [Finite F] {p : ℕ}
    (hp : p.Prime) (hp3 : 3 < p) (hpd : p ∣ Nat.card F - 1) :
    ∃ a : Fˣ, a ^ p = 1 ∧ a ^ 3 ≠ 1 := by
  let : Fact p.Prime := ⟨hp⟩
  obtain ⟨a, ha⟩ := exists_prime_orderOf_dvd_card' (G := Fˣ) p (by rwa [Nat.card_units])
  refine ⟨a, ha ▸ pow_orderOf_eq_one a, ?_⟩
  intro h
  have hd : p ∣ 3 := ha ▸ orderOf_dvd_of_pow_eq_one h
  have := Nat.le_of_dvd (by decide : 0 < 3) hd
  omega

/-- Every prime greater than three dividing the field-unit order supplies an actual
scalar actor generating the unitriangular image in the prime-to-p residual. -/
theorem unipotent_le_primeToResidual [Finite F] {p : ℕ}
    (hp : p.Prime) (hp3 : 3 < p) (hpd : p ∣ Nat.card F - 1) :
    (unipotentInCentralizer F).range ≤ primeToResidual p (centralizer F) := by
  obtain ⟨a, ha, hcube⟩ := exists_prime_actor F hp hp3 hpd
  exact unipotent_le_primeToResidual_of_torus F p a (k := 1) (by simpa using ha) hcube

private theorem unipotent_le_normal_of_torus (N : Subgroup (centralizer F)) [N.Normal]
    (a : Fˣ) (ha : torus F a ∈ N) (hcube : a ^ 3 ≠ 1) :
    (unipotentInCentralizer F).range ≤ N := by
  have hfirst : (a : F)^3 ≠ 1 := fun h => hcube (Units.ext h)
  have hsecond : (↑a⁻¹ : F)^3 ≠ 1 := by
    intro h
    have hi : (a⁻¹)^3 = 1 := Units.ext h
    have hh := congrArg Inv.inv hi
    exact hcube (by simpa only [← inv_pow, inv_inv, inv_one] using hh)
  apply range_le_of_roots F (unipotentInCentralizer F) N
  · apply scalar_root_le_normal N _ (torus F a) ha ((a : F)^3) hfirst
    intro x
    simpa only [MonoidHom.comp_apply, firstRoot, MonoidHom.coe_mk, OneHom.coe_mk,
      toAdd_ofAdd, mul_zero] using torus_conjugate F a (⟨x, 0, 0⟩ : U F)
  · apply scalar_root_le_normal N _ (torus F a) ha ((↑a⁻¹ : F)^3) hsecond
    intro x
    simpa only [MonoidHom.comp_apply, secondRoot, MonoidHom.coe_mk, OneHom.coe_mk,
      toAdd_ofAdd, mul_zero] using torus_conjugate F a (⟨0, x, 0⟩ : U F)

/-- Odd torus elements and their scalar commutators generate the entire two-residual. -/
theorem twoResidual_eq_top [Finite F] {n : ℕ}
    (hF : Nat.card F = 2 ^ n) (hn : 3 < n) (hmod : 2 ^ n % 3 = 1) :
    pResidual 2 (centralizer F) = ⊤ := by
  let : CharP F 2 := ringChar.of_eq (binary_char F hF (by omega))
  have ht (a : Fˣ) : torus F a ∈ pResidual 2 (centralizer F) := by
    apply mem_pResidual_of_orderOf_coprime
    exact (units_odd F hF (by omega)).coprime_two_left.of_dvd_right
      ((orderOf_map_dvd (torus F) a).trans (orderOf_dvd_natCard a))
  obtain ⟨_, p, hp, hp3, hd⟩ := Nat.BinarySignedTorus.linear_quotient hn hmod
  have h3 : 3 ∣ 2 ^ n - 1 := Nat.dvd_of_mod_eq_zero (by omega)
  obtain ⟨a, _, hcube⟩ := exists_prime_actor F hp hp3 (by
    rw [hF]
    exact hd.trans (Nat.div_dvd_of_dvd h3))
  have hu := unipotent_le_normal_of_torus F (pResidual 2 (centralizer F)) a (ht a) hcube
  apply top_unique
  intro g _
  obtain ⟨b, u, rfl⟩ := centralizer_factorization F g
  exact (pResidual 2 (centralizer F)).mul_mem (ht b) (hu ⟨u, rfl⟩)

/-- The two-residual has the same exact two-core index as the centralizer. -/
theorem residual_twoCore_index [Finite F] {n : ℕ}
    (hF : Nat.card F = 2 ^ n) (hn : 3 < n) (hmod : 2 ^ n % 3 = 1) :
    (pCore 2 (pResidual 2 (centralizer F))).index = (2 ^ n - 1) / 3 := by
  rw [twoResidual_eq_top F hF hn hmod]
  have he := pCore_map_iso 2 (Subgroup.topEquiv : (⊤ : Subgroup (centralizer F)) ≃* centralizer F)
  rw [← twoCore_index F hF (by omega) hmod, ← he]
  exact (Subgroup.index_map_equiv _ Subgroup.topEquiv).symm

/-- The two-core has odd index inside the actual two-residual. -/
theorem residual_twoCore_index_odd [Finite F] {n : ℕ}
    (hF : Nat.card F = 2 ^ n) (hn : 3 < n) (hmod : 2 ^ n % 3 = 1) :
    Odd (pCore 2 (pResidual 2 (centralizer F))).index := by
  rw [residual_twoCore_index F hF hn hmod]
  exact (Nat.BinarySignedTorus.linear_quotient hn hmod).1

/-- The order of the actual two-residual in the large binary source range. -/
theorem residual_card [Finite F] {n : ℕ}
    (hF : Nat.card F = 2 ^ n) (hn : 3 < n) (hmod : 2 ^ n % 3 = 1) :
    Nat.card (pResidual 2 (centralizer F)) = 2 ^ (n * 3) * ((2 ^ n - 1) / 3) := by
  rw [twoResidual_eq_top F hF hn hmod, Nat.card_congr Subgroup.topEquiv.toEquiv]
  exact centralizer_card F hF (by omega) hmod

/-- Every prime greater than three dividing the residual order divides `2 ^ n - 1`. -/
theorem prime_dvd_sub_one_of_dvd_residual [Finite F] {n p : ℕ}
    (hF : Nat.card F = 2 ^ n) (hn : 3 < n) (hmod : 2 ^ n % 3 = 1)
    (hp : p.Prime) (hp3 : 3 < p) (hd : p ∣ Nat.card (pResidual 2 (centralizer F))) :
    p ∣ 2 ^ n - 1 := by
  rw [residual_card F hF hn hmod] at hd
  rcases hp.dvd_mul.mp hd with htwo | hodd
  · have hle := Nat.le_of_dvd (by decide : 0 < 2) (hp.dvd_of_dvd_pow htwo)
    omega
  · exact hodd.trans (Nat.div_dvd_of_dvd (Nat.dvd_of_mod_eq_zero (by omega)))

/-- A prime divisor greater than three of the field-unit order generates the
two-core of the actual two-residual inside its prime-to-p residual. -/
theorem residual_twoCore_le_primeToResidual [Finite F] {n p : ℕ}
    (hF : Nat.card F = 2 ^ n) (hn : 3 < n) (hmod : 2 ^ n % 3 = 1)
    (hp : p.Prime) (hp3 : 3 < p) (hd : p ∣ 2 ^ n - 1) :
    pCore 2 (pResidual 2 (centralizer F)) ≤ primeToResidual p (pResidual 2 (centralizer F)) := by
  rw [twoResidual_eq_top F hF hn hmod]
  let e : (⊤ : Subgroup (centralizer F)) ≃* centralizer F := Subgroup.topEquiv
  have h : pCore 2 (centralizer F) ≤ primeToResidual p (centralizer F) := by
    rw [twoCore_eq_unipotent F hF (by omega)]
    exact unipotent_le_primeToResidual F hp hp3 (by rwa [hF])
  rw [← pCore_map_iso 2 e, ← map_primeToResidual e] at h
  exact (Subgroup.map_le_map_iff_of_injective e.injective).mp h

/-- The source prime exists, divides the actual residual order, and its
prime-to-p residual contains the full two-core. -/
theorem exists_prime_residual_twoCore_le [Finite F] {n : ℕ}
    (hF : Nat.card F = 2 ^ n) (hn : 3 < n) (hmod : 2 ^ n % 3 = 1) :
    ∃ p : ℕ, p.Prime ∧ 3 < p ∧ p ∣ Nat.card (pResidual 2 (centralizer F)) ∧
      pCore 2 (pResidual 2 (centralizer F)) ≤ primeToResidual p (pResidual 2 (centralizer F)) := by
  obtain ⟨_, p, hp, hp3, hd⟩ := Nat.BinarySignedTorus.linear_quotient hn hmod
  refine ⟨p, hp, hp3, ?_, residual_twoCore_le_primeToResidual F hF hn hmod hp hp3 ?_⟩
  · rw [residual_card F hF hn hmod]
    exact dvd_mul_of_dvd_right hd _
  · exact hd.trans (Nat.div_dvd_of_dvd (Nat.dvd_of_mod_eq_zero (by omega)))


end Matrix.PSL3.EvenInnerCentralizers.MarkedInvariants
