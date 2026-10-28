module

public import Theory.SpecificGroups.G2.MultiplierOrdinary.OddQuadraticTorus.RankOne
public import Theory.SpecificGroups.G2.FiniteUniversalCover
public import Theory.AtlasPort.LinearGroups.G2.Order
public import Theory.GroupTheory.CentralExtensionPartialInversion

/-!
# Central-product quadratic tori and transfer in G₂

A cyclic product of order (q+1)² mapping to the actual octonion model with
kernel of exponent two has index prime to every r>3 dividing q+1. A Sylow
subgroup of its image therefore gives a full Sylow subgroup of G₂. Partial
inversion kills the commutator of its lifts in any perfect central cover.

The central-product kernel is retained in the index formula. The final
application constructs the norm-one torus and its partial inverter from an
actual homomorphism SL₂ × SL₂ → G₂ with kernel of exponent two. Construction
of that geometric homomorphism is supplied by `OrthogonalRankOne` in the
parent module.
Source: Aschbacher–Smith I.1.1–4 and GLS III §6.1; the G₂ order formula uses
the licensed ATLAS octonion model (LICENSES/ATLAS.txt).
-/

public section

open Subgroup Matrix

namespace Atlas.G2.MultiplierOrdinary.OddQuadraticTorus

variable {F : Type*} [Field F] [Finite F]

/-- The quadratic product image index, retaining its possibly nontrivial kernel. -/
theorem quadratic_index {C : Type*} [Group C] [Finite C]
    (ι : C × C →* Model F) (hC : Nat.card C = Nat.card F + 1) :
    ι.range.index = Nat.card ι.ker *
      (Nat.card F ^ 6 * (Nat.card F - 1) ^ 2 *
        (Nat.card F ^ 4 + Nat.card F ^ 2 + 1)) := by
  have hk := ι.ker.card_mul_index
  rw [index_ker, Nat.card_prod, hC, ← pow_two] at hk
  have h2 : Nat.card F ^ 2 - 1 = (Nat.card F - 1) * (Nat.card F + 1) := by
    simpa [mul_comm] using Nat.sq_sub_sq (Nat.card F) 1
  have h6 : Nat.card F ^ 6 - 1 =
      (Nat.card F ^ 2 - 1) * (Nat.card F ^ 4 + Nat.card F ^ 2 + 1) := by
    apply Nat.sub_eq_of_eq_add
    have hq : 1 ≤ Nat.card F ^ 2 := Nat.one_le_pow _ _ Nat.card_pos
    have he := Nat.sub_add_cancel hq
    nlinarith [sq_nonneg (Nat.card F ^ 2), sq_nonneg (Nat.card F ^ 2 - 1)]
  apply Nat.eq_of_mul_eq_mul_left (show 0 < Nat.card ι.range from Nat.card_pos)
  calc
    Nat.card ι.range * ι.range.index = Nat.card (Model F) := ι.range.card_mul_index
    _ = (Nat.card F + 1)^2 *
        (Nat.card F ^ 6 * (Nat.card F - 1)^2 * (Nat.card F ^ 4 + Nat.card F ^ 2 + 1)) := by
      rw [card_Model, h6, h2]
      ring
    _ = _ := by rw [← hk]; ring

/-- Every odd prime misses a finite kernel of exponent two. -/
theorem not_dvd_card_kernel_of_square
    {A G : Type*} [Group A] [Finite A] [Group G] (ι : A →* G)
    (hk : ∀ a, ι a = 1 → a ^ 2 = 1)
    {r : ℕ} [Fact r.Prime] (hr : r ≠ 2) : ¬ r ∣ Nat.card ι.ker := by
  have hp : IsPGroup 2 ι.ker := by
    apply isPGroup_iff_pow_pow_eq_one.mpr
    intro a
    exact ⟨1, Subtype.ext (by simpa using hk a a.property)⟩
  obtain ⟨n, hn⟩ := hp.exists_card_eq
  rw [hn]
  intro h
  exact hr ((Nat.prime_dvd_prime_iff_eq (Fact.out : r.Prime) Nat.prime_two).mp
    ((Fact.out : r.Prime).dvd_of_dvd_pow h))

/-- A quadratic central-product torus has index prime to r>3 dividing q+1. -/
theorem not_dvd_quadratic_index {C : Type*} [Group C] [Finite C]
    (ι : C × C →* Model F) (hC : Nat.card C = Nat.card F + 1)
    (hk : ∀ a, ι a = 1 → a ^ 2 = 1)
    {r : ℕ} [Fact r.Prime] (hr : 3 < r) (hd : r ∣ Nat.card F + 1) :
    ¬ r ∣ ι.range.index := by
  rw [quadratic_index ι hC]
  apply (Fact.out : r.Prime).not_dvd_mul
    (not_dvd_card_kernel_of_square ι hk (by omega))
  have hq : (Nat.card F : ZMod r) = -1 := by
    have hh := (CharP.cast_eq_zero_iff (ZMod r) r (Nat.card F + 1)).mpr hd
    push_cast at hh
    exact eq_neg_of_add_eq_zero_left hh
  intro hi
  have hh := (CharP.cast_eq_zero_iff (ZMod r) r _).mpr hi
  rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_pow,
    Nat.cast_pow, Nat.cast_sub (show 1 ≤ Nat.card F from Nat.card_pos)] at hh
  norm_num [Nat.cast_add, Nat.cast_pow, hq] at hh
  have h12 : r ∣ 12 := (CharP.cast_eq_zero_iff (ZMod r) r 12).mp hh
  have hp := (Fact.out : r.Prime)
  have he : r = 2 ∨ r = 3 := by
    have h : r ∣ 2 ^ 2 * 3 := by norm_num at h12 ⊢; exact h12
    rcases hp.dvd_mul.mp h with h | h
    · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h))
    · exact Or.inr ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp h)
  omega

private theorem pair_generates {C G : Type*} [Group C] [Group G]
    (ι : C × C →* G) (P : Subgroup C) (z : P)
    (hz : ∀ u : P, u ∈ zpowers z) :
    closure ({ι (z, 1), ι (1, z)} : Set G) = (P.prod P).map ι := by
  apply le_antisymm
  · apply (closure_le _).mpr
    intro g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl
    · exact ⟨(z, 1), ⟨z.property, P.one_mem⟩, rfl⟩
    · exact ⟨(1, z), ⟨P.one_mem, z.property⟩, rfl⟩
  · rintro g ⟨⟨a, b⟩, ⟨ha, hb⟩, rfl⟩
    obtain ⟨i, hi⟩ := mem_zpowers_iff.mp (hz ⟨a, ha⟩)
    obtain ⟨j, hj⟩ := mem_zpowers_iff.mp (hz ⟨b, hb⟩)
    have hi' : (z : C) ^ i = a := congrArg Subtype.val hi
    have hj' : (z : C) ^ j = b := congrArg Subtype.val hj
    have hrep : ι (a, b) = (ι ((z : C), 1)) ^ i * (ι (1, (z : C))) ^ j := by
      rw [← map_zpow, ← map_zpow, ← map_mul]
      congr 1
      ext <;> simp [hi', hj']
    rw [hrep]
    exact mul_mem (zpow_mem (subset_closure (by simp)) i)
      (zpow_mem (subset_closure (by simp)) j)

omit [Finite F] in
/-- The torus image contains an actual full Sylow with two inverted generators.
Injectivity of the torus map is not required. -/
theorem exists_quadratic_configuration
    {C : Type*} [CommGroup C] [Finite C] [IsCyclic C]
    (ι : C × C →* Model F) {r : ℕ} [Fact r.Prime] (hr : 3 < r)
    (hi : ¬ r ∣ ι.range.index) (w : Model F)
    (hinv : ∀ c : C, w * ι (c,1) * w⁻¹ = ι (c⁻¹,1))
    (hfix : ∀ c : C, w * ι (1,c) * w⁻¹ = ι (1,c)) :
    ∃ (Q : Sylow r (Model F)) (x y : Model F) (n : ℕ),
      closure ({x, y} : Set (Model F)) = (Q : Subgroup (Model F)) ∧
      n.Coprime 2 ∧ x ^ n = 1 ∧ Commute x y ∧
      w * x * w⁻¹ = x⁻¹ ∧ Commute w y ∧
      (Q : Subgroup (Model F)) ≤ ι.range := by
  let P : Sylow r C := Classical.choice inferInstance
  let D : Subgroup (C × C) := (P : Subgroup C).prod (P : Subgroup C)
  let H : Subgroup (Model F) := D.map ι
  have hDi : ¬ r ∣ D.index := by
    rw [Subgroup.index_prod]
    exact (Fact.out : r.Prime).not_dvd_mul P.not_dvd_index P.not_dvd_index
  have hHi : ¬ r ∣ H.index := by
    rw [Subgroup.index_map]
    exact (Fact.out : r.Prime).not_dvd_mul
      (fun h => hDi (h.trans (Subgroup.index_dvd_of_le le_sup_left))) hi
  obtain ⟨k, hk⟩ := P.isPGroup'.exists_card_eq
  have hprod : IsPGroup r D := by
    apply IsPGroup.of_card (n := k + k)
    rw [Nat.card_congr (Subgroup.prodEquiv (P : Subgroup C) (P : Subgroup C)).toEquiv,
      Nat.card_prod, hk, pow_add]
  let Q := (hprod.map ι).toSylow hHi
  obtain ⟨z, hz⟩ := IsCyclic.exists_generator (α := P)
  have hn : (Nat.card P).Coprime 2 := by
    rw [hk]
    exact ((Nat.prime_two.coprime_iff_not_dvd.mpr (by
      intro h
      have he := (Nat.prime_dvd_prime_iff_eq Nat.prime_two (Fact.out : r.Prime)).mp h
      omega)).symm).pow_left k
  refine ⟨Q, ι (z, 1), ι (1, z), Nat.card P, pair_generates ι _ z hz, hn, ?_,
    (Commute.all ((z : C), 1) (1, (z : C))).map ι, ?_, ?_, ?_⟩
  · rw [← map_pow]
    have hzpow : (z : C) ^ Nat.card P = 1 :=
      congrArg Subtype.val (pow_card_eq_one' (x := z))
    have hpair : ((z : C), (1 : C)) ^ Nat.card P = 1 := Prod.ext hzpow (one_pow _)
    rw [hpair, map_one]
  · exact (hinv z).trans (by
      simpa only [Prod.inv_mk, inv_one] using ι.map_inv ((z : C),1))
  · exact (mul_inv_eq_iff_eq_mul).mp (hfix z)
  · exact D.map_le_range ι

/-- The quadratic-torus calculation for an arbitrary finite perfect central cover. -/
theorem not_dvd_kernel_of_quadratic
    {C : Type*} [CommGroup C] [Finite C] [IsCyclic C]
    (ι : C × C →* Model F) (hC : Nat.card C = Nat.card F + 1)
    (hk : ∀ a, ι a = 1 → a ^ 2 = 1) (w : Model F)
    (hinv : ∀ c : C, w * ι (c,1) * w⁻¹ = ι (c⁻¹,1))
    (hfix : ∀ c : C, w * ι (1,c) * w⁻¹ = ι (1,c))
    {E : Type*} [Group E] [Finite E] [Group.IsPerfect E]
    (f : E →* Model F) (hf : Function.Surjective f) (hc : f.ker ≤ center E)
    {r : ℕ} [Fact r.Prime] (hr : 3 < r) (hd : r ∣ Nat.card F + 1) :
    ¬ r ∣ Nat.card f.ker := by
  obtain ⟨Q, x, y, n, hQ, hn, hx, hxy, hwx, hwy, _hcontain⟩ :=
    exists_quadratic_configuration ι hr (not_dvd_quadratic_index ι hC hk hr hd) w hinv hfix
  exact CentralExtension.not_dvd_card_kernel_of_partial_inversion
    f hf hc Q x y w hQ hn hx hxy hwx hwy

/-- Rank-one factors supply the literal norm-one image and its partial inverter. -/
theorem exists_quadratic_torus_of_rankOne_product
    (p : ℕ) [Fact p.Prime] [CharP F p]
    (π : (SpecialLinearGroup (Fin 2) F × SpecialLinearGroup (Fin 2) F) →* Model F)
    (hπ : ∀ a, π a = 1 → a ^ 2 = 1) :
    ∃ (ι : normOne F p × normOne F p →* Model F) (w : Model F),
      (∀ a, ι a = 1 → a ^ 2 = 1) ∧
      (∀ c, w * ι (c,1) * w⁻¹ = ι (c⁻¹,1)) ∧
      (∀ c, w * ι (1,c) * w⁻¹ = ι (1,c)) := by
  obtain ⟨s, v, hs, hv⟩ := exists_normOne_SL2 F p
  let ι := π.comp (s.prodMap s)
  have hi : Function.Injective (s.prodMap s) := Prod.map_injective.mpr ⟨hs, hs⟩
  refine ⟨ι, π (v,1), ?_, ?_, ?_⟩
  · intro a ha
    apply hi
    rw [map_pow, map_one]
    exact hπ _ ha
  · intro c
    change π (v,1) * π (s c,s 1) * (π (v,1))⁻¹ = π (s c⁻¹,s 1)
    rw [← map_inv, ← map_mul, ← map_mul]
    apply congrArg π
    apply Prod.ext
    · exact hv c
    · simp
  · intro c
    change π (v,1) * π (s 1,s c) * (π (v,1))⁻¹ = π (s 1,s c)
    rw [← map_inv, ← map_mul, ← map_mul]
    apply congrArg π
    apply Prod.ext <;> simp

/-- A concrete pair of rank-one factors supplies the actual norm-one torus and
partial inverter. Its kernel of exponent two is harmless for odd Sylow primes. -/
theorem not_dvd_kernel_of_rankOne_product
    (p : ℕ) [Fact p.Prime] [CharP F p]
    (π : (SpecialLinearGroup (Fin 2) F × SpecialLinearGroup (Fin 2) F) →* Model F)
    (hπ : ∀ a, π a = 1 → a ^ 2 = 1)
    {E : Type*} [Group E] [Finite E] [Group.IsPerfect E]
    (f : E →* Model F) (hf : Function.Surjective f) (hc : f.ker ≤ center E)
    {r : ℕ} [Fact r.Prime] (hr : 3 < r) (hd : r ∣ Nat.card F + 1) :
    ¬ r ∣ Nat.card f.ker := by
  obtain ⟨ι, w, hk, hinv, hfix⟩ := exists_quadratic_torus_of_rankOne_product p π hπ
  exact not_dvd_kernel_of_quadratic ι (card_normOne F p) hk w hinv hfix f hf hc hr hd

/-- Application to the literal universal kernel. The geometric rank-one
homomorphism is the explicit input supplied by the parent module. -/
theorem universal_not_dvd_kernel_of_rankOne_product
    (p : ℕ) [Fact p.Prime] [CharP F p] (hF : 2 < Nat.card F)
    (π : (SpecialLinearGroup (Fin 2) F × SpecialLinearGroup (Fin 2) F) →* Model F)
    (hπ : ∀ a, π a = 1 → a ^ 2 = 1)
    {r : ℕ} [Fact r.Prime] (hr : 3 < r) (hd : r ∣ Nat.card F + 1) :
    ¬ r ∣ Nat.card (PerfectCentralCovering.universalProjection (Model F)).ker := by
  let : Group.IsPerfect (Model F) := Atlas.G2.isPerfect hF
  exact not_dvd_kernel_of_rankOne_product p π hπ
    (PerfectCentralCovering.universalProjection (Model F))
    (PerfectCentralCovering.universalProjection_surjective _)
    (PerfectCentralCovering.universalProjection_ker_le_center _) hr hd

end Atlas.G2.MultiplierOrdinary.OddQuadraticTorus

end
