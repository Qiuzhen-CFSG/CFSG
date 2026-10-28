module

public import Theory.ElementaryAbelian.Basic
public import Theory.GroupTheory.PGroup.CyclicInvolution
public import Mathlib.GroupTheory.Sylow
import Mathlib.Tactic

/-!
# Four-group actions fixing a Sylow subgroup

In a centerless group an inner involution comes from an actual involution.
If it fixes a Sylow two-subgroup pointwise, its conjugating element lies in
that Sylow subgroup by maximality, hence in its center. A cyclic center has
only one involution. Two distinct nonidentity members of a faithful
four-group action therefore cannot both act by inner automorphisms.

The final theorem isolates the remaining model input: all involutions
fixing the specified Sylow subgroup must be inner. It does not assert that
input for an arbitrary finite group.

This is the elementary group-theoretic reduction for the unitary alternatives
in Aschbacher–Smith, *The Classification of Quasithin Groups*, F.6.18(10)–(11),
used in 15.4.18, printed pp.1162–1163.
-/

open Subgroup
namespace Theory.GroupAction
variable {K : Type*} [Group K]

/-- An element squaring to one and centralizing a Sylow two-subgroup belongs to that Sylow subgroup. -/
public theorem mem_sylow_of_sq_eq_one_of_centralizes
    (P : Sylow 2 K) {x : K} (hx : x ^ 2 = 1)
    (hc : x ∈ centralizer (P : Set K)) : x ∈ P := by
  have h2 : IsPGroup 2 (zpowers x) := IsPGroup.of_card_dvd_pow (n := 1) (by
    simpa only [Nat.card_zpowers, pow_one] using orderOf_dvd_of_pow_eq_one hx)
  have hnorm : zpowers x ≤ normalizer (P : Set K) :=
    zpowers_le.mpr (centralizer_le_normalizer _ hc)
  have he := P.is_maximal' (h2.to_sup_of_normal_right' P.isPGroup' hnorm) le_sup_right
  exact (show zpowers x ≤ P from sup_le_iff.mp (le_of_eq he) |>.1) (mem_zpowers x)

private theorem conj_injective_of_center_eq_bot (hZ : center K = ⊥) :
    Function.Injective (MulAut.conj : K →* MulAut K) := by
  apply (MulAut.conj : K →* MulAut K).ker_eq_bot_iff.mp
  apply le_bot_iff.mp
  intro x hx
  have he : MulAut.conj x = 1 := hx
  have hc : x ∈ center K := by
    rw [mem_center_iff]
    intro y
    have hy := congrArg (fun a : MulAut K => a y) he
    change x * y * x⁻¹ = y at hy
    exact ((mul_inv_eq_iff_eq_mul).mp hy).symm
  simpa only [hZ] using hc

/-- In a centerless finite group with cyclic Sylow center, at most one nonidentity inner involution fixes that Sylow subgroup pointwise. -/
public theorem inner_involutions_fixing_sylow_eq [Finite K]
    (P : Sylow 2 K) [IsCyclic (center P)] (hZ : center K = ⊥)
    {α β : MulAut K} (hα : α ^ 2 = 1) (hβ : β ^ 2 = 1)
    (hα1 : α ≠ 1) (hβ1 : β ≠ 1)
    (hαP : ∀ x : P, α x = x) (hβP : ∀ x : P, β x = x)
    (hαi : ∃ x, α = MulAut.conj x) (hβi : ∃ x, β = MulAut.conj x) : α = β := by
  obtain ⟨x, rfl⟩ := hαi
  obtain ⟨y, rfl⟩ := hβi
  have hinj := conj_injective_of_center_eq_bot hZ
  have hx2 : x ^ 2 = 1 := hinj (by simpa only [map_pow, map_one] using hα)
  have hy2 : y ^ 2 = 1 := hinj (by simpa only [map_pow, map_one] using hβ)
  have hxc : x ∈ centralizer (P : Set K) := by
    intro z hz
    have hh := hαP ⟨z, hz⟩
    change x * z * x⁻¹ = z at hh
    exact ((mul_inv_eq_iff_eq_mul).mp hh).symm
  have hyc : y ∈ centralizer (P : Set K) := by
    intro z hz
    have hh := hβP ⟨z, hz⟩
    change y * z * y⁻¹ = z at hh
    exact ((mul_inv_eq_iff_eq_mul).mp hh).symm
  have hxP := mem_sylow_of_sq_eq_one_of_centralizes P hx2 hxc
  have hyP := mem_sylow_of_sq_eq_one_of_centralizes P hy2 hyc
  let xZ : center P := ⟨⟨x, hxP⟩, mem_center_iff.mpr fun z => Subtype.ext (hxc z z.property)⟩
  let yZ : center P := ⟨⟨y, hyP⟩, mem_center_iff.mpr fun z => Subtype.ext (hyc z z.property)⟩
  have hxZ : orderOf xZ = 2 := orderOf_eq_prime
    (Subtype.ext (Subtype.ext hx2)) (fun h => hα1 (by
      have hx1 : x = 1 := congrArg (fun z : center P => (z : K)) h
      rw [hx1, map_one]))
  have hyZ : orderOf yZ = 2 := orderOf_eq_prime
    (Subtype.ext (Subtype.ext hy2)) (fun h => hβ1 (by
      have hy1 : y = 1 := congrArg (fun z : center P => (z : K)) h
      rw [hy1, map_one]))
  exact congrArg MulAut.conj (congrArg (fun z : center P => (z : K))
    (IsCyclic.eq_of_orderOf_eq_two hxZ hyZ))

/-- If every involution fixing a Sylow subgroup is inner and its center is cyclic, no four-group acts faithfully while fixing that Sylow subgroup pointwise. -/
public theorem not_injective_elementaryFour_fixing_sylow_of_inner [Finite K]
    {A : Type*} [Group A] [Finite A] [IsElementaryAbelian 2 A]
    (P : Sylow 2 K) [IsCyclic (center P)] (hZ : center K = ⊥)
    (hinner : ∀ α : MulAut K, α ^ 2 = 1 →
      (∀ x : P, α x = x) → ∃ x, α = MulAut.conj x)
    (hA : Nat.card A = 4) (ρ : A →* MulAut K)
    (hfix : ∀ a : A, ∀ x : P, ρ a x = x) : ¬ Function.Injective ρ := by
  classical
  intro hinj
  let := Fintype.ofFinite A
  have hc : Fintype.card A = 4 := by simpa using hA
  have hnt : Nontrivial A := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  obtain ⟨a, ha⟩ := exists_ne (1 : A)
  obtain ⟨b, -, hb⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (show ({1, a} : Finset A).card < Finset.univ.card from by
      rw [Finset.card_univ, hc, Finset.card_pair (Ne.symm ha)]; omega)
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hb
  have hs (t : A) : ρ t ^ 2 = 1 := by
    rw [← map_pow, Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p 2 A) t, map_one]
  have hn (t : A) (ht : t ≠ 1) : ρ t ≠ 1 := by
    intro he
    exact ht (hinj (he.trans ρ.map_one.symm))
  exact hb.2 (hinj (inner_involutions_fixing_sylow_eq P hZ
    (hs b) (hs a) (hn b hb.1) (hn a ha) (hfix b) (hfix a)
    (hinner _ (hs b) (hfix b)) (hinner _ (hs a) (hfix a))))

end Theory.GroupAction
