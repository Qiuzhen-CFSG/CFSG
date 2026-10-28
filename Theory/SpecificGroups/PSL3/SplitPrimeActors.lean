module
public import Theory.SpecificGroups.PSL3.SplitPrimeActors.Reduction
public import Theory.SpecificGroups.PSL3.SplitPrimeActors.FixedTorus
public import Theory.SpecificGroups.PSL3.OuterSolvable.Coverage

/-!
# Split odd-prime actors in the actual automorphism group of binary PSL₃

A nontrivial p-power field contribution supplies a pure field actor of order p
in the same actor subgroup: the graph and diagonal factors have been removed
from the actual automorphism. Its fixed split torus has an elementary subgroup
of order p², so adjoining the actor forces rank three. Consequently every
p-power actor is inner when p > 3, p divides the split torus order and the
ambient actor subgroup has prime rank at most two.

All decomposition, field fixed-point and scalar-kernel premises are proved.
Binary projective automorphism coverage supplies standard membership. This is
the noncubic linear branch of Aschbacher–Smith A.3.18, printed pp.51–53, used
in the actual component action of 2.5.7, printed p.556.
-/

public section
noncomputable section
open Subgroup
open scoped MatrixGroups
namespace Matrix.PSL3.SplitPrimeActors
open OuterSolvable ExtensionBorel
variable {F : Type*} [Field F] [Finite F] [CharP F 2]
variable {p : ℕ} [Fact p.Prime]

/-- A pure field actor of order p forces rank three in any overgroup of Inn. -/
theorem field_actor_rank_three (hp : p ≠ 3)
    (A : Subgroup (MulAut PSL(3,F))) (hinner : MulAut.innerSubgroup PSL(3,F) ≤ A)
    (σ : F ≃+* F) (hσ : orderOf σ = p) (hσA : fieldAction F σ ∈ A)
    (hd : p ∣ Nat.card F - 1) : 3 ≤ primeRank p A := by
  obtain ⟨E,hE,hcard,hfix⟩ := exists_fixed_elementary σ hσ hp hd
  let := hE
  let f : PSL(3,F) →* A := MulAut.conj.codRestrict A (fun g => hinner ⟨g,rfl⟩)
  have hf : Function.Injective f := by
    intro x y hh
    exact ExtensionBorel.inner_injective F (congrArg Subtype.val hh)
  let B := E.map f
  let : IsElementaryAbelian p B := IsElementaryAbelian.map f
  let x : A := ⟨fieldAction F σ,hσA⟩
  have hx : orderOf x = p := by
    rw [← orderOf_injective A.subtype A.subtype_injective]
    exact (orderOf_injective (fieldAction F) fieldAction_injective σ).trans hσ
  have hxB : x ∉ B := by
    rintro ⟨g,_,he⟩
    have hi : fieldAction F σ ∈ MulAut.innerSubgroup PSL(3,F) :=
      ⟨g,congrArg Subtype.val he⟩
    have hs := field_eq_one_of_inner σ hi
    rw [hs,orderOf_one] at hσ
    exact (Fact.out : p.Prime).ne_one hσ.symm
  have hBfix : B ≤ centralizer ({x} : Set A) := by
    rintro _ ⟨g,hg,rfl⟩
    apply mem_centralizer_singleton_iff.mpr
    apply Subtype.ext
    apply MulEquiv.ext
    intro y
    have hgfix := (MulAut.mem_fixedSubgroup _ _).mp (hfix hg)
    change g * fieldAction F σ y * g⁻¹ = fieldAction F σ (g * y * g⁻¹)
    rw [map_mul,map_mul,map_inv,hgfix]
  have hcB : Nat.card B = p^2 := by rw [card_map_of_injective hf,hcard]
  exact IsElementaryAbelian.primeRank_ge_of_fixed_join B x hx hxB hBfix hcB

/-- Under the rank-two bound every standard p-power actor, p > 3, is inner. -/
theorem standard_inner_of_primePower (hp : 3 < p) (hd : p ∣ Nat.card F - 1)
    (A : Subgroup (MulAut PSL(3,F))) (hinner : MulAut.innerSubgroup PSL(3,F) ≤ A)
    (hrank : primeRank p A ≤ 2) (a : MulAut PSL(3,F)) (haA : a ∈ A)
    (hstandard : a ∈ standard F) (ha : ∃ m : ℕ, a ^ (p^m) = 1) :
    a ∈ MulAut.innerSubgroup PSL(3,F) := by
  let : Finite (F ≃+* F) := Finite.of_injective (fun σ : F ≃+* F => (σ : F → F))
    DFunLike.coe_injective
  obtain ⟨m,ham⟩ := ha
  obtain ⟨g,σ,he,hσ⟩ := inner_field_of_primePower hp a hstandard ham
  have hσA : fieldAction F σ ∈ A := by
    have hh := A.mul_mem (A.inv_mem (hinner ⟨g,rfl⟩)) haA
    rwa [he,inv_mul_cancel_left] at hh
  have hσone : σ = 1 := by
    by_contra hn
    have hP : IsPGroup p (zpowers σ) := IsPGroup.of_card_dvd_pow (n := m)
      (by rw [Nat.card_zpowers]; exact orderOf_dvd_of_pow_eq_one hσ)
    have hdP : p ∣ Nat.card (zpowers σ) := hP.card_eq_or_dvd.resolve_left (by
      intro hc
      have hb := (card_eq_one.mp hc : zpowers σ = ⊥)
      exact hn (mem_bot.mp (hb ▸ mem_zpowers σ)))
    obtain ⟨τ,hτ⟩ := exists_prime_orderOf_dvd_card' p hdP
    have hτA : fieldAction F (τ : F ≃+* F) ∈ A := by
      obtain ⟨k,hk⟩ := τ.property
      rw [← hk,map_zpow]
      exact A.zpow_mem hσA k
    have hτp : orderOf (τ : F ≃+* F) = p :=
      (orderOf_injective (zpowers σ).subtype (zpowers σ).subtype_injective τ).trans hτ
    have hh := field_actor_rank_three (by omega : p ≠ 3) A hinner τ hτp hτA hd
    omega
  rw [he,hσone,map_one,mul_one]
  exact ⟨g,rfl⟩

/-- Full binary automorphism coverage discharges standard membership. -/
theorem inner_of_primePower {n : ℕ} (hn : 0 < n) (hF : Nat.card F = 2^n)
    (hp : 3 < p) (hd : p ∣ Nat.card F - 1)
    (A : Subgroup (MulAut PSL(3,F))) (hinner : MulAut.innerSubgroup PSL(3,F) ≤ A)
    (hrank : primeRank p A ≤ 2) (a : MulAut PSL(3,F)) (haA : a ∈ A)
    (ha : ∃ m : ℕ, a ^ (p^m) = 1) : a ∈ MulAut.innerSubgroup PSL(3,F) := by
  apply standard_inner_of_primePower hp hd A hinner hrank a haA _ ha
  rw [standard_eq_top_of_two_power_card F hn hF]
  trivial

/-- Literal actor-range application, retaining the supplied component action. -/
theorem action_inner_of_primePower {H : Type*} [Group H]
    {n : ℕ} (hn : 0 < n) (hF : Nat.card F = 2^n)
    (hp : 3 < p) (hd : p ∣ Nat.card F - 1)
    (f : H →* MulAut PSL(3,F)) (hinner : MulAut.innerSubgroup PSL(3,F) ≤ f.range)
    (hrank : primeRank p f.range ≤ 2) (x : H) (hx : ∃ m : ℕ, x ^ (p^m) = 1) :
    f x ∈ MulAut.innerSubgroup PSL(3,F) := by
  apply inner_of_primePower hn hF hp hd f.range hinner hrank (f x) ⟨x,rfl⟩
  obtain ⟨m,hm⟩ := hx
  exact ⟨m,by rw [← map_pow,hm,map_one]⟩

end Matrix.PSL3.SplitPrimeActors
