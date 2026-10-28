module
public import Theory.SpecificGroups.SymplecticFour.OddFieldActors.Reduction
public import Theory.SpecificGroups.SymplecticFour.OddFieldActors.Torus

/-!
# Odd symplectic field actors force prime rank three

The fixed split torus has an elementary subgroup of order p². Its inner
image commutes with a field actor of order p and does not contain that
actor. Their join therefore has rank three. An automorphism subgroup of
rank at most two containing all inner automorphisms cannot contain such
an actor. The genuine inner–field decomposition then shows that every
p-power-order element of that subgroup is inner.

Source: Aschbacher–Smith A.3.18, printed pp.51–53; the application to the
actual component action in 2.5.7 is the separate source consumer.
-/

public section
noncomputable section
open Subgroup
namespace Theory.SpecificGroups.SymplecticFour.OddFieldActors
open DiagramAutomorphisms
variable {F : Type*} [Field F] [Finite F] [CharP F 2]
variable {p : ℕ} [Fact p.Prime]

theorem field_actor_rank_three (A : Subgroup (MulAut (Sp F)))
    (hinner : MulAut.innerSubgroup (Sp F) ≤ A)
    (σ : F ≃+* F) (hσ : orderOf σ = p) (hσA : fieldAutomorphism σ ∈ A)
    (hd : p ∣ Nat.card F - 1) : 3 ≤ primeRank p A := by
  obtain ⟨E,hE,hcard,hfix⟩ := exists_fixed_elementary σ hσ hd
  let := hE
  let f : Sp F →* A := MulAut.conj.codRestrict A (fun g => hinner ⟨g,rfl⟩)
  have hf : Function.Injective f := by
    intro x y hh
    exact InvolutionNormalForms.inner_injective (congrArg Subtype.val hh)
  let B := E.map f
  let : IsElementaryAbelian p B := IsElementaryAbelian.map f
  let x : A := ⟨fieldAutomorphism σ,hσA⟩
  have hfield : Function.Injective (fieldAutomorphismHom (F := F)) := by
    intro a b hh
    apply InvolutionNormalForms.outerFieldHom_injective
    exact congrArg (QuotientGroup.mk' (MulAut.innerSubgroup (Sp F))) hh
  have hx : orderOf x = p := by
    rw [← orderOf_injective A.subtype A.subtype_injective]
    exact (orderOf_injective fieldAutomorphismHom hfield σ).trans hσ
  have hxB : x ∉ B := by
    rintro ⟨g,_,he⟩
    have hi : fieldAutomorphism σ ∈ MulAut.innerSubgroup (Sp F) :=
      ⟨g,congrArg Subtype.val he⟩
    have hs := InvolutionNormalForms.field_eq_one_of_inner σ hi
    rw [hs,orderOf_one] at hσ
    exact (Fact.out : p.Prime).ne_one hσ.symm
  have hBfix : B ≤ centralizer ({x} : Set A) := by
    rintro _ ⟨g,hg,rfl⟩
    apply mem_centralizer_singleton_iff.mpr
    apply Subtype.ext
    apply MulEquiv.ext
    intro y
    have hgfix := (MulAut.mem_fixedSubgroup _ _).mp (hfix hg)
    change g * fieldAutomorphism σ y * g⁻¹ = fieldAutomorphism σ (g * y * g⁻¹)
    rw [map_mul,map_mul,map_inv,hgfix]
  have hcB : Nat.card B = p^2 := by rw [card_map_of_injective hf,hcard]
  exact IsElementaryAbelian.primeRank_ge_of_fixed_join B x hx hxB hBfix hcB

theorem primePower_actor_inner (hF : 2 < Nat.card F) (ho : Odd p)
    (hd : p ∣ Nat.card F - 1) (A : Subgroup (MulAut (Sp F)))
    (hinner : MulAut.innerSubgroup (Sp F) ≤ A) (hrank : primeRank p A ≤ 2)
    (a : MulAut (Sp F)) (haA : a ∈ A) (ha : ∃ m : ℕ, a ^ (p^m) = 1) :
    a ∈ MulAut.innerSubgroup (Sp F) := by
  let : Finite (F ≃+* F) := Finite.of_injective (fun σ : F ≃+* F => (σ : F → F))
    DFunLike.coe_injective
  obtain ⟨m,ham⟩ := ha
  obtain ⟨g,σ,he,hσ⟩ := inner_field_of_primePower hF ho a ham
  have hσA : fieldAutomorphism σ ∈ A := by
    have hh := A.mul_mem (A.inv_mem (hinner ⟨g,rfl⟩)) haA
    rwa [he,inv_mul_cancel_left] at hh
  have hσone : σ = 1 := by
    by_contra hn
    have hp : IsPGroup p (zpowers σ) := IsPGroup.of_card_dvd_pow (n := m)
      (by rw [Nat.card_zpowers]; exact orderOf_dvd_of_pow_eq_one hσ)
    have hdP : p ∣ Nat.card (zpowers σ) := hp.card_eq_or_dvd.resolve_left (by
      intro hc
      have hb := (card_eq_one.mp hc : zpowers σ = ⊥)
      exact hn (mem_bot.mp (hb ▸ mem_zpowers σ)))
    obtain ⟨τ,hτ⟩ := exists_prime_orderOf_dvd_card' p hdP
    have hτA : fieldAutomorphism (τ : F ≃+* F) ∈ A := by
      obtain ⟨k,hk⟩ := τ.property
      rw [← hk]
      change fieldAutomorphismHom (σ ^ k) ∈ A
      rw [map_zpow]
      exact A.zpow_mem hσA k
    have hτp : orderOf (τ : F ≃+* F) = p :=
      (orderOf_injective (zpowers σ).subtype (zpowers σ).subtype_injective τ).trans hτ
    have hh := field_actor_rank_three A hinner τ hτp hτA hd
    omega
  rw [he,hσone]
  have hh : fieldAutomorphism (1 : F ≃+* F) = 1 := fieldAutomorphismHom.map_one
  rw [hh,mul_one]
  exact ⟨g,rfl⟩

end Theory.SpecificGroups.SymplecticFour.OddFieldActors
