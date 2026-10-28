module

public import Theory.ElementaryAbelian.Quotient
public import Theory.GroupTheory.PGroup.FrattiniAutomorphismKernel
public import Mathlib.GroupTheory.SpecificGroups.Quaternion
public import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.Tactic.Group

/-!
# Faithful quaternion actions on an odd prime plane

If an invariant subgroup has order p, both it and its quotient are cyclic.
The central quaternion involution, a commutator, fixes both layers because
automorphisms of cyclic groups commute. Its displacement lies in the fixed
order-p subgroup and has square one, hence is trivial for odd p. This
contradicts faithfulness. The only invariant subgroups are therefore 1 and
the full plane.

Source: the Sylow irreducibility assertion in Aschbacher–Smith 13.3.14(d),
printed p.892. No irreducibility or central-inversion premise is assumed.
-/

public section
open Subgroup

namespace QuaternionGroup

private theorem central_involution_killed {C : Type*} [Group C] [IsCyclic C]
    (f : QuaternionGroup 2 →* MulAut C) : f (.a 2) = 1 := by
  have hc (g h : QuaternionGroup 2) : f g * f h = f h * f g := by
    apply (IsCyclic.mulAutMulEquiv C).injective
    simp only [map_mul]
    exact mul_comm _ _
  rw [show (QuaternionGroup.a 2 : QuaternionGroup 2) =
    .a 1 * .xa 0 * (.a 1)⁻¹ * (.xa 0)⁻¹ by decide]
  simp only [map_mul, map_inv]
  rw [hc]
  group

theorem faithful_plane_irreducible
    {p : ℕ} [Fact p.Prime] (hp : Odd p)
    {V : Type*} [Group V] [Finite V] [IsElementaryAbelian p V]
    (hc : Nat.card V = p ^ 2) (ρ : QuaternionGroup 2 →* MulAut V)
    (hf : Function.Injective ρ) (A : Subgroup V)
    (hA : ∀ g x, x ∈ A → ρ g x ∈ A) : A = ⊥ ∨ A = ⊤ := by
  have hd : Nat.card A ∣ p ^ 2 := hc ▸ A.card_subgroup_dvd_card
  obtain ⟨k, hk, he⟩ := (Nat.dvd_prime_pow (Fact.out : p.Prime)).mp hd
  interval_cases k
  · exact Or.inl (A.eq_bot_of_card_eq (by simpa using he))
  · have hcard : Nat.card A = p := by simpa using he
    let : IsCyclic A := isCyclic_of_prime_card hcard
    let φ : QuaternionGroup 2 →* MulAut A := {
      toFun := fun g => {
        toFun := fun x => ⟨ρ g x, hA g x x.property⟩
        invFun := fun x => ⟨ρ g⁻¹ x, hA g⁻¹ x x.property⟩
        left_inv := fun x => Subtype.ext (by simp)
        right_inv := fun x => Subtype.ext (by simp)
        map_mul' := fun x y => Subtype.ext (map_mul (ρ g) (x : V) (y : V)) }
      map_one' := by ext x; change ρ 1 (x : V) = (x : V); simp
      map_mul' := by
        intro g h; ext x
        change ρ (g * h) (x : V) = ρ g (ρ h (x : V))
        rw [map_mul]; rfl }
    let : A.Normal := inferInstance
    have hmap (g : QuaternionGroup 2) : A.map (ρ g).toMonoidHom = A := by
      apply le_antisymm
      · rintro _ ⟨x, hx, rfl⟩; exact hA g x hx
      · intro x hx
        exact ⟨ρ g⁻¹ x, hA g⁻¹ x hx, by simp⟩
    let ψ : QuaternionGroup 2 →* MulAut (V ⧸ A) := {
      toFun := fun g => QuotientGroup.congr A A (ρ g) (hmap g)
      map_one' := by
        ext q
        obtain ⟨v, rfl⟩ := QuotientGroup.mk'_surjective A q
        change QuotientGroup.mk' A (ρ 1 v) = QuotientGroup.mk' A v
        simp
      map_mul' := by
        intro g h; ext q
        obtain ⟨v, rfl⟩ := QuotientGroup.mk'_surjective A q
        change QuotientGroup.mk' A (ρ (g * h) v) = QuotientGroup.mk' A (ρ g (ρ h v))
        rw [map_mul]; rfl }
    have hquot : Nat.card (V ⧸ A) = p := by
      have hh := A.index_mul_card
      change Nat.card (V ⧸ A) * Nat.card A = Nat.card V at hh
      rw [hcard, hc, pow_two] at hh
      exact mul_right_cancel₀ (Fact.out : p.Prime).ne_zero hh
    let : IsCyclic (V ⧸ A) := isCyclic_of_prime_card hquot
    have hzφ := central_involution_killed φ
    have hzψ := central_involution_killed ψ
    have hzfix (v : V) (hv : v ∈ A) : ρ (.a 2) v = v := by
      exact congrArg (fun f : MulAut A => (f ⟨v, hv⟩ : V)) hzφ
    have hzquot (v : V) : QuotientGroup.mk' A (ρ (.a 2) v) = QuotientGroup.mk' A v := by
      exact congrArg (fun f : MulAut (V ⧸ A) => f (QuotientGroup.mk' A v)) hzψ
    have hzsq (v : V) : ρ (.a 2) (ρ (.a 2) v) = v := by
      have hh : ρ (.a 2) * ρ (.a 2) = 1 := by
        rw [← map_mul, show (QuaternionGroup.a 2 : QuaternionGroup 2) * .a 2 = 1 by decide, map_one]
      exact congrArg (fun f : MulAut V => f v) hh
    have hz : ρ (.a 2) = 1 := by
      ext v
      have hm : v⁻¹ * ρ (.a 2) v ∈ A := QuotientGroup.eq.mp (hzquot v).symm
      have hh := hzfix _ hm
      rw [map_mul, map_inv, hzsq] at hh
      let d : A := ⟨v⁻¹ * ρ (.a 2) v, hm⟩
      have hs : d ^ 2 = 1 := by
        apply Subtype.ext
        change (v⁻¹ * ρ (.a 2) v) ^ 2 = 1
        calc
          _ = (v⁻¹ * ρ (.a 2) v) * (v⁻¹ * ρ (.a 2) v) := pow_two _
          _ = ((ρ (.a 2) v)⁻¹ * v) * (v⁻¹ * ρ (.a 2) v) := by rw [hh]
          _ = 1 := by group
      have he : d = 1 := orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes
        (Nat.coprime_two_left.mpr hp) (orderOf_dvd_of_pow_eq_one hs)
        (hcard ▸ _root_.orderOf_dvd_natCard d))
      have hv : v⁻¹ * ρ (.a 2) v = 1 := congrArg Subtype.val he
      exact (inv_mul_eq_one.mp hv).symm
    have he : (QuaternionGroup.a 2 : QuaternionGroup 2) = 1 := hf (hz.trans ρ.map_one.symm)
    exact (by decide : (QuaternionGroup.a 2 : QuaternionGroup 2) ≠ 1) he |>.elim
  · exact Or.inr (A.eq_top_of_card_eq (he.trans hc.symm))

end QuaternionGroup
