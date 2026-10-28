module

public import Theory.GroupAction.FourGroupSylowCentralizer

/-!
# Elementary abelian pointwise Sylow fixers

In a centerless finite group with cyclic Sylow center, two nonidentity inner
involutions fixing that Sylow subgroup coincide. Thus an elementary abelian
group of pointwise fixers has order at most two whenever its involutions are
inner. This is the intrinsic counting step used for the small odd models in
Aschbacher–Smith, E.6.8(5), printed p.248.
-/

open Subgroup
namespace Theory.GroupAction
variable {X : Type*} [Group X] [Finite X]

public theorem elementary_sylow_fixer_card_le_two_of_inner (S : Sylow 2 X) [IsCyclic (center S)]
    (hZ : center X = ⊥)
    (hinner : ∀ a : MulAut X, a ^ 2 = 1 →
      (∀ x : S, a x = x) → ∃ g, a = MulAut.conj g)
    (A : Subgroup (MulAut X)) [IsElementaryAbelian 2 A]
    (hfix : ∀ a ∈ A, ∀ x ∈ S, a x = x) : Nat.card A ≤ 2 := by
  classical
  let f : A → Bool := fun a => decide (a = 1)
  have hf : Function.Injective f := by
    intro a b he
    by_cases ha : a = 1
    · have hb : b = 1 := by simpa [f, ha] using he.symm
      exact ha.trans hb.symm
    by_cases hb : b = 1
    · have ha' : a = 1 := by simpa [f, hb] using he
      exact (ha ha').elim
    apply Subtype.ext
    have hsq (c : A) : (c : MulAut X) ^ 2 = 1 :=
      elemPow_eq_one_of_isElementaryAbelian _ c.property
    have hn (c : A) (hc : c ≠ 1) : (c : MulAut X) ≠ 1 :=
      fun hh => hc (Subtype.ext hh)
    exact inner_involutions_fixing_sylow_eq S hZ (hsq a) (hsq b) (hn a ha) (hn b hb)
      (fun x => hfix a a.property x x.property) (fun x => hfix b b.property x x.property)
      (hinner a (hsq a) (fun x => hfix a a.property x x.property))
      (hinner b (hsq b) (fun x => hfix b b.property x x.property))
  exact (Nat.card_le_card_of_injective f hf).trans (by simp)
end Theory.GroupAction
