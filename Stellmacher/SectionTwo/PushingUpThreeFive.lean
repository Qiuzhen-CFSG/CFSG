module
public import Stellmacher.SectionTwo.PushingUpThreeTwo
public import Stellmacher.SectionTwo.PushingUpThreeFour

/-!
# Odd automorphism orbits in the pushing-up theorem

Under the original hypotheses of Stellmacher (2.5), the subgroup generated
by the translates of V under an odd-order subgroup of Aut(S) is normal in G.
This is the exact normality conclusion of the cited *Pushing up* (3.5) needed
by that result; the final containment in O₂(G) is supplied by its consumer.

The proved contained-orbit theorem reduces normality to keeping every
translate inside the distinguished two-core. If a translate escaped, square
control would make the square of its automorphism preserve the core. Every
element of an odd finite group is a power of its square, so the automorphism
itself would preserve the core, contradicting the escape. The original
quotient map, centralizer kernel, and SL₂(2) quotient hypotheses are retained.

Source: Stellmacher, *Pushing up*, Arch. Math. 46 (1986), (3.5), journal p.16,
as invoked in `refs/latex/stellmacher-n-group.tex`, (2.5).
-/

open scoped BigOperators Pointwise

namespace Stellmacher.SectionTwo
universe u

private theorem odd_element_eq_square_power
    {A : Type*} [Group A] [Finite A]
    (hA : Odd (Nat.card A)) (a : A) :
    ∃ k : ℕ, a = (a ^ 2) ^ k := by
  have hord : Odd (orderOf a) :=
    hA.of_dvd_nat (orderOf_dvd_natCard a)
  obtain ⟨j, hj⟩ := hord
  refine ⟨j + 1, ?_⟩
  calc
    a = a ^ (orderOf a + 1) := by
      rw [pow_add, pow_orderOf_eq_one, one_mul, pow_one]
    _ = a ^ (2 * (j + 1)) := by rw [hj]; congr 1
    _ = (a ^ 2) ^ (j + 1) := pow_mul a 2 (j + 1)

public theorem pushing_up_three_five_normal
    {G : Type u} [Group G] [Finite G]
    (h : Hypotheses G) (S : Sylow 2 G)
    (hcharacteristic :
      ∀ K : Subgroup S, K.Characteristic → K ≠ ⊥ →
        ¬ (K.map (S : Subgroup G).subtype).Normal)
    (hunique :
      IsUniqueMaximalContaining (S : Subgroup G) (⊤ : Subgroup G))
    {barG : Type u} [Group barG] [Finite barG]
    (q : G →* barG) (hq : Function.Surjective q)
    (hker : q.ker = cSubgroup S)
    (hbar : Nonempty
      (barG ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod 2)))
    (T : Subgroup (MulAut S)) (hT : Odd (Nat.card T)) :
    (⨆ τ : T, automorphismTranslateV S (τ : MulAut S)).Normal := by
  obtain ⟨hVQ, hnormal⟩ := pushing_up_three_two_contained_orbit_normal
    h S hcharacteristic hunique q hq hker hbar
  apply hnormal T hT
  intro τ
  by_contra hout
  have hsquare := pushing_up_three_four_square_control
    h S hcharacteristic hunique q hq hker hbar (τ : MulAut S) hout
  obtain ⟨k, hk⟩ := odd_element_eq_square_power hT τ
  have hk' : (τ : MulAut S) = ((τ : MulAut S) ^ 2) ^ k :=
    congrArg Subtype.val hk
  have hpowfix : ∀ n : ℕ,
      (((τ : MulAut S) ^ 2) ^ n) • pushingUpQ S = pushingUpQ S := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => rw [pow_succ, mul_smul, hsquare, ih]
  have hfix : (τ : MulAut S) • pushingUpQ S = pushingUpQ S := by
    rw [hk']
    exact hpowfix k
  have hmono : (τ : MulAut S) • vSubgroupInSylow S ≤
      (τ : MulAut S) • pushingUpQ S := Subgroup.map_mono hVQ
  exact hout (hmono.trans_eq hfix)

end Stellmacher.SectionTwo
