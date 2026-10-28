module

public import Theory.GroupAction.OddBinaryFourFiveNormal
public import Theory.GroupAction.FaithfulSixteen

/-!
# Strict odd overgroups of a five-subgroup in GL₄(2)

A faithful four-dimensional binary representation converts to a faithful action
on an elementary abelian group of order sixteen. The Hall--Sylow calculation
normalizes the marked five-subgroup; the centralizer calculation then forces a
strict odd solvable overgroup to be cyclic of order fifteen. Its action is
regular on the nonzero vectors.

Source: Aschbacher--Smith, *The Classification of Quasithin Groups*,
Lemma 14.2.21, printed p.989 (PDF p.1006).
-/

namespace Theory.GroupAction

/-- A strict odd solvable overgroup of a five-subgroup in GL₄(2) is cyclic of
order fifteen and regular on the nonzero vectors. No normality or order bound
on the actor is assumed. -/
public theorem cyclic_fifteen_regular_of_odd_linear_four
    {A V : Type*} [Group A] [Finite A]
    [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    (hsolv : Group.IsSolvable A)
    (ρ : A →* (V ≃ₗ[ZMod 2] V)) (hρ : Function.Injective ρ)
    (hodd : Odd (Nat.card A)) (hV : Module.finrank (ZMod 2) V = 4)
    (K : Subgroup A) (hK : Nat.card K = 5) (hlt : K < ⊤) :
    Nat.card A = 15 ∧ IsCyclic A ∧
      ∀ x y : V, x ≠ 0 → y ≠ 0 → ∃! a : A, ρ a x = y := by
  let _ : K.Normal := normal_five_of_odd_linear_four hsolv ρ hρ hodd hV K hK
  let _ : Finite V := Module.finite_of_finite (ZMod 2)
  let σ : A →* MulAut (Multiplicative V) := {
    toFun a := (ρ a).toAddEquiv.toMultiplicative
    map_one' := by
      ext x
      exact congrArg Multiplicative.ofAdd (LinearEquiv.congr_fun ρ.map_one x.toAdd)
    map_mul' a b := by
      ext x
      exact congrArg Multiplicative.ofAdd
        (LinearEquiv.congr_fun (ρ.map_mul a b) x.toAdd) }
  have hσ : Function.Injective σ := by
    intro a b h
    apply hρ
    ext x
    exact congrArg Multiplicative.toAdd (MulEquiv.congr_fun h (Multiplicative.ofAdd x))
  have hv : Nat.card (Multiplicative V) = 16 := by
    change Nat.card V = 16
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), hV, Nat.card_zmod]
    norm_num
  obtain ⟨hc, hcyc⟩ := cyclic_fifteen_of_normal_five_lt_top σ hσ K hK hodd hv hlt
  let _ := hcyc
  refine ⟨hc, hcyc, ?_⟩
  intro x y hx hy
  exact faithful_cyclic_fifteen_regular σ hσ hc hv
    (Multiplicative.ofAdd x) (Multiplicative.ofAdd y) hx hy

end Theory.GroupAction
