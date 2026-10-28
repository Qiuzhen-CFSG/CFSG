module

public import Theory.GroupTheory.PGroup.HomocyclicPrimeAction.Linear
public import Theory.GroupTheory.PGroup.HomocyclicOmegaFrattini

/-!
# Prime-order automorphisms of rank-two homocyclic groups

An automorphism of order dividing a prime `p > 3` fixes omega in any group
identified with `C(p²) × C(p²)`. Conjugating by the given isomorphism gives
an actual linear action on two additive coordinates. The matrix calculation
fixes all `p`-multiples, and the homocyclic power-map surjectivity identifies
these with the whole omega subgroup.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
manuscript of 1 March 2004, first assertion of Lemma A.1.30, printed p.27.
-/

namespace HomocyclicPrimeAction

private noncomputable def coordinateAction {P : Type*} [Group P] (N : ℕ)
    (e : Multiplicative (Fin 2 → ZMod N) ≃* P) :
    MulAut P →* Module.End (ZMod N) (Fin 2 → ZMod N) where
  toFun a := AddMonoidHom.toZModLinearMap N {
    toFun := fun x => (e.symm (a (e (Multiplicative.ofAdd x)))).toAdd
    map_zero' := by change (e.symm (a (e 1))).toAdd = 0; simp
    map_add' := by
      intro x y
      change (e.symm (a (e (Multiplicative.ofAdd x * Multiplicative.ofAdd y)))).toAdd = _
      simp only [map_mul, toAdd_mul] }
  map_one' := by
    apply LinearMap.ext
    intro x
    change (e.symm (e (Multiplicative.ofAdd x))).toAdd = x
    rw [e.symm_apply_apply, toAdd_ofAdd]
  map_mul' a b := by
    apply LinearMap.ext
    intro x
    change (e.symm (a (b (e (Multiplicative.ofAdd x))))).toAdd =
      (e.symm (a (e (Multiplicative.ofAdd
        (e.symm (b (e (Multiplicative.ofAdd x)))).toAdd)))).toAdd
    rw [ofAdd_toAdd, e.apply_symm_apply]

/-- Order dividing `p` forces fixation of every `p`-th power in the homocyclic group. -/
public theorem fixes_prime_powers_of_equiv {p : ℕ} [Fact p.Prime] (hp : 3 < p)
    {P : Type*} [Group P]
    (e : Multiplicative (Fin 2 → ZMod (p ^ 2)) ≃* P)
    (a : MulAut P) (ha : a ^ p = 1) (x : P) : a (x ^ p) = x ^ p := by
  let L := coordinateAction (p ^ 2) e
  have hL : (L a) ^ p = 1 := by rw [← map_pow, ha, map_one]
  have h := linear_fixes_prime_multiples hp (L a) hL (e.symm x).toAdd
  have he : Multiplicative.ofAdd (p • (e.symm x).toAdd) = e.symm (x ^ p) := by
    rw [map_pow]
    rfl
  change (e.symm (a (e (Multiplicative.ofAdd (p • (e.symm x).toAdd))))).toAdd =
    p • (e.symm x).toAdd at h
  rw [he, e.apply_symm_apply] at h
  apply e.symm.injective
  apply Multiplicative.toAdd.injective
  simpa only [map_pow, toAdd_pow] using h

/-- Every automorphism of order dividing `p` fixes omega in `C(p²) × C(p²)`,
transported through the given group isomorphism. -/
public theorem fixes_omega_of_equiv {p : ℕ} [Fact p.Prime] (hp : 3 < p)
    {P : Type*} [Group P]
    (e : P ≃* (Multiplicative (ZMod (p ^ 2)) × Multiplicative (ZMod (p ^ 2))))
    (a : MulAut P) (ha : a ^ p = 1) : ∀ x ∈ omega₁ P (p := p), a x = x := by
  let c : StandardHomocyclicCover (Fin 2) (p ^ 2) ≃* P :=
    ((AddEquiv.toMultiplicative
      (LinearEquiv.finTwoArrow (ZMod (p ^ 2)) (ZMod (p ^ 2))).toAddEquiv).trans
      (MulEquiv.prodMultiplicative _ _)).trans e.symm
  intro x hx
  have hx' : c.symm x ∈ omega (StandardHomocyclicCover (Fin 2) (p ^ 2)) (p := p) 1 := by
    rw [← c.symm.map_omega p 1]
    exact ⟨x, hx, rfl⟩
  obtain ⟨y, hy⟩ := HomocyclicOmegaFrattini.powerMap_surjective (Fin 2) p 2 (by decide)
    ⟨c.symm x, hx'⟩
  have hy' : y ^ p = c.symm x := by
    have h := congrArg Subtype.val hy
    simpa only [HomocyclicOmegaFrattini.powerMap, MonoidHom.codRestrict_apply,
      powMonoidHom_apply, show 2 - 1 = 1 from rfl, pow_one] using h
  have hxy : x = (c y) ^ p := by
    rw [← map_pow, hy', c.apply_symm_apply]
  rw [hxy]
  exact fixes_prime_powers_of_equiv hp c a ha (c y)

end HomocyclicPrimeAction
