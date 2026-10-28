module
public import Theory.GroupTheory.PGroup.HomocyclicFrattini
public import Mathlib.GroupTheory.SpecificGroups.KleinFour

/-!
# The Frattini quotient of a rank-two homocyclic two-group

A group given by an actual multiplicative equivalence with two cyclic groups
of order `2^n`, for `n ≥ 1`, has Klein four Frattini quotient. This translates
the coordinates of the abelian Sylow subgroup in ABG II.3 Proposition 4,
article page 28, to the quotient hypothesis used by the generic automizer
index calculation. The lemma itself requires neither ambient normality nor
any classification assumptions.

Reindex the two coordinates by Bool and transport the Frattini subgroup
through the given equivalence. The standard homocyclic Frattini theorem then
identifies the quotient with the mod-two coordinate group. Its cardinality
is four and its exponent is two, which gives precisely the Klein four
structure.
-/

private def pairCoordinates (q : ℕ) :
    (Multiplicative (ZMod q) × Multiplicative (ZMod q)) ≃*
      StandardHomocyclicCover Bool q where
  toFun x := Multiplicative.ofAdd (fun b => if b then x.1.toAdd else x.2.toAdd)
  invFun x := (Multiplicative.ofAdd (x.toAdd true), Multiplicative.ofAdd (x.toAdd false))
  left_inv x := by simp
  right_inv x := by ext b; cases b <;> rfl
  map_mul' x y := by ext b; cases b <;> rfl

public theorem isKleinFour_frattini_quotient_of_equiv_prod_zmod
    {U : Type*} [Group U] {n : ℕ} (hn : 1 ≤ n)
    (e : U ≃* (Multiplicative (ZMod (2 ^ n)) × Multiplicative (ZMod (2 ^ n)))) :
    IsKleinFour (U ⧸ frattini U) := by
  let f := e.trans (pairCoordinates (2 ^ n))
  have hf : (frattini U).map f.toMonoidHom =
      frattini (StandardHomocyclicCover Bool (2 ^ n)) := by
    apply le_antisymm
    · exact Subgroup.map_le_iff_le_comap.mpr
        (frattini_le_comap_frattini_of_surjective f.surjective)
    · intro u hu
      refine ⟨f.symm u, ?_, f.apply_symm_apply u⟩
      exact frattini_le_comap_frattini_of_surjective
        (φ := f.symm.toMonoidHom) f.symm.surjective hu
  let q := (QuotientGroup.congr _ _ f hf).trans
    (standardHomocyclicCoverFrattiniQuotientEquiv Bool 2 n hn)
  constructor
  · rw [Nat.card_congr q.toEquiv]
    simp [StandardHomocyclicCover, Nat.card_eq_fintype_card]
  · rw [Monoid.exponent_eq_of_mulEquiv q]
    exact standardHomocyclicCover_exponent Bool 2
