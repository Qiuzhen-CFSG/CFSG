module

public import Theory.SpecificGroups.UnitaryThree.OddTorusNormalizer.Placement.NonabelianFrame.Basic
public import Theory.Representation.RankThreePGroupIrreducible
public import FeitThompson.FinalTheorem

/-!
# Irreducibility in the odd nonabelian unitary branch

The odd-order theorem supplies solvability. After extension to an algebraic
closure, complete reducibility and odd degree divisibility force a reducible
three-dimensional faithful action to be a sum of lines, which would make the
group abelian. Thus the actual subgroup acts absolutely irreducibly, and each
overgroup acts irreducibly over the original coefficient field.

Source: GLS4, Chapter 4, Lemma 3.11(a),
`refs/KGroup/GLS4/Chapter4.tex`, lines 585–603; the degree argument is isolated
in `Theory.Representation.RankThreePGroupIrreducible`.
-/

public section
open BenderSuzuki.MatrixGroups Representation
open scoped TensorProduct
namespace UnitaryThree.OddTorusNormalizer.NonabelianFrame
variable {E : Type*} [Field E]

/-- The faithful action of a nonabelian odd subgroup is absolutely irreducible
in characteristic two, using the odd-order theorem and degree divisibility. -/
theorem natural_isAbsolutelyIrreducible_of_odd_nonabelian
    [Finite E] [CharP E 2] (J : HermitianForm 3 E) (H : Subgroup J.specialSubgroup)
    (hodd : Odd (Nat.card H)) (hna : ¬ IsMulCommutative H) :
    IsAbsolutelyIrreducible ((naturalRepresentation J).comp H.subtype) := by
  let ρ := (naturalRepresentation J).comp H.subtype
  let F := AlgebraicClosure E
  let σ := extendScalars F ρ
  let : Group.IsSolvable H := odd_order_theorem H hodd
  have hc : ringChar F = 0 ∨
      (Nat.Prime (ringChar F) ∧ Nat.Coprime (ringChar F) (Nat.card H)) := by
    right
    rw [ringChar.eq F 2]
    exact ⟨Nat.prime_two, Nat.coprime_two_left.mpr hodd⟩
  refine ⟨isIrreducible_of_finrank_eq_three_of_odd_card σ
    (isCompletelyReducible_of_ringChar_eq_zero_or_prime_coprime σ hc) ?_ ?_ hodd hna⟩
  · exact (extendScalars_faithful_iff F ρ).mp
      ((naturalRepresentation_injective J).comp Subtype.val_injective)
  · change Module.finrank F (F ⊗[E] (Fin 3 → E)) = 3
    rw [Module.finrank_baseChange]
    simp

/-- Every overgroup of the given odd nonabelian subgroup acts irreducibly on
the original three-space. -/
theorem natural_isIrreducible_of_odd_nonabelian_le
    [Finite E] [CharP E 2] (J : HermitianForm 3 E) (H K : Subgroup J.specialSubgroup)
    (hodd : Odd (Nat.card H)) (hna : ¬ IsMulCommutative H) (hHK : H ≤ K) :
    IsIrreducible ((naturalRepresentation J).comp K.subtype) := by
  let ρ := (naturalRepresentation J).comp H.subtype
  let σ := (naturalRepresentation J).comp K.subtype
  let : IsAbsolutelyIrreducible ρ :=
    natural_isAbsolutelyIrreducible_of_odd_nonabelian J H hodd hna
  have hi : IsIrreducible ρ :=
    IsAbsolutelyIrreducible.irreducible_of_isAbsolutelyIrreducible ρ
  refine ⟨fun W => ?_⟩
  let W' : Subrepresentation ρ :=
    ⟨W.toSubmodule, fun h v hv => W.apply_mem_toSubmodule (Subgroup.inclusion hHK h) hv⟩
  rcases hi.eq_bot_or_eq_top W' with h | h
  · exact Or.inl (Subrepresentation.toSubmodule_injective
      (congrArg (fun U : Subrepresentation ρ => U.toSubmodule) h))
  · exact Or.inr (Subrepresentation.toSubmodule_injective
      (congrArg (fun U : Subrepresentation ρ => U.toSubmodule) h))

end UnitaryThree.OddTorusNormalizer.NonabelianFrame
