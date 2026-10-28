module
public import Theory.GroupAction.KleinFourFactorization

/-!
# The refined Klein-four inversion decomposition

Two commuting involutive automorphisms of a finite odd-order group determine
its common fixed subgroup and three fixed/inverted subsets. Every element
is the ordered product of a common fixed element and one element of each
subset. The inversion factors are sets, since they need not be subgroups.
On a fixed subgroup, the other two nonidentity positions of the Klein four
act identically, so the choice of inverting involution does not change the
corresponding subset. Trivial or equal action images remain permitted.

The decomposition is the surjectivity part of the established four-factor
bijection. A point inverted by both automorphisms is fixed by their product,
which identifies the final factor with the paper's third subset. This reuses
the canonical automorphism fixed subgroup and the proved Brauer--Wielandt
argument rather than assuming a three-factor decomposition as input.

Source: Alperin--Brauer--Gorenstein II.8, article p63 / PDF64, equation (8.1)
and its preceding notation in `page-064.tex`. The common fixed and inversion
subset definitions are deliberately exposed for the later local analysis.
-/

namespace Theory.GroupAction.KleinFourDecomposition
variable {G : Type*} [Group G]

@[expose] public def commonFixed (first second : MulAut G) : Subgroup G :=
  first.fixedSubgroup ⊓ second.fixedSubgroup

@[expose] public def invertedFixed (fixedActor invertingActor : MulAut G) : Set G :=
  {element | fixedActor element = element ∧ invertingActor element = element⁻¹}

public theorem other_action_eq (first second : MulAut G)
    (commuting : Function.Commute first second) {element : G}
    (fixed : first element = element) : (first * second) element = second element := by
  change first (second element) = second element
  rw [commuting element, fixed]

public theorem invertedFixed_other_choice (first second : MulAut G)
    (commuting : Function.Commute first second) :
    invertedFixed first second = invertedFixed first (first * second) := by
  ext element
  constructor
  · rintro ⟨fixed, inverted⟩
    exact ⟨fixed, (other_action_eq first second commuting fixed).trans inverted⟩
  · rintro ⟨fixed, inverted⟩
    exact ⟨fixed, (other_action_eq first second commuting fixed).symm.trans inverted⟩

public theorem exists_commonFixed_mul_three_inverted [Finite G]
    (odd : Odd (Nat.card G)) (first second : MulAut G)
    (firstInvolutive : Function.Involutive first)
    (secondInvolutive : Function.Involutive second)
    (commuting : Function.Commute first second) (element : G) :
    ∃ common left middle right : G,
      common ∈ commonFixed first second ∧
      left ∈ invertedFixed first second ∧
      middle ∈ invertedFixed second first ∧
      right ∈ invertedFixed (first * second) first ∧
      common * left * middle * right = element := by
  have hab : Commute first second := DFunLike.ext _ _ commuting
  obtain ⟨⟨h, x, y, z⟩, heq⟩ :=
    (MulAut.fixed_inverted_four_factor_bijective odd first second
      firstInvolutive secondInvolutive hab).surjective element
  refine ⟨h, x, y, z, ?_, x.property, ⟨y.property.2, y.property.1⟩, ?_, heq⟩
  · simpa [commonFixed] using h.property
  · exact ⟨by simp [MulAut.mul_apply, z.property.1, z.property.2], z.property.1⟩
end Theory.GroupAction.KleinFourDecomposition
