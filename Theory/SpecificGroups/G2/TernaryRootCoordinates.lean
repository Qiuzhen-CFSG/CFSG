module
public import Theory.GroupAction.TernaryCubicCoordinates
public import Theory.SpecificGroups.G2.TernaryLevi
public import Theory.SpecificGroups.GL2.ThreeConjugacy

/-!
# The literal ternary G₂ root action in Jordan coordinates

Explicit changes of coordinates identify the length-three-plus-one Jordan
operator with each Atlas root convention. Thus any nonquadratic cubic on
elementary eighty-one has a constructed equivalence with the short or long
root action. The double-displacement formulas retain the actual coordinate
line. The original-group consumer is G2Recognition.MaximalCubicCoordinates.

The GL₂(3) conjugacy calculation also puts an arbitrary order-three actor
at the specified positive root generator. The Weyl action and commutator
form still require separate compatibility proofs for I.4.5, printed p.417.

The root conventions are from the licensed Atlas split-octonion port,
revision 8eabb35afe2b5e45bf913a2d05c53e558d2e2917. Attribution and license:
LICENSES/ATLAS-CITATION.cff and LICENSES/ATLAS.txt.
-/

public section
open Atlas.G2
namespace Atlas.G2.TernaryCore

private def shortJordanChange : V ≃* V where
  toFun x := Multiplicative.ofAdd ![-x.toAdd 1-x.toAdd 3,
    -x.toAdd 0+x.toAdd 1,-x.toAdd 1,x.toAdd 2]
  invFun x := Multiplicative.ofAdd ![-x.toAdd 1-x.toAdd 2,
    -x.toAdd 2,x.toAdd 3,-x.toAdd 0+x.toAdd 2]
  left_inv x := by
    apply Multiplicative.toAdd.injective
    funext i
    fin_cases i <;> simp
  right_inv x := by
    apply Multiplicative.toAdd.injective
    funext i
    fin_cases i <;> simp
  map_mul' x y := by
    apply Multiplicative.toAdd.injective
    funext i
    fin_cases i <;> simp <;> ring

private theorem shortJordanChange_action (x : V) :
    shortJordanChange (Multiplicative.ofAdd ![x.toAdd 0+x.toAdd 1,
      x.toAdd 1+x.toAdd 2,x.toAdd 2,x.toAdd 3])=shortRoot (shortJordanChange x) := by
  apply Multiplicative.toAdd.injective
  funext i
  fin_cases i <;> simp [shortJordanChange,shortRoot] <;> ring_nf

private def longJordanChange : V ≃* V where
  toFun x := Multiplicative.ofAdd ![-x.toAdd 0+x.toAdd 1-x.toAdd 3,
    x.toAdd 1,x.toAdd 1-x.toAdd 3,x.toAdd 2]
  invFun x := Multiplicative.ofAdd ![-x.toAdd 0+x.toAdd 2,
    x.toAdd 1,x.toAdd 3,x.toAdd 1-x.toAdd 2]
  left_inv x := by
    apply Multiplicative.toAdd.injective
    funext i
    fin_cases i <;> simp
  right_inv x := by
    apply Multiplicative.toAdd.injective
    funext i
    fin_cases i <;> simp
    ring
  map_mul' x y := by
    apply Multiplicative.toAdd.injective
    funext i
    fin_cases i <;> simp <;> ring

private theorem longJordanChange_action (x : V) :
    longJordanChange (Multiplicative.ofAdd ![x.toAdd 0+x.toAdd 1,
      x.toAdd 1+x.toAdd 2,x.toAdd 2,x.toAdd 3])=longRoot (longJordanChange x) := by
  apply Multiplicative.toAdd.injective
  funext i
  fin_cases i <;> simp [longJordanChange,longRoot] <;> ring

variable {A : Type*} [Group A] [Finite A] [IsElementaryAbelian 3 A]

/-- An actual nonquadratic cubic is conjugate to the literal short-root action. -/
theorem exists_shortRoot_coordinates (a : MulAut A) (ha : a^3=1) (hc : Nat.card A=81)
    (hne : ∃ v : A,a (a v*v⁻¹)*(a v*v⁻¹)⁻¹≠1) :
    ∃ e : A ≃* V, ∀ v,e (a v)=shortRoot (e v) := by
  obtain ⟨e,he⟩ := Theory.GroupAction.TernaryCubicCoordinates.exists_coordinates a ha hc hne
  refine ⟨e.trans shortJordanChange,?_⟩
  intro v
  change shortJordanChange (e (a v))=shortRoot (shortJordanChange (e v))
  rw [he,shortJordanChange_action]

/-- The same construction with the literal long-root coordinate convention. -/
theorem exists_longRoot_coordinates (a : MulAut A) (ha : a^3=1) (hc : Nat.card A=81)
    (hne : ∃ v : A,a (a v*v⁻¹)*(a v*v⁻¹)⁻¹≠1) :
    ∃ e : A ≃* V, ∀ v,e (a v)=longRoot (e v) := by
  obtain ⟨e,he⟩ := Theory.GroupAction.TernaryCubicCoordinates.exists_coordinates a ha hc hne
  refine ⟨e.trans longJordanChange,?_⟩
  intro v
  change longJordanChange (e (a v))=longRoot (longJordanChange (e v))
  rw [he,longJordanChange_action]

/-- The short-root square displacement is its second coordinate line. -/
theorem shortRoot_double (v : V) :
    shortRoot (shortRoot v*v⁻¹)*(shortRoot v*v⁻¹)⁻¹=
      Multiplicative.ofAdd ![0,-v.toAdd 3,0,0] := by
  apply Multiplicative.toAdd.injective
  funext i
  fin_cases i <;> simp [shortRoot,Matrix.vecHead,Matrix.vecTail] <;> ring

/-- The long-root square displacement is its first coordinate line. -/
theorem longRoot_double (v : V) :
    longRoot (longRoot v*v⁻¹)*(longRoot v*v⁻¹)⁻¹=
      Multiplicative.ofAdd ![-v.toAdd 3,0,0,0] := by
  apply Multiplicative.toAdd.injective
  funext i
  fin_cases i <;> simp [longRoot,Matrix.vecHead,Matrix.vecTail]
  ring

end Atlas.G2.TernaryCore
namespace Atlas.G2.TernaryLevi

/-- All order-three actors are conjugate to the specified positive-root generator. -/
theorem isConj_generator_of_order_three (a : GL23) (ha : orderOf a=3) :
    IsConj a (generator false) := by
  obtain ⟨i,hi,_⟩ := Matrix.GeneralLinearGroup.three_conjugacy_data.1 a
  obtain ⟨g,hg⟩ := isConj_iff.mp hi
  have ho : orderOf a=orderOf (Matrix.GeneralLinearGroup.threeClassRepr i) := by
    rw [←hg]
    exact ((MulAut.conj g).orderOf_eq a).symm
  rw [ha,Matrix.GeneralLinearGroup.three_conjugacy_data.2.1] at ho
  have he : i=3 := (by decide : ∀ j : Fin 8,
    3 = ![1,2,4,3,6,2,8,8] j → j=3) i ho
  subst i
  apply hi.trans
  apply isConj_iff.mpr
  exact ⟨Matrix.GeneralLinearGroup.threeReflection,by decide +kernel⟩

end Atlas.G2.TernaryLevi
