module

public import Theory.SpecificGroups.G2.PRegularClasses.Torus
public import Theory.SpecificGroups.G2.PRegularClasses.GeometricTorus
public import Theory.SpecificGroups.G2.PRegularClasses.RationalFusion

/-!
# Counting odd-order conjugacy classes in the actual G₂ model

For every finite field F of characteristic two, the actual split-octonion
automorphism group has at most |F|² odd-order conjugacy classes. The two
characteristic-polynomial coefficients define an invariant on the literal
conjugacy-class quotient. Geometric torus conjugacy over the algebraic closure
and polynomial descent prove the rank-two polynomial form. Rational fusion
then shows that these coefficients separate odd-order classes inside G₂,
giving an injection into `F × F`.

The conditional counting lemmas are retained as general interfaces. The final
theorems discharge their premises using the imported geometric and rational
conjugacy results. No representation-classification or class-count premise is
used, and no lower bound on |F| is required.

Source context: GLS III, 2.8.2 (`refs/KGroup/GLS3/chapter2.tex`) and
Aschbacher--Smith, G.9.3, printed pp.356--357 of `refs/quasithin.pdf`.
-/

public section

namespace Atlas.G2.PRegularClasses

variable {F : Type*} [Field F]

/-- The actual coefficient invariant separates odd-order classes once the
polynomial-shape and rational-conjugacy theorems have been supplied. -/
theorem classParameters_injOn_pRegular_of_charpoly
    (hshape : ∀ g : Model F, ¬ 2 ∣ orderOf g →
      charpoly g = classPolynomial ((charpoly g).coeff 7) ((charpoly g).coeff 6))
    (hconj : ∀ g h : Model F, ¬ 2 ∣ orderOf g → ¬ 2 ∣ orderOf h →
      charpoly g = charpoly h → IsConj g h) :
    Set.InjOn classParameters (ConjClasses.mk '' {g : Model F | ¬ 2 ∣ orderOf g}) := by
  rintro _ ⟨g, hg, rfl⟩ _ ⟨h, hh, rfl⟩ he
  apply ConjClasses.mk_eq_mk_iff_isConj.mpr
  apply hconj g h hg hh
  have h₁ : (charpoly g).coeff 7 = (charpoly h).coeff 7 := congrArg Prod.fst he
  have h₂ : (charpoly g).coeff 6 = (charpoly h).coeff 6 := congrArg Prod.snd he
  rw [hshape g hg, h₁, h₂, ← hshape h hh]

/-- Conditional counting assembly, on the full octonion automorphism model
and its actual `ConjClasses.mk` image. Both geometric premises remain explicit. -/
theorem card_pRegularConjClasses_le_of_charpoly [Finite F]
    (hshape : ∀ g : Model F, ¬ 2 ∣ orderOf g →
      charpoly g = classPolynomial ((charpoly g).coeff 7) ((charpoly g).coeff 6))
    (hconj : ∀ g h : Model F, ¬ 2 ∣ orderOf g → ¬ 2 ∣ orderOf h →
      charpoly g = charpoly h → IsConj g h) :
    Nat.card (ConjClasses.mk '' {g : Model F | ¬ 2 ∣ orderOf g}) ≤ Nat.card F ^ 2 := by
  have hi : Function.Injective (fun c : (ConjClasses.mk ''
      {g : Model F | ¬ 2 ∣ orderOf g}) => classParameters c.val) :=
    fun c d h => Subtype.ext
      (classParameters_injOn_pRegular_of_charpoly hshape hconj c.property d.property h)
  simpa only [Nat.card_prod, pow_two] using Nat.card_le_card_of_injective _ hi

variable [CharP F 2]

/-- Every odd-order octonion automorphism has the rank-two polynomial form.
The torus representative is taken over the algebraic closure, and the
identity descends to the original field. -/
theorem charpoly_eq_classPolynomial_of_odd_order (g : Model F)
    (hg : ¬ 2 ∣ orderOf g) :
    charpoly g = classPolynomial ((charpoly g).coeff 7) ((charpoly g).coeff 6) := by
  exact charpoly_eq_classPolynomial_of_torus_conjugacy
    (algebraMap F (AlgebraicClosure F)) isConj_torus_of_odd_order g hg

/-- Over a finite field of characteristic two, equal octonion characteristic
polynomials give conjugacy of odd-order elements inside the actual G₂ model. -/
theorem isConj_of_charpoly_eq [Finite F] (g h : Model F)
    (hg : ¬ 2 ∣ orderOf g) (hh : ¬ 2 ∣ orderOf h)
    (hp : charpoly g = charpoly h) : IsConj g h := by
  exact RationalFusion.isConj_of_charpoly_eq isConj_torus_of_odd_order g h hg hh hp

/-- The two coefficients separate the literal odd-order conjugacy classes. -/
theorem classParameters_injOn_pRegular [Finite F] :
    Set.InjOn classParameters (ConjClasses.mk '' {g : Model F | ¬ 2 ∣ orderOf g}) := by
  exact classParameters_injOn_pRegular_of_charpoly
    charpoly_eq_classPolynomial_of_odd_order isConj_of_charpoly_eq

/-- The actual finite G₂ model has at most |F|² odd-order conjugacy classes.
This bound is independent of tensor-representation exhaustivity. -/
theorem card_pRegularConjClasses_le [Finite F] :
    Nat.card (ConjClasses.mk '' {g : Model F | ¬ 2 ∣ orderOf g}) ≤ Nat.card F ^ 2 := by
  exact card_pRegularConjClasses_le_of_charpoly
    charpoly_eq_classPolynomial_of_odd_order isConj_of_charpoly_eq

end Atlas.G2.PRegularClasses
