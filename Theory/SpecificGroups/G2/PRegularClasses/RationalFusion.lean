module

public import Theory.SpecificGroups.G2.PRegularClasses.RationalFusion.TorusSeparation
public import Theory.SpecificGroups.G2.PRegularClasses.RationalFusion.Frobenius
public import Theory.SpecificGroups.G2.PRegularClasses.RationalFusion.CentralizerLang

/-!
# Rational G₂ conjugacy from characteristic polynomials

Equal octonion characteristic polynomials give conjugacy over the algebraic
closure from the stated geometric torus-normal-form hypothesis. This uses the
proved separation of split torus elements by the actual octonion Weyl maps,
including repeated eigenvalues.

Rational conjugacy additionally follows from the centralizer Lang equation:
the Frobenius discrepancy of an algebraic conjugator centralizes the first
element, and a Lang solution corrects that conjugator to a rational one.
The identity case needs no Lang equation. The imported centralizer theorem
solves the equation for all nonidentity odd-order elements, including repeated
eigenvalues and order three. Thus `isConj_of_charpoly_eq` retains only the
geometric torus-normal-form hypothesis, with no lower bound on the finite
field's cardinality. The corrected conjugator preserves octonion multiplication
and lies in the actual finite-field model.

Sources: Steinberg, `refs/KGroup/GLS3/Chapter2St2.tex`, 8.1, 10.1 and 12.5;
the semisimple geometry underlying GLS III, Section 2.8, used in
Aschbacher--Smith G.9.3, printed pp.356–357 of `refs/quasithin.pdf`.
-/

public section

namespace Atlas.G2.PRegularClasses.RationalFusion

open FieldExtension

variable {F : Type*} [Field F] [CharP F 2]

/-- The allowed geometric normal form suffices for conjugacy over the
algebraic closure, with no extra torus-separation premise. -/
theorem extension_isConj_of_charpoly_eq
    (hgeom : ∀ x : Model (AlgebraicClosure F), ¬ 2 ∣ orderOf x →
      ∃ l m : (AlgebraicClosure F)ˣ, IsConj x (torus l m))
    (g h : Model F) (hg : ¬ 2 ∣ orderOf g) (hh : ¬ 2 ∣ orderOf h)
    (hp : charpoly g = charpoly h) :
    IsConj (fieldEmbedding (algebraMap F (AlgebraicClosure F)) g)
      (fieldEmbedding (algebraMap F (AlgebraicClosure F)) h) := by
  apply isConj_of_charpoly_eq_of_torus_normal_form hgeom
  · simpa only [fieldEmbedding_orderOf] using hg
  · simpa only [fieldEmbedding_orderOf] using hh
  · simp only [fieldEmbedding_charpoly, hp]

/-- Assembly of rational fusion from geometric normal form and explicit
centralizer Lang equations. Only nonidentity elements need an equation. -/
theorem isConj_of_charpoly_eq_of_centralizer_lang [Finite F]
    (hgeom : ∀ x : Model (AlgebraicClosure F), ¬ 2 ∣ orderOf x →
      ∃ l m : (AlgebraicClosure F)ˣ, IsConj x (torus l m))
    (hLang : ∀ g : Model F, ¬ 2 ∣ orderOf g → g ≠ 1 →
      ∀ z : Model (AlgebraicClosure F),
        Commute z (fieldEmbedding (algebraMap F (AlgebraicClosure F)) g) →
        ∃ u : Model (AlgebraicClosure F),
          Commute u (fieldEmbedding (algebraMap F (AlgebraicClosure F)) g) ∧
          u * (frobenius F u)⁻¹ = z)
    (g h : Model F) (hg : ¬ 2 ∣ orderOf g) (hh : ¬ 2 ∣ orderOf h)
    (hp : charpoly g = charpoly h) : IsConj g h := by
  have hc := extension_isConj_of_charpoly_eq hgeom g h hg hh hp
  by_cases hg1 : g = 1
  · have hh1 : h = 1 := by
      apply fieldEmbedding_injective (algebraMap F (AlgebraicClosure F))
      rw [hg1, map_one] at hc
      simpa only [map_one] using isConj_one_right.mp hc
    rw [hg1, hh1]
  · exact isConj_of_extension_of_centralizer_lang F g h hc (hLang g hg hg1)

/-- Odd-order elements of the actual finite-field G₂ model with equal
octonion characteristic polynomials are conjugate, assuming only geometric
torus normal form over the algebraic closure. The centralizer Lang equations
and rational descent are discharged, including the nonregular cases. -/
theorem isConj_of_charpoly_eq [Finite F]
    (hgeom : ∀ x : Model (AlgebraicClosure F), ¬ 2 ∣ orderOf x →
      ∃ l m : (AlgebraicClosure F)ˣ, IsConj x (torus l m))
    (g h : Model F) (hg : ¬ 2 ∣ orderOf g) (hh : ¬ 2 ∣ orderOf h)
    (hp : charpoly g = charpoly h) : IsConj g h := by
  exact isConj_of_charpoly_eq_of_centralizer_lang hgeom
    (CentralizerLang.exists_lang F hgeom) g h hg hh hp

end Atlas.G2.PRegularClasses.RationalFusion
