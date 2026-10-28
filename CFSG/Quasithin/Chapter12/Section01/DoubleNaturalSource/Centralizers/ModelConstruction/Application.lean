module

public import CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.Centralizers.ModelConstruction.Construction
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.DoubleNaturalExcludedCentralizers

/-!
# Discharging the H.9 model premise for the chosen doubled orbit

The chosen module provides the elementary-abelian structure on the literal
T-orbit. The constructed model then supplies the corrected H.9 adapted-vector
application, including the Sylow assertion for the original relative point
centralizer. The multiple-overgroup hypothesis is retained in the named source
entry point; model compatibility itself follows already from the doubled branch.

Source: Aschbacher--Smith, the opening of 12.1.1, printed p.788, using the
corrected H.9 marking rather than its incompatible fixed-vector version.
-/

public section

open Subgroup Theory.GroupTheory
open CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

theorem doubleNatural_sourceModel_of_many
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (_hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (B : DoubledBranch T L V n) :
    letI := D.doubledOrbit_elementary h
    Nonempty B.SourceModel := by
  let := D.doubledOrbit_elementary h
  exact B.nonempty_sourceModel

theorem doubleNatural_adapted_nonsingular_of_many
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (B : DoubledBranch T L V n) :
    letI := D.doubledOrbit_elementary h
    ∀ w : componentOrbit V (T : Subgroup G),
      B.quadratic (Additive.ofMul w) = 1 →
      ∃ l : L, ∃ w' : componentOrbit V (T : Subgroup G),
        (w' : G) = (l : G) * (w : G) * (l : G)⁻¹ ∧
        B.quadratic (Additive.ofMul w') = 1 ∧
        Chapter1.IsSylowIn 2 ((T : Subgroup G) ⊓ centralizer ({(w' : G)} : Set G))
          (normalizer (L : Set G) ⊓ centralizer ({(w' : G)} : Set G)) := by
  let := D.doubledOrbit_elementary h
  obtain ⟨S⟩ := doubleNatural_sourceModel_of_many h D hmany B
  exact doubleNatural_adapted_nonsingular_of_sourceModel h D B S

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
