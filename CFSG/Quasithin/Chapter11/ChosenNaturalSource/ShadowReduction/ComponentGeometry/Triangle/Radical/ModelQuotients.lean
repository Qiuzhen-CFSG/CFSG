module

public import CFSG.Quasithin.Chapter11.Section01To02.SourceDefs
public import Theory.SpecificGroups.SL2.ResidualTwoExtension
public import Theory.GroupTheory.SolvableRadical.NormalTwoExtension
public import Theory.GroupTheory.CComponent.Radical
public import Theory.GroupTheory.SolvableRadical.SolvableKernel

/-!
# The actual radical quotients in the surviving cases

For the two-odd SL₂ quotient, its kernel is a proper normal subgroup of
the C-component and is therefore solvable. Passing through this literal
quotient identifies the radical quotient with PSL₂. For the PSL₂
two-core quotient, perfectness makes the radical equal to the two-core.
These are the model inputs for the automorphism calculation in 11.4.1(3).
Source: Aschbacher--Smith 11.1.2(1--2), p.762, and 11.4.1, p.776.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Radical
variable {G : Type*} [Group G] [Finite G] {K : Subgroup G}

/-- The SL₂ alternative induces an actual isomorphism on radical quotients. -/
theorem radical_model_of_twoOdd_sl2 (hK : K.IsCComponent) {p : ℕ} (hp : 3 < p)
    (hm : Source.IsSL (Source.TwoOddQuotient K) 2 p) :
    ClassicalGroup.IsPSL (K ⧸ solvableRadical K) 2 p := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hm
  let Q := Source.TwoOddQuotient K
  let q : K →* Q := (QuotientGroup.mk' (pPrimeCore 2 (K ⧸ pCore 2 K))).comp
    (QuotientGroup.mk' (pCore 2 K))
  have hq : Function.Surjective q :=
    (QuotientGroup.mk'_surjective _).comp (QuotientGroup.mk'_surjective _)
  let : IsQuasisimple Q := Theory.SpecificGroups.SL2.ResidualTwoExtension.quasisimple_of_equiv
    (by omega) e
  let : IsSimpleGroup (Q ⧸ center Q) := IsQuasisimple.simple
  let : Nontrivial Q := Function.Surjective.nontrivial
    (QuotientGroup.mk'_surjective (center Q))
  have hproper : q.ker ≠ ⊤ := by
    intro he
    have hsub : Subsingleton Q := by
      refine ⟨fun a b => ?_⟩
      obtain ⟨x, rfl⟩ := hq a
      obtain ⟨y, rfl⟩ := hq b
      exact (show q x = 1 from (show x ∈ q.ker from he.symm ▸ mem_top x)).trans
        (show q y = 1 from (show y ∈ q.ker from he.symm ▸ mem_top y)).symm
    exact not_subsingleton Q hsub
  let : Group.IsSolvable q.ker :=
    hK.isSolvable_of_subnormal_lt_top (inferInstance : q.ker.Normal).isSubnormal hproper
  exact ⟨F, inferInstance, inferInstance, hF,
    ⟨(solvableRadicalQuotientEquiv q hq).trans
      (Theory.SpecificGroups.SL2.ResidualTwoExtension.radicalQuotientEquiv (by omega) e)⟩⟩

/-- Perfectness and the genuine simple PSL₂ quotient identify the radical. -/
theorem radical_eq_core_of_psl2 [Group.IsPerfect K] {p : ℕ} (hp : 3 < p)
    (hm : ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 2 p) :
    solvableRadical K = pCore 2 K := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hm
  let : IsSimpleGroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) :=
    Matrix.ProjectiveSpecialLinearGroup.rank_two_simple (by omega)
  let : IsSimpleGroup (K ⧸ pCore 2 K) := e.isSimpleGroup
  exact radical_eq_core_of_perfect_simple_core_quotient

/-- The PSL₂ alternative uses the same quotient, after the proved radical equality. -/
theorem radical_model_of_psl2 [Group.IsPerfect K] {p : ℕ} (hp : 3 < p)
    (hm : ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 2 p) :
    ClassicalGroup.IsPSL (K ⧸ solvableRadical K) 2 p := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hm
  exact ⟨F, inferInstance, inferInstance, hF,
    ⟨(QuotientGroup.quotientMulEquivOfEq
      (radical_eq_core_of_psl2 hp ⟨F, inferInstance, inferInstance, hF, ⟨e⟩⟩)).trans e⟩⟩

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Radical
