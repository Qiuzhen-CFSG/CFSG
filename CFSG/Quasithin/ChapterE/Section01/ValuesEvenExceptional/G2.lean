module

public import CFSG.Quasithin.ChapterE.Section01.Basic
public import CFSG.Quasithin.ChapterE.Section01.ValuesEvenExceptional.G2.BinaryUpper
public import CFSG.Quasithin.ChapterE.Section01.ValuesEvenExceptional.G2.HigherUpper
public import CFSG.Quasithin.ChapterE.Section01.ValuesEvenExceptional.G2.LowerObstruction
public import Theory.AtlasPort.LinearGroups.G2.DerivedEvenOrder
public import Theory.GroupTheory.GeneralizedFitting.SelfCentralizing

/-!
# The derived G₂ value in E.1.14(1)

The source assumes an SQTK-group G with simple L = F*(G), G = L T, and an
actual equivalence L ≃ G₂(2^f)', for f > 0. Its generation parameter is f.
The proof needs only finiteness, simplicity of L, the supplement G = LT,
and the actual model equivalence; SQTK is not needed for this calculation.
Perfectness identifies the derived carrier with the full octonion model
only when f > 1; at f = 1 its order is 6048.

`binary_generation_inputs` proves even order and rank-one E-generation for
the entire ambient group in the binary case. Its proof constructs the two
T-overgroups from the restricted parabolics and proves their solvability.
Normality of F*(G), not a stronger assumption that G = L, supplies the
ambient conjugation action.

For f > 1, the two T-invariant parabolics have radical quotients with simple
PSL₂(2^f) socles. Their intrinsic E-generation transfers to G. The full ambient
conjugacy family of a highest-root group has a proper weak-closure normalizer
containing every E-member at rank f-1. These upper and lower calculations
include all outer two-extensions allowed by G = LT.

`generation_inputs` exposes even order, upper generation and the concrete
lower obstruction for the parent exceptional-value assembly. Their application
in `generationParameter_eq` determines the source minimum for every positive f,
using positivity at f = 1 and the obstruction at f > 1. This module imports
only the basic minimum specification, not the parent exceptional-value module.

Source: Aschbacher--Smith, *The Classification of Quasithin Groups*,
E.1.14(1), printed p.214 (PDF p.225), citing Aschbacher,
*GF(2)-representations of finite groups* (1982), Lemma 4.7. The actual model
and root calculations are imported from the licensed ATLAS port; see
LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/

public section
namespace CFSG.Quasithin.ChapterE.ExceptionalValues.G2

open Subgroup Atlas.G2 Atlas.G2.DerivedEvenOrder Theory.GroupTheory
variable {G F : Type*} [Group G] [Field F] [Finite F]

/-- An actual embedded derived model forces even ambient order for every
positive binary exponent, including the proper derived subgroup at f = 1. -/
theorem even_card_of_subgroup_equiv (L : Subgroup G) {f : ℕ} (hf : 0 < f)
    (hF : Nat.card F = 2 ^ f) (e : L ≃* commutator (Model F)) :
    Even (Nat.card G) := by
  apply even_iff_two_dvd.mpr
  apply dvd_trans _ L.card_subgroup_dvd_card
  rw [Nat.card_congr e.toEquiv]
  exact even_iff_two_dvd.mp (even_card_derived hf hF)

/-- The complete upper and parity inputs for the source's f = 1 endpoint.
The hypotheses of simplicity and SQTK are not needed for this specialization. -/
theorem binary_generation_inputs [Finite G] (hF : Nat.card F = 2)
    (T : Sylow 2 G) (e : generalizedFitting G ≃* commutator (Model F))
    (hLT : generalizedFitting G ⊔ (T : Subgroup G) = ⊤) :
    ¬ Odd (Nat.card G) ∧ IsEGenerated 1 G := by
  have heven := even_card_of_subgroup_equiv (generalizedFitting G)
    (by decide : 0 < 1) (by simpa using hF) e
  exact ⟨Nat.not_odd_iff_even.mpr heven, isEGenerated_one_of_binary_socle hF _ T e hLT⟩

variable [Finite G]

/-- The upper bound for every positive field exponent and every normal copy
of the derived model supplemented by T. At f = 1 the restricted parabolics
are solvable; at f > 1 their radical quotients supply the rank-f calculation.
No simplicity, SQTK or Sylow-alignment premise is needed. -/
theorem isEGenerated_of_derived_socle {f : ℕ} (hf : 0 < f)
    (hF : Nat.card F = 2 ^ f) (L : Subgroup G) [L.Normal]
    (T : Sylow 2 G) (e : L ≃* commutator (Model F))
    (hLT : L ⊔ (T : Subgroup G) = ⊤) : IsEGenerated f G := by
  by_cases h1 : f = 1
  · subst f
    exact isEGenerated_one_of_binary_socle (by simpa using hF) L T e hLT
  · exact isEGenerated_of_higher_socle (by omega) hF L T e hLT

/-- All inputs to the G₂ minimum calculation in E.1.14(1), in the original
ambient group G = F*(G)T. For f > 1 the full ambient root family and its proper
trapping subgroup are constructed from the actual model equivalence. At f = 1
even order and upper generation suffice. No local-generation, confinement,
full-model identification or outer-action premise remains. -/
theorem generation_inputs (T : Sylow 2 G)
    [IsSimpleGroup (generalizedFitting G)]
    (hLT : generalizedFitting G ⊔ (T : Subgroup G) = ⊤)
    {f : ℕ} (hf : 0 < f) (hF : Nat.card F = 2 ^ f)
    (e : generalizedFitting G ≃* commutator (Model F)) :
    ¬ Odd (Nat.card G) ∧ IsEGenerated f G ∧
      (1 < f → ∃ (Ω : Set (Subgroup G)) (M : Subgroup G),
        IsElementaryFamily Ω ∧ M ≠ ⊤ ∧
        normalizer (weakClosure (T : Subgroup G) Ω : Set G) ≤ M ∧
        ∀ A : Subgroup G, A ∈ Ω → A ≤ (T : Subgroup G) →
          ∀ K : Subgroup G, IsEMemberAt (f - 1) (T : Subgroup G) A K → K ≤ M) := by
  exact ⟨Nat.not_odd_iff_even.mpr (even_card_of_subgroup_equiv _ hf hF e),
    isEGenerated_of_derived_socle hf hF _ T e hLT,
    fun hhigher => LowerObstruction.exists_lower_obstruction T hLT hhigher hF e⟩

/-- E.1.14(1) for the actual derived G₂ model, including q = 2 and every
almost-simple outer two-extension allowed by G = LT. The upper bound attains
the minimum, and the full ambient highest-root family excludes every smaller
positive rank. -/
theorem generationParameter_eq (T : Sylow 2 G)
    [IsSimpleGroup (generalizedFitting G)]
    (hLT : generalizedFitting G ⊔ (T : Subgroup G) = ⊤)
    {f : ℕ} (hf : 0 < f) (hF : Nat.card F = 2 ^ f)
    (e : generalizedFitting G ≃* commutator (Model F)) :
    generationParameter G = f := by
  obtain ⟨heven, hupper, hlower⟩ := generation_inputs T hLT hf hF e
  have hspec := generationParameter_spec heven ⟨f, hf, hupper⟩
  apply Nat.le_antisymm (generationParameter_le hf hupper)
  by_cases h1 : f = 1
  · omega
  · by_contra h
    obtain ⟨Ω, M, hΩ, hM, hnorm, hmembers⟩ := hlower (by omega)
    obtain ⟨A, hA, hAT, K, hK, hKM⟩ :=
      ((hspec.2 T).mono (show generationParameter G ≤ f - 1 by omega)).exists_member_not_le
        Ω hΩ M hM hnorm
    exact hKM (hmembers A hA hAT K hK)

end CFSG.Quasithin.ChapterE.ExceptionalValues.G2
