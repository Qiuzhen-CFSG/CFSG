module

public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.SylowOvergroups.EvenLieOvergroups.RankOneModels
public import CFSG.Quasithin.ClassicalModels
public import Theory.SpecificGroups.ClassicalUnitary.TheoremDRootNormalizer.BinaryForms
public import Theory.SpecificGroups.ClassicalUnitary.SylowOvergroupParabolics
public import Theory.GroupTheory.PCoreOvergroup
public import Theory.GroupTheory.GeneralizedFitting.SelfCentralizingPrimeCore

/-!
# Unitary models in the proper Sylow-overgroup argument

The dimension-two branch is proved by the actual PSU₂--PSL₂ comparison over
the fixed field. This retains every Hermitian form and every positive binary
parameter, including the field of order two.

For higher dimensions the geometric reduction below takes two independent
inputs: exhaustive placement of proper Sylow overgroups in isotropic-subspace
stabilizers, and self-centralization of the intrinsic two-cores of those
stabilizers. The parabolic core lies in the chosen Sylow and is normal in the
overgroup, so characteristic two descends to that overgroup and determines
its generalized Fitting subgroup. The geometric inputs remain explicit;
this reduction does not establish the higher-dimensional source theorem.

The final applications use the literal B.1.13 component intersection through
`eq_component_of_proper_sylow_fitting_bound`.
Source: Aschbacher--Smith B.1.13, printed p.74 (PDF p.85), and GLS3 §2.6.
-/

public section

open Subgroup Theory.GroupTheory BenderSuzuki.MatrixGroups
open Theory.SpecificGroups.UnitaryRootNormalizer

namespace CFSG.Quasithin.ChapterB.ComponentRecognition.SylowOvergroups

/-- The actual binary PSU₂ model satisfies the proper Sylow-overgroup bound. -/
theorem properSylowFittingBound_unitaryTwo {F : Type*} [Field F] [Finite F]
    (J : HermitianForm 2 F) (a : ℕ) (ha : 0 < a)
    (hcard : Nat.card F = (2 ^ a) ^ 2)
    (hconj : ∀ x, J.conj x = x ^ (2 ^ a)) :
    ProperSylowFittingBound (ProjectiveSpecialUnitaryMatrixGroup J) := by
  let : CharP F 2 := charP_binary ha hcard
  have hfixed := fixed_card_binary J ha hcard hconj
  obtain ⟨e⟩ := nonempty_projectiveTwoEquiv J hcard hfixed
  exact properSylowFittingBound_psl2 (FixedBy.subfield F J.conj) a ha hfixed e

/-- The catalogue's dimension-two unitary alias uses a proved model comparison. -/
theorem properSylowFittingBound_of_isPSU_two {L : Type*} [Group L] [Finite L]
    (a : ℕ) (ha : 0 < a) (hmodel : ClassicalGroup.IsPSU L 2 (2 ^ a)) :
    ProperSylowFittingBound L := by
  obtain ⟨F, hF, hfin, J, hcard, hconj, ⟨e⟩⟩ := hmodel
  exact properSylowFittingBound_of_equiv e
    (properSylowFittingBound_unitaryTwo J a ha hcard hconj)

namespace HigherUnitary

open Theory.SpecificGroups.ClassicalUnitary.SylowOvergroupParabolics

/-- Conditional assembly of the two concrete geometric calculations. The
placement clause covers arbitrary proper Sylow overgroups, without a solvability
or two-local premise. Both geometric inputs still require model proofs. -/
theorem properSylowFittingBound_of_isotropic_placement
    {F : Type*} [Field F] [Finite F] {d : ℕ} (J : HermitianForm d F)
    (hplacement : ∀ (S : Sylow 2 (ProjectiveSpecialUnitaryMatrixGroup J))
      (X : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)),
      (S : Subgroup _) ≤ X → X ≠ ⊤ →
      ∃ W : Submodule F (Fin d → F), W ≠ ⊥ ∧ W ≠ ⊤ ∧
        TotallyIsotropic J W ∧ X ≤ parabolic J W)
    (hcore : ∀ W : Submodule F (Fin d → F), W ≠ ⊥ → W ≠ ⊤ →
      TotallyIsotropic J W →
      centralizer (pCore 2 (parabolic J W) : Set (parabolic J W)) ≤
        pCore 2 (parabolic J W)) :
    ProperSylowFittingBound (ProjectiveSpecialUnitaryMatrixGroup J) := by
  intro S X hSX hX
  obtain ⟨W, hW, hWtop, hi, hXP⟩ := hplacement S X hSX hX
  have hlocal := centralizer_pCore_le_of_sylow_le
    (S.subtype (hSX.trans hXP)) (X.subgroupOf (parabolic J W))
    (by intro x hx; exact hSX hx) (hcore W hW hWtop hi)
  have hXcore := (Theory.Quasithin.centralizer_pCore_le_iff 2
    (subgroupOfEquivOfLe hXP)).mp hlocal
  rw [generalizedFitting_eq_pCore_of_selfCentralizing 2 hXcore]
  exact le_sup_left

/-- The geometric calculation, when supplied, discharges the exact source
component-equality premise after transport by the actual model equivalence. -/
theorem eq_component_of_isotropic_placement
    {G : Type*} [Group G] [Finite G]
    (K L : Subgroup G) (T : Sylow 2 G)
    (hL : IsComponent G L) (hLK : ⁅L, K⁆ = L)
    (hkind : IsQuasisimple K ∨ Nat.card K = 3)
    (hK : (K.subgroupOf (K ⊔ (T : Subgroup G))).IsSubnormal) (hKL : K ≤ L)
    {F : Type*} [Field F] [Finite F] {d : ℕ} (J : HermitianForm d F)
    (e : L ≃* ProjectiveSpecialUnitaryMatrixGroup J)
    (hplacement : ∀ (S : Sylow 2 (ProjectiveSpecialUnitaryMatrixGroup J))
      (X : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)),
      (S : Subgroup _) ≤ X → X ≠ ⊤ →
      ∃ W : Submodule F (Fin d → F), W ≠ ⊥ ∧ W ≠ ⊤ ∧
        TotallyIsotropic J W ∧ X ≤ parabolic J W)
    (hcore : ∀ W : Submodule F (Fin d → F), W ≠ ⊥ → W ≠ ⊤ →
      TotallyIsotropic J W →
      centralizer (pCore 2 (parabolic J W) : Set (parabolic J W)) ≤
        pCore 2 (parabolic J W)) : K = L :=
  eq_component_of_proper_sylow_fitting_bound K L T hL hLK hkind hK hKL
    (properSylowFittingBound_of_equiv e
      (properSylowFittingBound_of_isotropic_placement J hplacement hcore))

end HigherUnitary

/-- B.1.13 for an actual dimension-two binary unitary component. -/
theorem eq_component_of_isPSU_two {G : Type*} [Group G] [Finite G]
    (K L : Subgroup G) (T : Sylow 2 G)
    (hL : IsComponent G L) (hLK : ⁅L, K⁆ = L)
    (hkind : IsQuasisimple K ∨ Nat.card K = 3)
    (hK : (K.subgroupOf (K ⊔ (T : Subgroup G))).IsSubnormal) (hKL : K ≤ L)
    (a : ℕ) (ha : 0 < a) (hmodel : ClassicalGroup.IsPSU L 2 (2 ^ a)) : K = L :=
  eq_component_of_proper_sylow_fitting_bound K L T hL hLK hkind hK hKL
    (properSylowFittingBound_of_isPSU_two a ha hmodel)

end CFSG.Quasithin.ChapterB.ComponentRecognition.SylowOvergroups
