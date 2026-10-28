module
public import CFSG.Quasithin.ChapterA.Section03.SQTKStructure.OrdinarySource.Basic
public import Theory.SpecificGroups.PSL3.OrdinaryCenterRecognition
public import Theory.SpecificGroups.PSL3.BinaryOddCenterCover
public import Theory.Alternating.OddCentralCovers
/-!
# Linear ordinary components in A.3.6

The ordinary Steinberg presentation supplies the actual SL₃ scalar
cover. Its center has order one or three. The exceptional binary fields
use their separately proved covering calculations.
Every branch supplies the full common Fitting and radical conclusion.

Source: Aschbacher–Smith A.3.6 and I.1.3, printed pp.43–45, 407.
-/

public section
noncomputable section
open Subgroup Theory.GroupTheory PerfectCentralCovering
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterA.SQTKStructure.OrdinarySource
open Chapter1.Section02 Chapter1.Section02.LocalModels

private theorem linear_ordinary {X : Type*} [Group X] [Finite X]
    (L : Subgroup X) (hL : IsComponent X L)
    (F : Type) [Field F] [Finite F] (h2 : Nat.card F ≠ 2) (h4 : Nat.card F ≠ 4)
    (e : L ⧸ center L ≃* PSL(3,F))
    (hmodel : ∀ _j : L ≃* PSL(3,F), TheoremCModel L)
    (hparam : Nat.card F % 3 = 1 → CoverParameter false (Nat.card F)) :
    A36Conclusion L := by
  let : IsQuasisimple L := hL.2
  let : IsSimpleGroup (L ⧸ center L) := IsQuasisimple.simple
  let : IsSimpleGroup PSL(3,F) := e.symm.isSimpleGroup
  by_cases hz : center L = ⊥
  · let j : L ≃* PSL(3,F) := QuotientGroup.quotientBot.symm.trans
      ((QuotientGroup.quotientMulEquivOfEq hz.symm).trans e)
    let : IsSimpleGroup L := j.isSimpleGroup
    exact simple_conclusion L hL (hmodel j)
  · obtain ⟨hc, hm, he, j, _⟩ :=
      Matrix.PSL3.OrdinaryCenterRecognition.nontrivial_center_recognition h2 h4 e hz
    exact ⟨.cover hL he (.classical false (Nat.card F) (hparam hm)
        ⟨F, inferInstance, inferInstance, rfl, ⟨j.symm⟩⟩),
      ReadyCoverCases.common_of_quasisimple (even_of_quasisimple L) (Or.inr hc)⟩

/-- The complete linear degree-three branch at every binary parameter.
The exceptional fields are treated by their genuine covering calculations. -/
theorem a36_linear_even {X : Type*} [Group X] [Finite X]
    (hcore : pCore 2 X = ⊥) (L : Subgroup X) (hL : IsComponent X L)
    (n : ℕ) (hn : 1 ≤ n) (F : Type) [Field F] [Finite F]
    (hF : Nat.card F = 2 ^ n) (e : L ⧸ center L ≃* PSL(3,F)) :
    A36Conclusion L := by
  let : IsQuasisimple L := hL.2
  let : IsSimpleGroup (L ⧸ center L) := IsQuasisimple.simple
  let : IsSimpleGroup PSL(3,F) := e.symm.isSimpleGroup
  have hmodel (j : L ≃* PSL(3,F)) : TheoremCModel L :=
    .rank_two (.linear n hn ⟨F, inferInstance, inferInstance, hF, ⟨j⟩⟩)
  by_cases h2 : Nat.card F = 2
  · have hz := Matrix.PSL3.BinaryOddCenterCover.center_eq_bot_two h2 e
      (GLS3.Chapter5.OddCentralCovers.component_center_odd hcore L hL)
    let j : L ≃* PSL(3,F) := QuotientGroup.quotientBot.symm.trans
      ((QuotientGroup.quotientMulEquivOfEq hz.symm).trans e)
    let : IsSimpleGroup L := j.isSimpleGroup
    exact simple_conclusion L hL (hmodel j)
  by_cases h4 : Nat.card F = 4
  · have hc : pCore 2 L = ⊥ := by
      rw [pCore_subnormal_eq_comap 2 hL.1, hcore, MonoidHom.comap_bot]
      exact L.subtype.ker_eq_bot_iff.mpr L.subtype_injective
    exact ReadyCoverCases.a36_psl3_four L hL hc F h4 e
  exact linear_ordinary L hL F h2 h4 e hmodel
    (fun hm => Or.inl ⟨n, hn, hF, hm⟩)

/-- The complete linear degree-three branch at an odd prime parameter. -/
theorem a36_linear_odd_prime {X : Type*} [Group X] [Finite X]
    (L : Subgroup X) (hL : IsComponent X L)
    (p : ℕ) (hp : p.Prime) (ho : Odd p) (F : Type) [Field F] [Finite F]
    (hF : Nat.card F = p) (e : L ⧸ center L ≃* PSL(3,F)) :
    A36Conclusion L := by
  have h2 : Nat.card F ≠ 2 := by rw [hF]; rintro rfl; norm_num at ho
  have h4 : Nat.card F ≠ 4 := by rw [hF]; rintro rfl; norm_num at hp
  apply linear_ordinary L hL F h2 h4 e
  · intro j
    exact .three_odd p hp ho false ⟨F, inferInstance, inferInstance, hF, ⟨j⟩⟩
  · intro _
    exact Or.inr (hF.symm ▸ ⟨hp, ho⟩)
end CFSG.Quasithin.ChapterA.SQTKStructure.OrdinarySource
