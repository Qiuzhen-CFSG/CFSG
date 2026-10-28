module
public import CFSG.Quasithin.ChapterD.Section02.Defs
public import Theory.Representation.BinaryOffender.PermutationConjugacy
public import Theory.Representation.BinaryOffender.QuadraticRatioTransport

/-!
# Conjugation preserves the bounded minimum-ratio family

The representation operator identifies fixed spaces of conjugate actors.
Conjugation preserves rank and the subgroup order, so it also preserves
minimum action ratio among nontrivial subgroups. This lets a small actor
be moved onto a selected component without changing its D.2.5 hypothesis.

Source: Aschbacher–Smith D.2.1–5, applied in 15.3.65, printed p.1152.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender
open scoped ENNReal
namespace CFSG.Quasithin.ChapterD
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V] (ρ : Representation (ZMod 2) G V)

/-- Conjugating an actor does not change its action ratio. -/
theorem actionRatio_map_conj (A : Subgroup G) (g : G) :
    actionRatio ρ (A.map (MulAut.conj g).toMonoidHom) = actionRatio ρ A := by
  unfold actionRatio
  rw [fixedCodim_map_conj,rank_map_conj]

/-- The bounded minimum-ratio family is closed under conjugation. -/
theorem RPlusBound.map_conj {A : Subgroup G} {r : ℝ≥0∞}
    (hA : A ∈ RPlusBound ρ r) (g : G) :
    A.map (MulAut.conj g).toMonoidHom ∈ RPlusBound ρ r := by
  let e := (MulAut.conj g).mapSubgroup
  refine ⟨⟨hA.1.1.map_conj g,?_⟩,hA.2.1.map_conj g,?_⟩
  · rw [actionRatio_map_conj]
    exact hA.1.2
  · intro B hBA hB
    have hle : e.symm B ≤ A := e.symm_apply_le.mpr hBA
    have hn : e.symm B ≠ ⊥ := by
      intro hh
      apply hB
      calc
        B = e (e.symm B) := (e.apply_symm_apply B).symm
        _ = ⊥ := by rw [hh,e.map_bot]
    have hr : actionRatio ρ B = actionRatio ρ (e.symm B) := by
      have h := actionRatio_map_conj ρ (e.symm B) g
      change actionRatio ρ (e (e.symm B)) = _ at h
      simpa only [e.apply_symm_apply] using h
    rw [actionRatio_map_conj,hr]
    exact hA.2.2 _ hle hn

end CFSG.Quasithin.ChapterD
