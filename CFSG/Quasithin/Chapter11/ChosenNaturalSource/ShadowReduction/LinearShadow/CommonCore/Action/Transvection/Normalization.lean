module

public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.CommonCore.Action.GeometryReductions
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry
public import CFSG.Quasithin.ChapterE.Section03.Parameters.Global

/-!
# Normalization before the transvection calculation

The corank bound of 11.2.2(3) controls the centralizer of C_A(V_H).
The exceptional equality case is impossible because the original flag line
lies in its plane and Hypothesis 11.3.1 controls the line centralizer in the
linear case. Thus V_H normalizes the actual selected conjugate A. This is
normalization in G, before any choice of coordinates on the conjugate.

The numerical alternative and action corank remain the exact earlier-source
inputs, from 11.2.2 and the selected Sylow image in 11.3.7 respectively.
This does not assume or establish the subsequent transvection recognition.

Source: Aschbacher--Smith, combined manuscript, 1 March 2004,
11.3.7(4), printed p.773, using 11.2.2(3), printed pp.767--768.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
open CFSG.Quasithin.ChapterE
open CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.CommonCore
variable {G : Type*} [Group G] {V W : Subgroup G}

/-- Centralizer control applies to the literal kernel on the conjugate. -/
theorem normalizes_conjugate_of_action_corank (g : G) {n : ℕ}
    (hr : (n : ℕ∞) < globalR V)
    (hc : subgroupCorank (V.map (MulAut.conj g).toMonoidHom)
      (V.map (MulAut.conj g).toMonoidHom ⊓ centralizer (W : Set G)) ≤ n) :
    W ≤ normalizer (V.map (MulAut.conj g).toMonoidHom : Set G) := by
  apply (le_centralizer_iff.mpr inf_le_right).trans
  apply centralizer_le_normalizer_of_corank_lt_globalR inf_le_left
  rw [globalR_map_equiv]
  exact lt_of_le_of_lt (by exact_mod_cast hc) hr

variable [Finite G] {T : Sylow 2 G} {L H : Subgroup G}
    {D : Chapter12.Section02.ChosenModule T L V} {S : D.NonbinaryNaturalInput}
    {U₁ : Submodule (ZMod 2) D.chosenCentralQuotient}

/-- The original flag and source centralizer assumption exclude the exceptional
corank equality, so the original V_H normalizes the selected A = V^g. -/
theorem source_omegaClosure_normalizes_conjugate
    (s : Hypothesis1131At D S U₁ H)
    (c : Coordinates D S.field) (f : InvariantFlag c)
    (hline : U₁ = c.binarySubspace (f.space 0))
    (hparameters : (S.field.degree : ℕ∞) < globalR V ∨
      (Source.IsSL (L ⧸ pCore 2 L) 3 (2 ^ S.field.degree) ∧
        globalR V = S.field.degree ∧
        ¬ centralizer (f.Vi 1 : Set G) ≤ normalizer (L : Set G)))
    (g : G)
    (hc : subgroupCorank (V.map (MulAut.conj g).toMonoidHom)
      (V.map (MulAut.conj g).toMonoidHom ⊓ centralizer (omegaClosure T H : Set G)) ≤
        S.field.degree) :
    omegaClosure T H ≤ normalizer (V.map (MulAut.conj g).toMonoidHom : Set G) := by
  apply normalizes_conjugate_of_action_corank g ?_ hc
  rcases hparameters with hr | ⟨hsl, _, hcentralizer⟩
  · exact hr
  · apply (hcentralizer ?_).elim
    have hV₁ : D.centralQuotientPreimage U₁ = f.Vi 0 := by
      rw [hline]
      rfl
    exact (centralizer_le (hV₁ ▸ f.Vi_mono (show (0 : Fin 3) ≤ 1 by decide))).trans
      (s.linear_centralizer hsl)

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.CommonCore
