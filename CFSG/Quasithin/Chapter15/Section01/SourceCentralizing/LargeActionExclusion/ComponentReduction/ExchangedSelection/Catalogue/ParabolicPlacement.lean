module

public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.ExchangedSelection.Catalogue.ParabolicPlacement.CentralizerReduction
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.ExchangedSelection.Catalogue.ParabolicPlacement.CentralSeed
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.ExchangedSelection.Catalogue.ParabolicPlacement.ResidualGeneration

/-!
# The common family argument of original 15.1.22

Apply the parabolic residual-supplement theorem to an actual family
escaping M_L. Once (*) places its escaping members in M, the original
O^{3′}(M ∩ L) escapes M_L too. The literal normalizer-quotient calculation
then finishes (!) from the two earlier plus-geometry facts.

The same-pair placement (*) and the source lifting/normalization steps
of (**) remain explicit inputs. This is their common downstream assembly,
not an assertion that those source results have already been established.
The order-two omega-center and the escaping family are the intended
model-specific inputs. Source: Aschbacher--Smith, printed pp.1098--1099.
-/

public section
open Subgroup Representation Representation.BinaryOffender Stellmacher Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section01.CaseIComponentData
open Section03 Section03.InitialSource ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V : Subgroup G} {p : ℕ}

/-- The omitted residual-escape inference in (!), applied to the original
pre-exclusion component. Only the earlier placement (*) remains an input. -/
theorem PreExclusionSource.parabolic_family_residual_escape
    {d : CaseIComponentData T M Mc V} {h : PreparedChosenModule T M V}
    (s : d.PreExclusionSource h.normalized p)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hTM : (T : Subgroup G) ≤ M)
    (hplacement : ∀ P ∈ d.sourceParabolics, P ≤ M ⊓ d.L ∨ P ≤ d.ML)
    (F : Set (Subgroup G)) (hF : F ⊆ d.sourceParabolics) (hout : ¬ sSup F ≤ d.ML) :
    (∀ P ∈ F, ¬ P ≤ d.ML → P ≤ M) ∧ ¬ d.localThreeResidual ≤ d.ML := by
  classical
  have hPM : ∀ P ∈ F, ¬ P ≤ d.ML → P ≤ M := by
    intro P hPF hPout
    exact ((hplacement P (hF hPF)).resolve_right hPout).trans inf_le_left
  obtain ⟨P,hPF,hPout⟩ : ∃ P ∈ F, ¬ P ≤ d.ML := by
    by_contra! hn
    exact hout (sSup_le hn)
  have hSL : d.SL ≤ d.ML := (s.local_intersections (h := h) hG hu hTM).2.1
  exact ⟨hPM, (hF hPF).localThreeResidual_escape s.local_component hSL
    (hPM P hPF hPout) hPout⟩

/-- Conditional assembly of (!) on the original pre-exclusion component.
The extra inputs are exactly (*) and the two outstanding source lifting
facts; neither input asserts the requested centralizer equality. -/
theorem PreExclusionSource.parabolic_family_centralizer_of_source_inputs
    {d : CaseIComponentData T M Mc V} {h : PreparedChosenModule T M V}
    (s : d.PreExclusionSource h.normalized p)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hTM : (T : Subgroup G) ≤ M)
    (hplacement : ∀ P ∈ d.sourceParabolics, P ≤ M ⊓ d.L ∨ P ≤ d.ML)
    (hcard : Nat.card d.plusOmega = 2)
    (hgeometry : ¬ d.localThreeResidual ≤ d.ML →
      (¬ d.plusOmega ≤ centralizer (d.plus d.localThreeResidual : Set d.ComponentPlus)) ∧
      d.S ⊓ centralizer (d.localThreeResidual : Set G) ≤ normalizer (d.L : Set G))
    (F : Set (Subgroup G)) (hF : F ⊆ d.sourceParabolics) (hout : ¬ sSup F ≤ d.ML) :
    (∀ P ∈ F, ¬ P ≤ d.ML → P ≤ M) ∧
      (¬ d.localThreeResidual ≤ d.ML) ∧
      d.S ⊓ centralizer (d.localThreeResidual : Set G) =
        d.S ⊓ centralizer (d.L : Set G) := by
  obtain ⟨hPM,hR⟩ := s.parabolic_family_residual_escape (h := h)
    hG hu hTM hplacement F hF hout
  obtain ⟨hm,hn⟩ := hgeometry hR
  exact ⟨hPM,hR,d.localThreeResidual_centralizer_of_plus_movement hTM hcard hm hn⟩

end CFSG.Quasithin.Chapter15.Section01.CaseIComponentData
