module

public import CFSG.Quasithin.Chapter6.SourceReduction.LocalCentralization.ModuleRecognition
public import CFSG.Quasithin.Chapter6.SourceReduction.LocalCentralization.FFReduction.SourceApplications

/-!
# Cartan relocation at degree two with module recognition discharged

The original FF theorem and the A₇ exclusion give omega-centralization of
the witnessed component. At degree two the new module proof identifies
all of [W,L], with splitting and multiplicity proved. A second application
of the same sieve constructs the C-component relative to the whole omega
centralizer. Thus this specialized route retains only the sieve and A₇
exclusion; it has no module-recognition callback.

The universal source owner qt-d-1222-rankone-cartan-local-classification
retains the proof of degree two, both remaining local implications, and
unconditional assembly. No assertion that the original input already has
degree two is made here.

Source: Aschbacher--Smith 5.1.13(1--5), printed pp.637--638.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric
variable {G : Type*} [Group G] [Finite G]

/-- The original local escape conclusion at degree two, with the full module
argument and the FF input discharged. -/
theorem localCartan_escape_of_sieve_a7_degree_two
    (hsieve : LocalCartanSieve KnownSimple.IsKnownSimple G)
    (ha7 : LocalCartanA7Exclusion G)
    {T : Sylow 2 G} {L W H A B Y : Subgroup G}
    (h : Input KnownSimple.IsKnownSimple T L W 2)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H) (c : CartanPair T L H A B)
    (hY : Y ∈ Chapter1.HOver G (H : Set G))
    (hescape : ¬ A ⊓ Y ≤ normalizer (residual H : Set G)) :
    CartanExceptionalConclusion T L W H := by
  obtain ⟨X,D,d⟩ := hsieve T L W 2 h H hH hgen A B c Y hY hescape
  have hXC := localCartan_centralizes_of_a7 ha7 h hH hgen c hY d
  have hm := d.module_of_exponent_eq_two h hH c hXC rfl
  have hC := omegaCentralizer_mem_HOver_of_residual hH.1.1
    (d.residual_le.trans hXC)
  obtain ⟨X',D',d'⟩ := hsieve T L W 2 h H hH hgen A B c
    (omegaCentralizer T) hC (d.escape_in_omegaCentralizer hXC)
  exact ⟨hm,d.residual_linear,X',d'.residual_le,d'.component_le,d'.component,d'.component_model⟩

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric
