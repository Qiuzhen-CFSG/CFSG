module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobalLocalCartan
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalLocalCharacteristic

/-!
# Remaining independent source inputs for the normalized rank-one pair

The shared Cartan construction and the left Sylow intersection are proved.
Characteristic two for both literal parabolics follows from the cores of
N_G(L) and N_G(O²(H)), so it needs no further model assumption.

The final local preparation now has two independent inputs: original
4.3.2 (uniqueness over L), and construction of the right factor in
5.1.10--11 and 5.2.1--4. This is conditional assembly, not an assertion
that either source theorem has been discharged. The local-preparation
owner retains their final discharge before the global-recognition step.

Source: Aschbacher--Smith, printed pp.613--618,634--635,646,649--650.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H : Subgroup G} (D : ChosenModule T L V)
include D

/-- Literal normalized local preparation, retaining precisely its two
unfinished earlier-source producers. No global recognition is assumed. -/
theorem rankOne_global_preparation_of_rightFactor
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H)
    (hN : localBorel T L ≤ normalizer (residual H : Set G))
    (hunique : ∀ X : Subgroup G, IsMaximalTwoLocal X → L ≤ X →
      X = normalizer (L : Set G))
    (hright : ∀ A B : Subgroup G, CartanPair T L H A B →
      ∃ L₂ : Subgroup G, Global.RightFactor T L H A B L₂) :
    ∃ A B L₂ : Subgroup G, Global.Preparation T L H A B L₂ := by
  have hi := D.rankOne_generic_input_of_many h hmany hn hpsl
  obtain ⟨A, B, c⟩ := D.rankOne_exists_cartanPair h hn hpsl hH hgen
  obtain ⟨L₂, r⟩ := hright A B c
  obtain ⟨hleft, hSylow⟩ := D.rankOne_sourceS_intersection_left h hpsl hH
  refine ⟨A, B, L₂, c, r.le_residual, r.outside, hunique, hleft, ?_, r.quotient,
    r.S_normalizes, r.cartan_normalizes, r.borel, r.characteristic_two hi hH c hleft hN⟩
  intro i
  fin_cases i
  · exact hSylow
  · exact r.sylow

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
