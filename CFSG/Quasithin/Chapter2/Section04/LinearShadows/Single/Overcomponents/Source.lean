module
public import CFSG.Quasithin.Chapter2.Section04.LinearShadows.Single.Overcomponents.LinearSource
public import CFSG.Quasithin.Chapter2.Section04.LinearShadows.Single.Overcomponents.CentralQuotient
public import CFSG.Quasithin.Chapter2.Section01To03.ComponentRefinement.SurvivingIntersections.NativeSource.Source
public import CFSG.Quasithin.ChapterA.Section02.SourceAssembly.Complete
public import CFSG.Quasithin.Chapter2.Section01To03.LocalStructure.C129Complete
/-!
# The complete original overcomponent contradiction in 2.4.11

The actual Γ₀ setup supplies the full marked component catalogue. Direct
models and odd central covers are removed by the original even central mark;
the binary Mathieu residue is excluded by the rank of the original core.
The remaining PSL₃(4) central cover contradicts the original outside-conjugate
normalizer barrier. Both universal A/B/C and local C.1.29 are instantiated
with their proved known-simple source theorems.

The preceding overgroup construction supplies the actual `MathieuSourceSetup`,
component inclusion, central two-core containment, and original central
involution. This module adds no model-recognition or intersection hypothesis.
Source: Aschbacher–Smith 2.4.11(2–3), printed pp.531–532.
-/
public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter2.LinearShadows.Single
open ChapterC.Section05.ConjugateSource ComponentRefinement
variable {G : Type*} [Group G] [Finite G]
lemma source_overcomponent_catalogue_false
    {M : Subgroup G} (d : MinimalBlockSetup M)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hST : (d.S : Subgroup d.H).map d.H.subtype < (T : Subgroup G))
    (hsingle : d.L0 = d.block) {n : ℕ} (hL : ChapterC.IsL2EvenBlock d.block n)
    (hM : IsMaximalTwoLocal M) (hTM : (T : Subgroup G) ≤ M)
    (hunique : ∀ J : Subgroup G, IsMaximalTwoLocal J → (T : Subgroup G) ≤ J → J = M)
    (hZ : center (d.block.map d.H.subtype) ≠ ⊥)
    (K : Subgroup G) [IsQuasisimple K] (hLK : d.block.map d.H.subtype ≤ K)
    (hcore : (pCore 2 K).map K.subtype ≤
      (center (d.block.map d.H.subtype)).map (d.block.map d.H.subtype).subtype)
    (X : Subgroup G) (P : Sylow 2 X) (z : G)
    (c : MathieuSourceSetup X K M P z)
    (h2 : 2 ∣ Nat.card (center K)) : False := by
  have hn : center K ≠ ⊥ := by
    intro hh
    rw [hh,card_bot] at h2
    norm_num at h2
  have hABC := fun (A : Type _) [Group A] [Finite A] =>
    ChapterA.Section02.theoremsABC_knownSimple (G := A)
  rcases (c.source_refinement_or_binary_mathieu hG hABC localC129Input_knownSimple).2 with hi | hb
  · have hm := psl_four_of_refined_even_center K M ((P : Subgroup X).map X.subtype) z hi hn h2
    obtain ⟨hc,⟨e⟩⟩ := center_and_native_quotient_of_psl_four hm
    exact source_overcomponent_not_psl_three_four d hG T hST hsingle hL hM hTM hunique
      hZ K hLK e (hc.symm ▸ hcore)
  · obtain ⟨hk,⟨e⟩,_⟩ := hb
    exact source_overcomponent_not_binary_m22 d hG T hST hsingle hL hM hTM hunique hZ K hLK hk e
end CFSG.Quasithin.Chapter2.LinearShadows.Single
