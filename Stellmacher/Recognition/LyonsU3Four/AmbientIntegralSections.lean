module

public import Stellmacher.Recognition.LyonsU3Four.LocalCentralizerBlocks
public import Stellmacher.Recognition.LyonsU3Four.GeneralizedDecompositionData
public import Stellmacher.Recognition.LyonsU3Four.AmbientSectionPreliminaries
public import Stellmacher.Recognition.LyonsU3Four.AmbientSectionExpansion
public import Stellmacher.Recognition.LyonsU3Four.AmbientSectionGram
public import Stellmacher.Recognition.LyonsU3Four.AmbientSectionMass

/-!
# Assembly interface for the integral ambient Lyons sections

The shared preliminaries supply actual complex expansions, integral involution
expansion machinery, principal-row normalization, the order-four norm and mass,
and the strict section-mass budget. The ordered integral expansion, full Gram
identities and involution mass formula are independent remaining construction
steps. This module re-exports the checked inputs for their final assembly;
it does not assert the existence of the completed ambient columns yet.

Source: Lyons, *A Characterization of the Group U₃(4)* (1972), pp. 373--374,
equations (3.1)--(3.3).
-/

public section
noncomputable section

namespace Stellmacher.Recognition.LyonsU3Four

open Subgroup ModularBlock PrincipalBlockConstruction
open GeneralizedDecompositionData

variable {G : Type*} [Group G] [Finite G]

/-- The complete integral section data attached to an actual order-four element.

The construction supplies the genuine order-five centralizer character and the
ordered integral columns in the basis `[0, 1, 2, 4, 3]`.  The two independent
section calculations then give the full Gram identities and the strict
contribution bound.  Congruence and Galois statements are intentionally left to
their dedicated sibling modules.
-/
theorem exists_ambient_integral_sections
    (S : Sylow 2 G) (h : SylowStructure S) (d : LocalCentralizerData S)
    (b : PrincipalCongruenceBlockData G) (t : S) (ht : orderOf t = 4) :
    ∃ M : FiveSectionModel S ((t : G)^2), ∃ _a : M.BrauerData b,
      ∃ c : GeneralizedDecompositionData {j // j ∈ b.block},
        orderOf M.mu = 5 ∧
        c.Equation3_1
            (fun j g => b.chi j.1 (ConjClasses.mk g))
            (t : G) ((t : G)^2) M.mu ∧
        c.Equation3_2 ∧ c.ContributionBound ∧
        c.dT ⟨b.principal, b.principal_mem⟩ = 1 ∧
        (∀ i, c.iDz i ⟨b.principal, b.principal_mem⟩ =
          if i = 0 then 1 else 0) := by
  obtain ⟨M, a, c, he⟩ := exists_ordered_ambient_section_expansion S h d b t ht
  have hgram := ambient_section_equation3_2 S h d b t ht M a c he
  have hmass : ∀ j : {i // i ∈ b.block},
      Theory.Character.twoSectionMass
          (fun g => b.chi j.1 (ConjClasses.mk g)) (t : G) +
        Theory.Character.twoSectionMass
          (fun g => b.chi j.1 (ConjClasses.mk g)) ((t : G)^2) =
          (c.contribution j : ℝ) / 64 := by
    intro j
    exact ambient_combined_mass S h d b t ht M c he j
  have htG : orderOf (t : G) = 4 := (Subgroup.orderOf_coe t).trans ht
  have hbound := ambient_contributionBound_of_mass_identity
    b (t : G) htG c hmass
  have hdt := ambient_section_principal_dT
    b (t : G) ((t : G)^2) M.mu c he
  have hidz := ambient_section_principal_iDz
    b (t : G) ((t : G)^2) M a c he
  exact ⟨M, a, c, M.order_mu, he, hgram, hbound, hdt, hidz⟩

end Stellmacher.Recognition.LyonsU3Four
