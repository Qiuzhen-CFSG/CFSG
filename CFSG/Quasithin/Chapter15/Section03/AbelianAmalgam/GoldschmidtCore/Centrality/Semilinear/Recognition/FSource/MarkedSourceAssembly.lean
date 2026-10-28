module

public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.MarkedCases
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.Recognition.FSource.MarkedG2Source
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.Recognition.FSource.MarkedFullG2Source
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.Recognition.FSource.MarkedMathieuSource
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.Recognition.FSource.CharacteristicTwoReduction

/-!
# Full F.6.18 source assembly from the remaining marked enumeration

The complete small, exceptional-vertex and split-sixteen arguments leave only
the source branch with two characteristic-two vertices. The remaining F.6.5
enumeration produces one of four original marked inclusion amalgams. Each of
their complete source proofs constructs the actual ambient group, cover, field,
action and local extensions. This assembles the corrected full source interface
from the genuine A/C and earlier marked-amalgam implications, with no F.6.18
classification output as a premise.

Source: Aschbacher–Smith F.6.5, F.6.13–18, printed pp.305,307–310.
The universal marked enumeration remains an explicit earlier-source input;
the assembly theorem does not assert that input.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.Recognition.FSource
open ChapterF.SourceAssembly
universe u
variable {κ : GroupClass.{u}} {G : Type u} [Group G] [Finite G]
    {G₁ G₂ : Subgroup G}

/-- Every large marked F.6.5 family supplies the complete source alternative. -/
theorem source_of_exceptional_marked_amalgam
    (hA : ∀ (H : Type u) [Group H] [Finite H], ChapterA.Section02.TheoremA κ H)
    (hC : ∀ (H : Type u) [Group H] [Finite H], ChapterA.Section02.TheoremC κ H)
    (q : ThreePrimeSQTKQuotient κ G) (h : ChapterF.IsGoldschmidtTriple G₁ G₂)
    (S : Sylow 2 G) (hS : G₁ ⊓ G₂ = (S : Subgroup G))
    (hM : ExceptionalMarkedAmalgam G₁ G₂) :
    SourceAlternative G₁ G₂ S ∨ SourceAlternative G₂ G₁ S := by
  rcases hM with hd | hf | hm | ha
  · exact source_of_marked_derived_g2 hA hC q h S hS hd
  · exact source_of_marked_full_g2 hA hC q h S hS hf
  · exact source_of_marked_mathieu hA hC q h S hS hm
  · exact source_of_marked_aut_mathieu hA hC q h S hS ha

/-- The full source classifier after the genuine earlier marked enumeration. -/
theorem sourceClassificationInput_of_characteristic_two_marked_amalgams
    (hA : ∀ (H : Type u) [Group H] [Finite H], ChapterA.Section02.TheoremA κ H)
    (hC : ∀ (H : Type u) [Group H] [Finite H], ChapterA.Section02.TheoremC κ H)
    (hF1 : CharacteristicTwoMarkedAmalgamInput.{u}) : SourceClassificationInput κ := by
  intro G _ _ G₁ G₂ h q
  obtain ⟨S,hS,ha⟩ := source_alternative_or_characteristic_two hA hC q h
  refine ⟨S,hS,?_⟩
  rcases ha with ha | ⟨hlarge,_,_,hgood₁,hgood₂,hnosplit⟩
  · exact ha
  let := q.coverGroup
  let := q.coverFinite
  have hcore := ChapterF.Noncyclic.twoCore_eq_bot_of_cover q.equiv.symm
  rcases hF1 G G₁ G₂ S h hcore hgood₁ hgood₂ hS hlarge hnosplit with hm | hm
  · exact source_of_exceptional_marked_amalgam hA hC q h S hS hm
  · exact (source_of_exceptional_marked_amalgam hA hC q h.symm
      S ((inf_comm _ _).trans hS) hm).symm

end CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.Recognition.FSource
