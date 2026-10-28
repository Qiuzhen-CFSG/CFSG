module

public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.SmallAmalgams.LargeNonabelianReduction
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.Recognition.FSource.MarkedSourceAssembly

/-!
# Removing all abelian-core and order-thirty-two inputs from the F.6 assembly

The original order-thirty-two pair now determines its compatible G₂(2)′
marking. Applying the ambient recognition to that marking gives the full
source alternative on the original Sylow and quotient. For the universal
classifier, the only remaining earlier marked enumeration has two nonabelian
cores and common Sylow order at least 64. The source A/C premises are unchanged.

Source: Aschbacher--Smith F.1.12(I)(8) and F.6.5,13–18.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.Recognition.FSource
open ChapterF.SourceAssembly
universe u
variable {κ : GroupClass.{u}} {G : Type u} [Group G] [Finite G]
    {G₁ G₂ : Subgroup G}

theorem source_of_common_sylow_card_thirty_two
    (hA : ∀ (H : Type u) [Group H] [Finite H], ChapterA.Section02.TheoremA κ H)
    (hC : ∀ (H : Type u) [Group H] [Finite H], ChapterA.Section02.TheoremC κ H)
    (q : ThreePrimeSQTKQuotient κ G) (h : ChapterF.IsGoldschmidtTriple G₁ G₂)
    (hgood₁ : generalizedFitting G₁=pCore 2 G₁)
    (hgood₂ : generalizedFitting G₂=pCore 2 G₂)
    (S : Sylow 2 G) (hS : G₁⊓G₂=(S : Subgroup G)) (hc : Nat.card S=32) :
    SourceAlternative G₁ G₂ S ∨ SourceAlternative G₂ G₁ S := by
  let := q.coverGroup
  let := q.coverFinite
  have hcore := ChapterF.Noncyclic.twoCore_eq_bot_of_cover q.equiv.symm
  rcases exceptional_marked_of_card_thirty_two h hcore hgood₁ hgood₂ S hS hc with hm | hm
  · exact source_of_exceptional_marked_amalgam hA hC q h S hS hm
  · exact (source_of_exceptional_marked_amalgam hA hC q h.symm
      S ((inf_comm _ _).trans hS) hm).symm

/-- Full source classification from just the genuinely remaining large,
nonabelian-core enumeration, with all abelian and order32 branches discharged. -/
theorem sourceClassificationInput_of_large_nonabelian_marked_amalgams
    (hA : ∀ (H : Type u) [Group H] [Finite H], ChapterA.Section02.TheoremA κ H)
    (hC : ∀ (H : Type u) [Group H] [Finite H], ChapterA.Section02.TheoremC κ H)
    (hF1 : LargeNonabelianMarkedAmalgamInput.{u}) : SourceClassificationInput κ :=
  sourceClassificationInput_of_characteristic_two_marked_amalgams hA hC
    (characteristicTwoMarked_of_large_nonabelian hF1)

end CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.Recognition.FSource
