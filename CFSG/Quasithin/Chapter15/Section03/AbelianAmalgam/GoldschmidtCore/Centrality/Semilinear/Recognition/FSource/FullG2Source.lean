module

public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.ComponentSieve.LargeGoldschmidt.MarkedFullG2Catalogue
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.Recognition.FSource.GraphCatalogue
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.Recognition.FSource.FullG2Locals
/-!
# The full binary G₂ amalgam gives the graph alternative

The actual full marking supplies the three local extensions. Its derived
amalgam places a wreathed group of order 32 inside the original two-residual.
The component catalogue and the marked first-vertex obstruction then force
the component-quotient Sylow to have order 32, exponent eight, and to be
noncommutative. The graph catalogue constructs the field, component cover,
and graph action from those invariants.

This proves the literal F.6.18(11) alternative from the original source
hypotheses and the full binary G₂ marking; none of the Sylow invariants or
local extensions is an additional premise. The genuine earlier Theorems A
and C remain the inputs owned by the global source assembly.
Source: Aschbacher–Smith F.6.18, printed pp.309–310.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.Recognition.FSource
open CFSG.Quasithin.ChapterF.SourceAssembly
universe u
variable {G H : Type u} [Group G] [Finite G] [Group H] [Finite H]
    {κ : GroupClass.{u}} {G₁ G₂ : Subgroup G}

theorem eleven_of_full_g2_source
    (hA : ChapterA.Section02.TheoremA κ H)
    (hC : ChapterA.Section02.TheoremC κ (generalizedFitting G ⧸ center (generalizedFitting G)))
    (hH : IsSQTK κ H) (eG : G ≃* (H ⧸ pPrimeCore 3 H))
    (hK : IsComponent G (generalizedFitting G))
    (hres : pResidual 2 G = generalizedFitting G)
    (h : ChapterF.IsGoldschmidtTriple G₁ G₂)
    (hM : ChapterF.GreenBook.ExceptionalModels.G2.IsFullAmalgam
      (RankTwoAmalgam.ofSubgroups G₁ (G₁ ⊓ G₂) G₂ inf_le_left inf_le_right))
    (S : Sylow 2 G) (hS : G₁ ⊓ G₂ = (S : Subgroup G)) : Alternative G₁ G₂ S := by
  obtain ⟨hsylow, hleft, hright⟩ := full_g2_marked_extensions S hS hM
  have hCres : ChapterA.Section02.TheoremC κ (pResidual 2 G ⧸ center (pResidual 2 G)) := by
    rw [hres]
    exact hC
  have hq : IsQuasisimple (pResidual 2 G) := by
    rw [hres]
    exact hK.2
  have hd := full_g2_source_component_sylow hA hCres hH eG hres hq h hM
  rw [hres] at hd
  obtain ⟨hproper, P, hP, he, hnc⟩ := hd
  exact eleven_of_source_sylow32_exponent_eight hA hC hH eG hK hres hproper S
    P hP he hnc hsylow hleft hright
end CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.Recognition.FSource
