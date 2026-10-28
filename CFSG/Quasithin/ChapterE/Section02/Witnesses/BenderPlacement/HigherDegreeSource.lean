module
public import CFSG.Quasithin.ChapterE.Section02.Witnesses.BenderPlacement.HigherDegreeModels
public import CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels.Source.OddFamilies
public import CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels.Source.PairedMarked
import all CFSG.Quasithin.ChapterB.Section06To07.Structure

/-!
# Strict-degree witnesses from the full original source catalogue

The actual E.2.2 catalogue supplies normal or exchanged marked component
models. Their checked image analysis turns every noncyclic star image into
a genuine original pair of degree greater than one, assuming only cubic
and quintic rank at most one. No generation-parameter quotient rule is used.

Source: Aschbacher--Smith E.2.2 and E.2.7--9, printed pp.215--222;
application to 8.2.9, printed p.720, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Matrix BenderSuzuki.MatrixGroups
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterE.Witnesses.BenderPlacement
universe u
variable {H : Type u} [Group H] [Finite H] {κ : GroupClass.{u}}

open ChapterB Section06.FixedPointBounds.ParabolicCartan.MarkedModels

theorem source_large_image_degree
    (hA : ChapterA.Section02.TheoremA κ H)
    (hC : ∀ (X : Type u) [Group X] [Finite X], ChapterA.Section02.TheoremC κ X)
    (hH : IsSQTK κ H)
    (T : Sylow 2 H) (hP : IsMinimalParabolicOver T ⊤) (hs : ¬Group.IsSolvable H)
    (V : Subgroup H) [IsElementaryAbelian 2 V] (hVT : V ≤ T)
    (hvn : (V.subgroupOf (T : Subgroup H)).Normal)
    (hVM : V ≤ (minimalParabolicMax T hP).pCoreIn 2)
    (hMV : minimalParabolicMax T hP ≤ normalizer (V : Set H))
    (hcard : 4 ≤ Nat.card (V.map (QuotientGroup.mk' (minimalParabolicCore T hP))))
    (h3 : primeRank 3 H ≤ 1) (h5 : primeRank 5 H ≤ 1) :
    ∃ (n : ℕ) (w : OriginalWitness T (minimalParabolicMax T hP) V n), 1 < w.degree := by
  obtain ⟨K,hK,_,hgen,_⟩ := Structure.source_original_component hH T hP hs
  apply source_large_image_degree_of_models hA hH T hP hs V hVT hvn hVM hMV hcard h3 h5 K hK hgen
  by_cases hn : K.Normal
  · let := hn
    exact Or.inl ⟨hn,source_normal_geometric_cases hA hC hH T hP hs K hK hgen⟩
  · exact Or.inr ⟨hn,source_exchanged_marked_cases hA hC hH T hP hs K hK hgen hn⟩

end CFSG.Quasithin.ChapterE.Witnesses.BenderPlacement
