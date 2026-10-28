module
public import CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels.Source.OddFamilies
public import CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels.Source.Bender
public import CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels.Source.LinearThree
public import CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels.Source.SymplecticFour
/-!
# Marked normal-component alternatives from the original source

The actual Theorem C component list, all genuine excluded model families,
and the explicit source Borel and diagram producers give the normal
marked alternatives. Only the literal binary derived symplectic carrier
is left unmarked here. No ambient generation-parameter assertion is made;
the sufficient Cartan source uses separate upper bounds.

Source: Aschbacher–Smith E.2.2, printed pp.215–216.
-/

public section
open Subgroup
namespace CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels
universe u
variable {H:Type u} [Group H] [Finite H] {κ:GroupClass.{u}}
theorem source_normal_marked_cases
    (hA:ChapterA.Section02.TheoremA κ H)
    (hC:∀(G:Type u) [Group G] [Finite G],ChapterA.Section02.TheoremC κ G)
    (hH:IsSQTK κ H) (T:Sylow 2 H) (hP:ChapterB.IsMinimalParabolicOver T ⊤)
    (hs:¬Group.IsSolvable H) (K:Subgroup H) (hK:K.IsCComponent) [K.Normal]
    (hgen:K⊔(T:Subgroup H)=⊤) :
    let M:=ChapterB.minimalParabolicMax T hP
    SingleOddLinearModel M K (T:Subgroup H) ∨
    SingleOddRankThreeModel M K (T:Subgroup H) ∨
    (∃f:ℕ,BenderModel M K f) ∨
    (∃f:ℕ,DiagramModel M K (T:Subgroup H) f) ∨
    Nonempty (sourceImage M K≃*commutator (ClassicalGroup.PSp 2 (ZMod 2))) := by
  rcases source_normal_geometric_cases hA hC hH T hP hs K hK hgen with h2|h3|hb|hl|hsp|hbi
  · exact Or.inl h2
  · exact Or.inr (Or.inl h3)
  · exact Or.inr (Or.inr (Or.inl (source_bender_model T hP hs K hK hgen hb)))
  · obtain ⟨f,hf,hm⟩:=hl
    exact Or.inr (Or.inr (Or.inr (Or.inl ⟨f,source_binary_linear_three_model T hP hs K hK hgen hf hm⟩)))
  · obtain ⟨f,hf,hm⟩:=hsp
    exact Or.inr (Or.inr (Or.inr (Or.inl ⟨f,source_binary_symplectic_model T hP hs K hK hgen hf hm⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr hbi)))
end CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels
