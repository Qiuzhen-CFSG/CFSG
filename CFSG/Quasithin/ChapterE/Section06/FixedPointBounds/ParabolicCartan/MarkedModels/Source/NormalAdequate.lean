module
public import CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels.Source.OddFamilies
public import CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels.Source.ClassicalCartan
public import CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels.Source.SuzukiCartan
public import CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels.Source.SymplecticCartan
public import CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels.Source.NumericalOddThree
public import CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels.Source.NumericalBinarySix
/-!
# The sufficient normal-component Cartan reduction

The actual complete component catalogue supplies its source geometric
family. Original generation bounds discard both odd degree-three rows
and the binary derived symplectic row when n(H)>1. Every characteristic-two
family constructs E-generation, n(H) bounded by the same field exponent,
and the complete original Hall–Cartan witness. The remaining alternative
is precisely the marked odd linear-two source row, whose separate
numerical producer must eliminate it in the final assembly.

No equality across the maximal core is used. Source: Aschbacher–Smith
E.2.2 and E.6.27, printed pp.215–216,257.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels
universe u
variable {H:Type u} [Group H] [Finite H] {κ:GroupClass.{u}}
theorem normal_cyclic_cartan_or_odd_two
    (hA:ChapterA.Section02.TheoremA κ H)
    (hC:∀(G:Type u) [Group G] [Finite G],ChapterA.Section02.TheoremC κ G)
    (hH:IsSQTK κ H) (T:Sylow 2 H) (hP:ChapterB.IsMinimalParabolicOver T ⊤)
    (hs:¬Group.IsSolvable H) (hn:1<generationParameter H)
    (K:Subgroup H) (hK:K.IsCComponent) [K.Normal]
    (hqs:IsQuasisimple (K⧸pCore 2 K)) (hgen:K⊔(T:Subgroup H)=⊤) :
    SingleOddLinearModel (ChapterB.minimalParabolicMax T hP) K (T:Subgroup H) ∨
    ∃f:ℕ,IsEGenerated f H ∧ generationParameter H≤f ∧ Nonempty (IntrinsicHallCartanData T hP f) := by
  rcases source_normal_geometric_cases hA hC hH T hP hs K hK hgen with h2|h3|hb|hl|hsp|hbi
  · exact Or.inl h2
  · obtain ⟨p,hp,ho,_,huni|hlin⟩:=h3
    · exact (normal_odd_three_false_of_parameter_gt_one hA hH T hP hs K hK hgen hp ho
        (Or.inr huni.2) hn).elim
    · obtain ⟨_,F,hF,hfin,hcard,e,_⟩:=hlin
      exact (normal_odd_three_false_of_parameter_gt_one hA hH T hP hs K hK hgen hp ho
        (Or.inl ⟨F,hF,hfin,hcard,⟨e⟩⟩) hn).elim
  · apply Or.inr
    cases hb with
    | linear f hf hm => exact ⟨f,normal_classical_intrinsic hA hH T hP hs hn K hK hqs hgen (.inl ⟨hf,hm⟩)⟩
    | unitary f hf hm => exact ⟨f,normal_classical_intrinsic hA hH T hP hs hn K hK hqs hgen (.inr (.inl ⟨hf,hm⟩))⟩
    | suzuki m hm he => exact ⟨2*m+1,normal_suzuki_intrinsic T hP hs K hK hqs hgen hm he⟩
  · obtain ⟨f,hf,hm⟩:=hl
    exact Or.inr ⟨f,normal_classical_intrinsic hA hH T hP hs hn K hK hqs hgen (.inr (.inr ⟨hf,hm⟩))⟩
  · obtain ⟨f,hf,hm⟩:=hsp
    exact Or.inr ⟨f,normal_symplectic_intrinsic hA hH T hP hs K hK hqs hgen hf hm⟩
  · exact ((Nat.not_le_of_gt hn) (normal_binary_six_parameter_le T hP hs K hK hgen hbi)).elim
end CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels
