module
public import CFSG.Quasithin.ChapterE.Section02.Structure.NumericalBounds.Paired.PrimeBound
public import CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels.Inverted.Paired
import all CFSG.Quasithin.ChapterB.Section06To07.Structure
/-!
# The complete reflected source alternative above degree two

The only remaining row in the intrinsic Cartan dispatcher is paired odd
PSL₂. Its actual generation bound is two, which contradicts the original
parameter hypothesis here. All source families therefore construct the same
marked Hall subgroup and reflected cyclic subgroup, with the precise model
exponent and normalizer escape. This is the adequate 13.3.16 source consumer;
it does not require the separate sharp paired degree-one theorem.
Source: Aschbacher–Smith E.2.2 and 13.3.16, pp.215–216,841.
-/
public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels.Inverted
open ChapterB
universe u
variable {H : Type u} [Group H] [Finite H]
theorem source_intrinsic_escape_of_parameter_gt_two
    (hH:IsSQTK KnownSimple.IsKnownSimple H) (T:Sylow 2 H) (hP:IsMinimalParabolicOver T ⊤)
    (hn : 2 < generationParameter H) :
    ∃ f:ℕ, IsEGenerated f H ∧ generationParameter H≤f ∧
      ∃ d : IntrinsicHallCartanData T hP f,
        ∀ (p : ℕ) (_ : Fact p.Prime) (A : Subgroup H), Odd p → A ≤ d.witness.cyclicGroup →
          IsPGroup p A → ¬ normalizer (A : Set H) ≤ minimalParabolicMax T hP := by
  rcases source_intrinsic_escape_or_paired_odd hH T hP (by omega) with ho|hg
  · obtain ⟨K,hK,hqs,hgen,hN,p,hp,hop,hp7,hm⟩ := ho
    let : Fact p.Prime := ⟨hp⟩
    have hs : ¬Group.IsSolvable H := by
      intro hs
      let := hs
      have hh := generationParameter_le_one_of_solvable (G := H)
      omega
    exact (Nat.not_le_of_gt hn (Structure.NumericalBounds.paired_prime_parameter_le_two
      ChapterA.Section02.theoremA_knownSimple hH T hP hs K hK hgen hN (p := p) (by omega) hm)).elim
  · exact hg
end CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels.Inverted
