module

public import Stellmacher.Recognition.Parrott.NormalizerGeneratorBranch
public import Stellmacher.Recognition.Parrott.NormalizerGeneratorEquations
public import Stellmacher.Recognition.Parrott.NormalizerGenerators
public import Stellmacher.Recognition.Parrott.NormalizerSquareRootSelection

/-!
# Compatible centralizer and normalizer generators

A reduced normalizer seed has one of two x-images. The central coordinate
change x ↦ xz, s ↦ svt preserves every centralizer equation and every reduced
seed equation, and interchanges these images. Choosing the appropriate frame
therefore gives equations (25)–(26) together with the actual normalizer
membership, generation, order and fusion supplied by the existing assembly.

The elementary subgroup F, Sylow subgroup T and fusion coordinates t,v remain
literal parameters. All u,w,a,b,c,d,y,r are retained; only x and s may change.
This supplies an existential compatible frame, which is what the local
presentation construction needs.

Source: D. Parrott, *A characterization of the Tits' simple group* (1972),
§3, printed pp.678–682. This coordinate normalization replaces the disputed
uniform exclusion immediately before (25). The branch-switching calculation is provided by NormalizerGeneratorBranch.
-/
open Subgroup Tits
namespace Stellmacher.Recognition
variable {G : Type*} [Group G] {z : G}
variable {e : ParrottSecondElementaryData z} {n : ParrottNormalizerFusionData e}

/-- Construct compatible centralizer and normalizer frames on the supplied
actual elementary and Sylow subgroups. Only the auxiliary x may be changed. -/
public theorem ParrottCentralizerGeneratorData.exists_normalized_normalizer_generators
    [Finite G] [IsSimpleGroup G] (f : ParrottCentralizerGeneratorData n)
    (hns : ¬ Group.IsSolvable G) (hN : IsNTwoGroup G)
    (h : ParrottCentralizerHypotheses z) :
    ∃ f' : ParrottCentralizerGeneratorData n,
      (f'.u, f'.w, f'.a, f'.b, f'.c, f'.d, f'.y, f'.r) =
        (f.u, f.w, f.a, f.b, f.c, f.d, f.y, f.r) ∧
      (f'.x = f.x ∨ f'.x = f.x*z) ∧
      Nonempty (ParrottNormalizerGeneratorData f') := by
  obtain ⟨k⟩ := f.exists_normalizerSeed hns hN h
  obtain ⟨f', k', hcoords, hchoice, hxs⟩ := k.exists_normalized_frame
  obtain ⟨hws, has, hbs, hcs, hxs, hcube⟩ := k'.equations_of_x_conj hxs
  refine ⟨f', hcoords, hchoice, ?_⟩
  exact ⟨f'.normalizerGeneratorDataOfEquations h k'.s k'.mem_normalizer k'.sq
    k'.t_conj k'.v_conj k'.y_conj hws has hbs hcs hxs hcube⟩

/-- The existential compatible generator packet needed by the actual local
presentation, retaining the original F,T,t,v through the parameter n. -/
public theorem ParrottCentralizerGeneratorData.nonempty_compatible_generator_data
    [Finite G] [IsSimpleGroup G] (f : ParrottCentralizerGeneratorData n)
    (hns : ¬ Group.IsSolvable G) (hN : IsNTwoGroup G)
    (h : ParrottCentralizerHypotheses z) :
    Nonempty (Σ f' : ParrottCentralizerGeneratorData n, ParrottNormalizerGeneratorData f') := by
  obtain ⟨f', _, _, ⟨k⟩⟩ := f.exists_normalized_normalizer_generators hns hN h
  exact ⟨⟨f', k⟩⟩

end Stellmacher.Recognition
