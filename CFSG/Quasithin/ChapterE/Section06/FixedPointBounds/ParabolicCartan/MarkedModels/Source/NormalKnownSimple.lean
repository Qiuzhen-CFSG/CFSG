module
public import CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels.Source.NormalComplete
public import CFSG.Quasithin.ChapterA.Section02.SourceAssembly.Complete
public import CFSG.Quasithin.ChapterE.Section01.ParameterReduction.Solvable
public import CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.Overlap
/-!
# Original known-simple normal-component applications

The completed Theorems A and C discharge the classification inputs of the
normal Cartan source. The original residual parabolic inherits SQTK from
the two-local normalizer of U, and its positive large parameter excludes
solvability. Its constructed Hall data also proves maximal solvability.
E.6.26 therefore places that maximal subgroup in the literal ambient M,
using the original higher-Thompson hypothesis and prescribed Sylow.

The last theorem retains only the genuine earlier E.6.26 and 4.4.13(1)
source implications. Every model, parameter bound, Hall, solvability and
overlap input of this normal-component branch is constructed.
Source: Aschbacher–Smith E.6.26–27, printed pp.256–257.
-/

public section
open Subgroup Theory.GroupTheory CFSG.Quasithin.ChapterB
namespace CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels
universe u
variable {G : Type u} [Group G] [Finite G]
theorem source_normal_intrinsic_cartan_knownSimple
    (hG : IsSQTK KnownSimple.IsKnownSimple G)
    (S : Sylow 2 G) (hP : ChapterB.IsMinimalParabolicOver S ⊤)
    (hn : 1 < generationParameter G)
    (K : Subgroup G) (hK : K.IsCComponent) [K.Normal]
    (hqs : IsQuasisimple (K ⧸ pCore 2 K)) (hgen : K ⊔ (S : Subgroup G) = ⊤) :
    ∃ f : ℕ, IsEGenerated f G ∧ generationParameter G ≤ f ∧
      Nonempty (IntrinsicHallCartanData S hP f) := by
  have hs : ¬Group.IsSolvable G := by
    intro hs
    let := hs
    exact (Nat.not_le_of_gt hn) generationParameter_le_one_of_solvable
  exact source_normal_intrinsic_cartan ChapterA.Section02.theoremA_knownSimple
    (fun _ _ _ => ChapterA.Section02.theoremC_knownSimple) hG S hP hs hn K hK hqs hgen

theorem source_normal_residual_alternative
    {T : Sylow 2 G} {U M V : Subgroup G}
    (h : HypothesisE61 KnownSimple.IsKnownSimple T M V) (hU : U ≠ ⊥) (hUV : U ≤ V)
    (earlier : Source4413One KnownSimple.IsKnownSimple G)
    (S : Sylow 2 (centralizer (U : Set G)))
    (P : Subgroup (primeToResidual 2 (centralizer (U : Set G))))
    (hP : ChapterB.IsMinimalParabolicOver (residualSylow S) P)
    (hn : 1 < generationParameter P)
    (K : Subgroup P) (hK : K.IsCComponent) [K.Normal]
    (hqs : IsQuasisimple (K ⧸ pCore 2 K))
    (hgen : K ⊔ (parabolicSylow S P hP : Subgroup P) = ⊤)
    (R : Sylow 2 ↥(M ⊓ centralizer (U : Set G)))
    (hR : (R : Subgroup ↥(M ⊓ centralizer (U : Set G))).map
      (M ⊓ centralizer (U : Set G)).subtype =
      (S : Subgroup (centralizer (U : Set G))).map (centralizer (U : Set G)).subtype)
    (hescape : ¬ (P.map (primeToResidual 2 (centralizer (U : Set G))).subtype).map
      (centralizer (U : Set G)).subtype ≤ M)
    (hmax : (ChapterB.minimalParabolicMax (parabolicSylow S P hP)
      (minimalParabolic_subtype (residualSylow S) P hP)).map (residualEmbedding U P) ≤ M) :
    ∃ f : ℕ, IsEGenerated f P ∧ generationParameter P ≤ f ∧
      ParabolicCartanAlternative V M U
        ((P.map (primeToResidual 2 (centralizer (U : Set G))).subtype).map
          (centralizer (U : Set G)).subtype) f := by
  have hs : ¬Group.IsSolvable P := by
    intro hs
    let := hs
    exact (Nat.not_le_of_gt hn) generationParameter_le_one_of_solvable
  have hM : ChapterB.minimalParabolicMax (parabolicSylow S P hP)
      (minimalParabolic_subtype (residualSylow S) P hP) = M.comap (residualEmbedding U P) := by
    apply maximal_eq_overlap_of_image_le _ _ _ _ _ hmax
    · rw [parabolicSylow_image, ← hR]
      exact (map_subtype_le _).trans inf_le_left
    · rwa [residualEmbedding_range]
  exact residual_normal_alternative h hU hUV earlier S P hP
    ChapterA.Section02.theoremA_knownSimple
    (fun _ _ _ => ChapterA.Section02.theoremC_knownSimple)
    (residual_sqtk h hU hUV P) hs hn K hK hqs hgen hM R hR hescape
/-- The actual higher-Thompson hypotheses place the maximal overgroup.
Only the genuine earlier source implications E.6.26 and 4.4.13 remain. -/
theorem source_normal_residual_alternative_of_thompson
    {T : Sylow 2 G} {U M V : Subgroup G}
    (h : HypothesisE61 KnownSimple.IsKnownSimple T M V) (hU : U ≠ ⊥) (hUV : U ≤ V)
    (earlier : Source4413One KnownSimple.IsKnownSimple G)
    (h626 : SylowThompson.E626Input G)
    {j : ℕ} (hj1 : 1 ≤ j) (hj : (j : ℕ∞) < globalR V)
    (hJ : thompsonJ (M ⊓ centralizer (U : Set G)) j ≤ M ⊓ centralizer (V : Set G))
    (R : Sylow 2 ↥(M ⊓ centralizer (U : Set G)))
    (S : Sylow 2 (centralizer (U : Set G)))
    (hS : (S : Subgroup (centralizer (U : Set G))).map (centralizer (U : Set G)).subtype =
      (R : Subgroup ↥(M ⊓ centralizer (U : Set G))).map (M ⊓ centralizer (U : Set G)).subtype)
    (P : Subgroup (primeToResidual 2 (centralizer (U : Set G))))
    (hP : ChapterB.IsMinimalParabolicOver (residualSylow S) P)
    (hn : j < generationParameter P)
    (K : Subgroup P) (hK : K.IsCComponent) [K.Normal]
    (hqs : IsQuasisimple (K ⧸ pCore 2 K))
    (hgen : K ⊔ (parabolicSylow S P hP : Subgroup P) = ⊤)
    (hescape : ¬ (P.map (primeToResidual 2 (centralizer (U : Set G))).subtype).map
      (centralizer (U : Set G)).subtype ≤ M) :
    ∃ f : ℕ, IsEGenerated f P ∧ generationParameter P ≤ f ∧
      ParabolicCartanAlternative V M U
        ((P.map (primeToResidual 2 (centralizer (U : Set G))).subtype).map
          (centralizer (U : Set G)).subtype) f := by
  have hn1 : 1 < generationParameter P := lt_of_le_of_lt hj1 hn
  obtain ⟨f,hg,hb,⟨d⟩⟩ := source_normal_intrinsic_cartan_knownSimple
    (residual_sqtk h hU hUV P) (parabolicSylow S P hP)
    (minimalParabolic_subtype (residualSylow S) P hP) hn1 K hK hqs hgen
  have h113 : Overlap.SourceE113.{u} := by
    intro X _ _ hs
    let := hs
    exact generationParameter_le_one_of_solvable
  have hM := Overlap.residual_maximal_eq_overlap h h626 h113 hU hUV hj1 hj hJ R S hS
    P hP d.maximal_solvable hescape
  let d' := transportResidual S P hP f d M hM R hS.symm
  exact ⟨f,hg,hb,residual_alternative_of_hall_data_at h hU hUV earlier P
    (parabolicSylow S P hP) (minimalParabolic_subtype (residualSylow S) P hP)
    (residual_twoCore_ne_bot h hU hUV S P hP) hn1 hM hescape d'⟩

end CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels
