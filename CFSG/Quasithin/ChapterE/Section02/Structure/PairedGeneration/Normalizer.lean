module

public import CFSG.Quasithin.ChapterE.Section01.ParameterReduction.ChiefOrbit.PairedNormalizer
public import CFSG.Quasithin.ChapterE.Section02.Structure.PairedComponents

/-!
# The original paired E.2.2 local-normalizer consumer

The original core-free minimal parabolic has trivial solvable radical.
Its nonnormal generating component is simple and has normalizer index two
by the genuine strongly-quasithin paired-component theorem. These exact
source facts discharge the lower paired normalizer theorem. Solvability
of the actual maximal overgroup remains the model Borel/dihedral input
owned by the paired numerical assembly; no E-generation premise is added.

Source: Aschbacher–Smith, E.2.2, pp.215–216, using E.1.11, p.214.
-/

public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterE.Structure.PairedGeneration
variable {G : Type*} [Group G] [Finite G]

theorem source_localNormalizer_le {n : ℕ} (hn : 0 < n)
    (hG : IsStronglyQuasithin G) (T : Sylow 2 G)
    (hP : ChapterB.IsMinimalParabolicOver T ⊤)
    [Group.IsSolvable (ChapterB.minimalParabolicMax T hP)]
    (hs : ¬ Group.IsSolvable G) (hJ : ChapterB.minimalParabolicCore T hP = ⊥)
    {K : Subgroup G} (hK : IsComponent G K)
    (hgen : K ⊔ (T : Subgroup G) = ⊤) (hKn : ¬ K.Normal)
    {Ω : Set (Subgroup G)} (hΩ : IsElementaryFamily Ω) :
    ChiefOrbit.localNormalizer T K Ω ≤ ChiefOrbit.generationTarget n T Ω := by
  have hrad : solvableRadical G = ⊥ :=
    (ChapterB.minimalParabolic_nonsolvable_core_eq_radical T hP hs).symm.trans hJ
  let : IsQuasisimple K := hK.2
  let : IsSimpleGroup K := isSimpleGroup_of_isQuasisimple_of_solvableRadical_eq_bot hrad hK.1
  rcases component_normal_or_pair hG T hK hgen with hh | ⟨t,_,_,_,_,_,_,hi⟩
  · exact (hKn hh.1).elim
  · exact ChiefOrbit.localNormalizer_le_of_paired_solvable_max hn T hP hK hgen hrad
      (residual_eq_layer T hK hgen) hi hΩ

end CFSG.Quasithin.ChapterE.Structure.PairedGeneration
