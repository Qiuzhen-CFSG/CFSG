module

public import CFSG.Quasithin.ChapterE.Section01.ParameterReduction.ChiefOrbit.NormalizerDiagonal.Preparation
public import CFSG.Quasithin.ChapterE.Section01.ParameterReduction.ChiefOrbit.NormalizerDiagonal.Overgroups
public import CFSG.Quasithin.ChapterB.Section06To07.Structure
public import Theory.GroupTheory.GeneralizedFitting.ComponentOrbitAutomizer
public import Theory.GroupTheory.GeneralizedFitting.SemisimpleCenter

/-!
# The escaping local normalizer in a minimal parabolic

The actual solvable maximal overgroup of T already lies in the E-generation
target. A proper nontrivial stabilizer-invariant seed in a simple component
cannot generate with T. Hence an escaping J₀=N_K(W₀) must equal K.
The local weak closure is then a normal two-subgroup of J₀S and centralizes K.

Solvability of the maximal overgroup is retained explicitly: escape from
the generation target alone does not imply escape from the unique maximal.
The paired rank-one source model calculations discharge this hypothesis.

Source: Aschbacher–Smith, E.1.11, pp.213–214; paired E.2.2, pp.215–216.
-/

public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterE.ChiefOrbit
variable {G : Type*} [Group G] [Finite G]

theorem pairedNormalizer_eq_component_of_escape {n : ℕ} (hn : 0 < n)
    (T : Sylow 2 G) (hP : ChapterB.IsMinimalParabolicOver T ⊤)
    [Group.IsSolvable (ChapterB.minimalParabolicMax T hP)]
    {K : Subgroup G} (hK : IsComponent G K) [IsSimpleGroup K]
    {Ω : Set (Subgroup G)} (hΩ : IsElementaryFamily Ω)
    (hnot : ¬ localNormalizer T K Ω ≤ generationTarget n T Ω) :
    localNormalizer T K Ω = K := by
  by_contra hne
  have hnb : localNormalizer T K Ω ≠ ⊥ := fun he => hnot (he ▸ bot_le)
  have hproper := component_seed_sup_sylow_ne_top T hK
    (show localNormalizer T K Ω ≤ K from inf_le_left) hnb hne
    (stabilizer_le_localNormalizer_normalizer T K hΩ)
  have hM := hP.1.le_maximal
    ⟨(ChapterB.minimalParabolicMax_spec T hP).2,
      (ChapterB.minimalParabolicMax_spec T hP).1.covBy_top⟩
    le_sup_right (lt_top_iff_ne_top.mpr hproper)
  exact hnot (le_sup_left.trans (hM.trans
    (solvable_overgroup_le_generationTarget hn T (ChapterB.minimalParabolicMax T hP)
      (ChapterB.minimalParabolicMax_spec T hP).2 hΩ)))

theorem localWeakClosure_centralizes_of_localNormalizer_eq
    (T : Sylow 2 G) {K : Subgroup G} (hK : IsComponent G K)
    {Ω : Set (Subgroup G)} (hΩ : IsElementaryFamily Ω)
    (he : localNormalizer T K Ω = K) :
    localWeakClosure T K Ω ≤ centralizer (K : Set G) := by
  let H := normalizerGroup T K Ω
  have hKH : K ≤ H := by rw [← he]; exact le_sup_left
  have hWH : localWeakClosure T K Ω ≤ H :=
    (localWeakClosure_le T K Ω).trans le_sup_right
  let W := (localWeakClosure T K Ω).subgroupOf H
  let : W.Normal := localWeakClosure_normal T K hΩ
  let : Group.IsNilpotent W :=
    ((T.isPGroup'.to_le ((localWeakClosure_le T K Ω).trans inf_le_left)).comap_subtype).isNilpotent
  have hc := (hK.subgroupOf hKH).le_centralizer_of_solvable_normal W
  apply le_centralizer_iff.mp
  intro k hk w hw
  exact congrArg Subtype.val
    (mem_centralizer_iff.mp (hc (show (⟨k,hKH hk⟩ : H) ∈ K.subgroupOf H from hk))
      (⟨w,hWH hw⟩ : H) hw)
end CFSG.Quasithin.ChapterE.ChiefOrbit
