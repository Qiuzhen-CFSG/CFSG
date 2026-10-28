module
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.NonblockEndgameSieveContracts
public import CFSG.Quasithin.ChapterA.Section04.Signalizers.QuotientKernel
public import Theory.GroupTheory.InnerImageGeometry
public import Theory.GroupTheory.SylowPreimageNormalizerImage
public import Theory.GroupTheory.SylowKernelCore
public import GorensteinWalter.PSL2Center

/-!
# The literal quotient-image geometry for original 4.3.16

The direct secondary projection retains its PSL₂ quotient. Centerlessness
of that quotient controls the further inner-action kernel. Independently,
A.4.2 gives a Sylow subgroup of the full root-normalizer action kernel; the
original enlarged-core bound puts it inside R₂. Frattini therefore lifts
the normalizer of R₂-star to the original radical normalizer, which
normalizes K₂. Quasisimplicity makes this local normalizer proper.

The final constructor discharges LocalImageData on the original s.action,
full component quotient, and literal images. The source model alternatives
and row exclusions remain separate obligations of the same sieve owner.
Source: Aschbacher--Smith, original 4.3.14--16, printed pp.617--618.
-/

@[expose] public section
noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock.EndgameSieve
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
variable {c : SourceConfiguration T L} {n : ℕ}

/-- The enlarged-core bound puts an actual kernel Sylow inside the literal R₂. -/
theorem SecondaryData.action_kernel_sylow_le (s : SecondaryData c n)
    (D : Chapter12.Section02.ChosenModule T L V) :
    ∃ P : Sylow 2 s.action.ker,
      (P : Subgroup s.action.ker).map s.action.ker.subtype ≤
        (R₂ c).subgroupOf (rootNormalizer c) := by
  let := s.normal
  let := s.isComponent.perfect
  change ∃ P : Sylow 2 (normalQuotientAction s.component (pCore 2 s.component)).ker,
    (P : Subgroup _).map (normalQuotientAction s.component (pCore 2 s.component)).ker.subtype ≤
      (R₂ c).subgroupOf (rootNormalizer c)
  let T' : Sylow 2 (rootNormalizer c) := T.subtype (root_normalized c D)
  obtain ⟨P,hP⟩ := ChapterA.Section04.sylow_normalQuotientAction_ker s.component T'
  refine ⟨P, ?_⟩
  rw [hP]
  apply (map_le_iff_le_comap).mp
  rw [map_pCoreIn_of_injective 2 _ _ (rootNormalizer c).subtype_injective,
    Subgroup.map_sup, Sylow.coe_subtype, map_subgroupOf_eq_of_le (root_normalized c D)]
  exact s.enlarged_core_le

/-- The original radical-normalizer containment lifts through the literal action. -/
theorem SecondaryData.image_normalizer_control (s : SecondaryData c n)
    (D : Chapter12.Section02.ChosenModule T L V) :
    (SecondaryData.ambientImage s) ⊓ normalizer (SecondaryData.radicalImage s : Set _) ≤
      normalizer (SecondaryData.secondaryImage s : Set _) := by
  obtain ⟨P,hP⟩ := SecondaryData.action_kernel_sylow_le s D
  have hlift := normalizer_image_of_kernel_sylow_le
    ((R₂ c).subgroupOf (rootNormalizer c))
    (isPGroup_pCoreIn 2 (secondary c ⊔ S c)).comap_subtype s.action P hP
  have hamb : SecondaryData.ambientImage s ≤ s.action.range := by
    rw [← SecondaryData.localGroup_image]
    exact map_le_range _ _
  apply ((inf_le_inf_right _ hamb).trans hlift).trans
  apply le_trans (map_mono ?_)
    (((secondary c).subgroupOf (rootNormalizer c)).le_normalizer_map s.action)
  intro x hx
  have hr : ((R₂ c).subgroupOf (rootNormalizer c)).map (rootNormalizer c).subtype = R₂ c :=
    map_subgroupOf_eq_of_le s.radical_le
  have hx' : (x : G) ∈ normalizer (R₂ c : Set G) := by
    rw [← hr]
    exact ((R₂ c).subgroupOf (rootNormalizer c)).le_normalizer_map
      (rootNormalizer c).subtype (mem_map_of_mem _ hx)
  apply mem_normalizer_iff.mpr
  intro y
  exact mem_normalizer_iff.mp (s.radical_normalizer hx').2 (y : G)
end CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock.EndgameSieve

namespace CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock.EndgameSieve
open Subgroup Theory.GroupTheory
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
variable {c : SourceConfiguration T L} {n : ℕ}

/-- The PSL₂ model survives both the core projection and the inner-action kernel. -/
theorem SecondaryData.secondaryImage_model (s : SecondaryData c n) :
    ClassicalGroup.IsPSL
      (SecondaryData.secondaryImage s ⧸ pCore 2 (SecondaryData.secondaryImage s)) 2 (2 ^ n) := by
  have hm := SecondaryData.secondaryProjection_model s
  have hz : center ((SecondaryData.secondaryProjection s).range ⧸
      pCore 2 (SecondaryData.secondaryProjection s).range) = ⊥ := by
    obtain ⟨F,_,_,_,⟨e⟩⟩ := hm
    apply (eq_bot_iff_forall _).mpr
    intro x hx
    have hx' : e x ∈ center (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) := by
      apply mem_center_iff.mpr
      intro y
      obtain ⟨y,rfl⟩ := e.surjective y
      simpa only [map_mul] using congrArg e (mem_center_iff.mp hx y)
    rw [GorensteinWalter.psl2_center_eq_bot,mem_bot] at hx'
    exact e.injective (hx'.trans (map_one e).symm)
  have he : SecondaryData.secondaryImage s =
      (SecondaryData.secondaryProjection s).range.map MulAut.conj :=
    SecondaryData.secondary_action_image s
  rw [he]
  exact hm.of_mulEquiv (innerImageCoreEquiv _ hz).symm

/-- The nontrivial radical action has a proper normalizer in the inner component. -/
theorem SecondaryData.componentImage_not_le_radical_normalizer (s : SecondaryData c n) :
    ¬ SecondaryData.componentImage s ≤ normalizer (SecondaryData.radicalImage s : Set _) := by
  let := s.quasisimple
  rw [SecondaryData.componentImage_eq_inner]
  exact inner_not_le_normalizer_twoGroup _ (SecondaryData.radicalImage_two s).1
    (SecondaryData.radicalImage_two s).2

/-- All three literal image-geometry clauses, with no extra kernel or model premise. -/
theorem SecondaryData.localImageData (s : SecondaryData c n)
    (D : Chapter12.Section02.ChosenModule T L V) : SecondaryData.LocalImageData s :=
  ⟨SecondaryData.secondaryImage_model s, SecondaryData.image_normalizer_control s D,
    SecondaryData.componentImage_not_le_radical_normalizer s⟩
end CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock.EndgameSieve

end
