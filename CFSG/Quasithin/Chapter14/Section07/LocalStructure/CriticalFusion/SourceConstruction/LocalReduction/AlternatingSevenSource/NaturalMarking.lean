module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.AlternatingSevenSource.NaturalBranches
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.AlternatingSevenSource.SeedGeometry
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.AlternatingSevenSource.NaturalMarking.Words
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.AlternatingSevenSource.NaturalMarking.AlternatingSpan
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.AlternatingSevenSource.NaturalMarking.Sylow

/-!
# Original flag words in the natural six-dimensional quotient

The original seed maps injectively to a binary plane, and its point
residual permutes its three nonzero words transitively. Thus they have one
weight, excluding weight six. Sylow fixation leaves exactly the standard
pair and four-set words. Their respective cubic orbit and centralizer
contradictions exclude both A₇ and S₇ natural quotients.
Source: Aschbacher–Smith 14.7.2 and 14.7.50, printed pp.1043 and 1065,
refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.AlternatingSevenSource
open Chapter12.Section08 CriticalFusion.Source
open Chapter14.Section04.LargerDimension.LocalAction.Components
open BinaryPermutation SevenSourceCubics SevenParabolic
open Theory.SpecificGroups.SymmetricSeven.LocalResidualRecognition
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3}

private theorem line_eq_zero_or_eq
    (W : Submodule (ZMod 2) (core (Fin 7))) (hd : Module.finrank (ZMod 2) W = 1)
    {v : core (Fin 7)} (hv : v ∈ W) (hv0 : v ≠ 0)
    {w : core (Fin 7)} (hw : w ∈ W) : w = 0 ∨ w = v := by
  obtain ⟨c,hc⟩ := exists_smul_eq_of_finrank_eq_one hd
    (x := (⟨v,hv⟩ : W)) (by intro he; exact hv0 (congrArg Subtype.val he)) (⟨w,hw⟩ : W)
  have he := congrArg Subtype.val hc
  change c • v = w at he
  fin_cases c
  · change (0 : ZMod 2) • v = w at he
    rw [zero_smul] at he
    exact Or.inl he.symm
  · change (1 : ZMod 2) • v = w at he
    rw [one_smul] at he
    exact Or.inr he.symm

/-- The original local has no proper natural quotient with the marked symmetric Sylow. -/
theorem local_symmetric_natural_impossible_at
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (hm : ⁅F.Vi 2,F.H.pCoreIn 2⁆ ≠ ⊥)
    (I : Subgroup G) (hI : I ∈ F.Hz L (normalizer (L : Set G)))
    (π : I →* Equiv.Perm (Fin 7)) (hπ : Function.Surjective π) (hk : IsPGroup 2 π.ker)
    (hT : ((T : Subgroup G).subgroupOf I).map π = standardTwo)
    {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
    {ρ : Representation (ZMod 2) I W}
    (c : BinaryConjugationSection I (F.UH I) (F.Vi 1) ρ)
    (p : ρ.IntertwiningMap ((coreRepresentation (Fin 7)).comp π))
    (hp : p.toLinearMap.ker ≠ ⊤) : False := by
  let E := (c.imageSpace V).map p.toLinearMap
  let D := (c.imageSpace (F.Vi 2)).map p.toLinearMap
  have hd : Module.finrank (ZMod 2) D = 1 := local_quotient_plane_finrank h hI c p hp
  have hD : D ≠ ⊥ := by
    intro he
    rw [he,finrank_bot] at hd
    omega
  obtain ⟨v,hv,hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hD
  have hDE : D ≤ E := Submodule.map_mono (c.imageSpace_mono (F.le_seed 2))
  have hvE : v ∈ E := hDE hv
  have hweights : ∀ w ∈ E, w ≠ 0 → weight w = weight v := by
    intro w hw hw0
    obtain ⟨a,ha⟩ := local_quotient_seed_transitive h hI c p v hvE hv0 w hw hw0
    rw [←ha]
    exact weight_permute (π (inclusion (F.Li_one_le_of_mem_Hz hI) a)) v
  have hfix : ∀ a ∈ standardTwo, coreRepresentation (Fin 7) a v = v := by
    intro a ha
    obtain ⟨t,ht,rfl⟩ := (hT.symm ▸ ha)
    exact local_quotient_plane_sylow_fixed c p t ht v hv
  rcases NaturalMarking.symmetric_fixed_word_pair_or_four_of_plane
    E (local_quotient_seed_finrank h hI c p hp) v hvE hv0 hweights hfix with hpair | hfour
  · obtain ⟨w,hw,hwv⟩ := hv
    obtain ⟨z,hz,hzw⟩ := (c.mem_imageSpace_iff (F.Vi 2) w).mp hw
    have hzpair : p (c.coordinates z).toAdd = SevenSourceSpan.point := by
      exact (congrArg p hzw).trans (hwv.trans hpair)
    exact local_symmetric_weight_two_impossible_at h hab structural previous faithful
      I hI π hπ hk hT c p hp z hz hzpair
  · have hword : ∀ z : F.UH I, (z : G) ∈ F.Vi 2 →
        p (c.coordinates z).toAdd = 0 ∨ p (c.coordinates z).toAdd = SevenSourceCubics.point := by
      intro z hz
      have hzD : p (c.coordinates z).toAdd ∈ D :=
        ⟨_,(c.mem_imageSpace_iff (F.Vi 2) _).mpr ⟨z,hz,rfl⟩,rfl⟩
      simpa only [hfour] using line_eq_zero_or_eq D hd hv hv0 hzD
    have hlo := local_symmetric_weight_four_centralizer_rank_at h hab structural previous faithful
      I hI π hπ hk hT c p hp hword
    have hup := plane_centralizer_three_rank_le_one_at h structural hm
    omega

/-- The original local has no proper natural quotient with the marked alternating Sylow. -/
theorem local_alternating_natural_impossible_at
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (hm : ⁅F.Vi 2,F.H.pCoreIn 2⁆ ≠ ⊥)
    (I : Subgroup G) (hI : I ∈ F.Hz L (normalizer (L : Set G)))
    (π : I →* alternatingGroup (Fin 7)) (hπ : Function.Surjective π) (hk : IsPGroup 2 π.ker)
    (hT : ((T : Subgroup G).subgroupOf I).map π = Alternating.two)
    {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
    {ρ : Representation (ZMod 2) I W}
    (c : BinaryConjugationSection I (F.UH I) (F.Vi 1) ρ)
    (p : ρ.IntertwiningMap ((alternatingCoreRepresentation (Fin 7)).comp π))
    (hp : p.toLinearMap.ker ≠ ⊤) : False := by
  let E := (c.imageSpace V).map p.toLinearMap
  let D := (c.imageSpace (F.Vi 2)).map p.toLinearMap
  have hd : Module.finrank (ZMod 2) D = 1 := local_quotient_plane_finrank h hI c p hp
  have hD : D ≠ ⊥ := by
    intro he
    rw [he,finrank_bot] at hd
    omega
  obtain ⟨v,hv,hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hD
  have hDE : D ≤ E := Submodule.map_mono (c.imageSpace_mono (F.le_seed 2))
  have hvE : v ∈ E := hDE hv
  have hweights : ∀ w ∈ E, w ≠ 0 → weight w = weight v := by
    intro w hw hw0
    obtain ⟨a,ha⟩ := local_quotient_seed_transitive h hI c p v hvE hv0 w hw hw0
    rw [←ha]
    exact weight_permute (π (inclusion (F.Li_one_le_of_mem_Hz hI) a)).val v
  have hfix : ∀ a ∈ Alternating.two, alternatingCoreRepresentation (Fin 7) a v = v := by
    intro a ha
    obtain ⟨t,ht,rfl⟩ := (hT.symm ▸ ha)
    exact local_quotient_plane_sylow_fixed c p t ht v hv
  rcases NaturalMarking.fixed_word_pair_or_four_of_plane
    E (local_quotient_seed_finrank h hI c p hp) v hvE hv0 hweights hfix with hpair | hfour
  · obtain ⟨w,hw,hwv⟩ := hv
    obtain ⟨z,hz,hzw⟩ := (c.mem_imageSpace_iff (F.Vi 2) w).mp hw
    have hzpair : p (c.coordinates z).toAdd = SevenSourceSpan.point := by
      exact (congrArg p hzw).trans (hwv.trans hpair)
    exact local_alternating_weight_two_impossible_at h hab structural previous faithful
      I hI π hπ hk hT c p hp z hz hzpair
  · have hword : ∀ z : F.UH I, (z : G) ∈ F.Vi 2 →
        p (c.coordinates z).toAdd = 0 ∨ p (c.coordinates z).toAdd = SevenSourceCubics.point := by
      intro z hz
      have hzD : p (c.coordinates z).toAdd ∈ D :=
        ⟨_,(c.mem_imageSpace_iff (F.Vi 2) _).mpr ⟨z,hz,rfl⟩,rfl⟩
      simpa only [hfour] using line_eq_zero_or_eq D hd hv hv0 hzD
    have hlo := local_alternating_weight_four_centralizer_rank_at h hab structural previous faithful
      I hI π hπ hk hT c p hp hword
    have hup := plane_centralizer_three_rank_le_one_at h structural hm
    omega

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.AlternatingSevenSource
