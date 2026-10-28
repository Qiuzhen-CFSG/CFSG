module
public import CFSG.Quasithin.Chapter10.SourceA5NaturalGeneration.Completion
public import CFSG.Quasithin.Chapter10.SourceA5PointControlComplete
public import CFSG.Quasithin.Chapter10.SourceA5HallPlacement.SourceOddNormalizerComplete

/-!
# Normalization of the original A5 component after tensor exclusion

On a minimal fundamental setup, a proper seed has separated support. The
proved numerical bounds and point inspection give w>1. Full Hall-kernel
escape and odd-normalizer control give a faithful odd Hall subgroup in an
actual HStar overgroup; its literal image lies in L₀. The weak-closure
endgame then forces the natural module and n(H)=2, whereas the completed
natural-generation argument gives n(H)≤1.

Thus every nonnormal minimal A5 setup has its genuine tensor model. The
normalization application reselects a minimal setup with the same G,T,L and
retains only the independent tensor exclusion, together with the standing
multiple-overgroup hypothesis. No fixed-setup irreducibility is assumed.
Source: Aschbacher--Smith 10.2.3(4), 10.2.9--13, printed pp.746--747,750--755.
-/

@[expose] public noncomputable section

open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02 ChapterE ChapterE.Section06.FixedPointBounds.ParabolicCartan
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
  (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))

local instance : IsElementaryAbelian 2 (⁅D.fullModule,L⁆ : Subgroup G) :=
  source_original_full_moved_elementary D

include e in
/-- The actual proper seed is impossible: the faithful Hall image gives
incompatible generation bounds on the same HStar overgroup. -/
theorem source_a5_proper_seed_contradiction_of_many
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hD : D.IsMinimalFullModule)
    (hproper : D.seed ≠ D.moduleSubgroup)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard) : False := by
  obtain ⟨t, ht, htn⟩ := Set.not_subset.mp hn
  have hlocal := source_local_module_cubic_bound_of_many D hmany
  have hfull := source_full_module_cubic_bound_of_many D hmany
  have hsep := source_a5_moved_seed_separated D e hn ht htn hproper hlocal
  obtain ⟨_, hi, hcross, _⟩ :=
    source_a5_original_proper_seed_control_of_many D e hn ht htn hD hproper hmany
  obtain ⟨hcent, hw⟩ := source_a5_point_control_of_irreducible D e hi ht htn hcross
  obtain ⟨H, hH⟩ := Chapter3.exists_HStar_of_hasMaximalOutside
    (source_maximalOutside_of_many D hmany)
  have hb := source_a5_hstar_generation_bound D e hn ht htn hD hfull hsep hH
  have hlargeE : (1 : ℕ∞) < (generationParameter H : ℕ∞) :=
    hw.trans_le (source_a5_hstar_globalW_le_generation D e hcent hH hb)
  have hlarge : 1 < generationParameter H := by exact_mod_cast hlargeE
  obtain ⟨B, hBM, hHall, hfaith⟩ := source_a5_hstar_hall_faithful D e hn ht htn
    (source_a5_original_bounded_separated_coordinates D e hn ht htn hD hfull hsep) hH hlarge
  have hodd : Odd (Nat.card (B.map H.subtype)) := by
    rw [card_map_of_injective H.subtype_injective]
    apply Nat.not_even_iff_odd.mp
    intro he
    apply hHall.p_in_pi_of_p_dvd_card ⟨2,Nat.prime_two⟩ _ rfl
    rw [Nat.card_congr (subgroupOfEquivOfLe hBM).toEquiv]
    exact even_iff_two_dvd.mp he
  have hBJ := source_a5_faithful_odd_subgroup_le_orbit D e hn (B.map H.subtype)
    (map_le_iff_le_comap.mpr hBM) hodd hfaith
  exact source_a5_hall_placement_contradiction D e hi hn ht htn hcross hcent
    hH B hBM hHall (hBJ.trans le_sup_left)

/-- Every nonnormal minimal original A5 setup lies in the tensor branch.
The separated natural and deleted alternatives have been contradicted. -/
theorem source_a5_minimal_tensor_of_many
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hD : D.IsMinimalFullModule)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard) :
    Nonempty (SourceA5TensorModel D e) := by
  by_cases hseed : D.seed = D.moduleSubgroup
  · exact source_a5_original_tensor_model_of_seed_eq_local D e hn hD hseed
      (source_full_module_cubic_bound_of_many D hmany)
  · exact (source_a5_proper_seed_contradiction_of_many D e hn hD hseed hmany).elim

/-- The original component is normalized once the tensor branch is excluded
on minimal setups with the same G, T and L. -/
theorem source_a5_normalizes_after_tensor_exclusion_of_many
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hL : L ∈ Chapter1.LStar G (T : Subgroup G))
    (hf : ChapterA.Section04.IsFaithfulSignalizerType L)
    (hq : IsQuasisimple (L ⧸ pCore 2 L))
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hnot : ∀ E : FundamentalSetup KnownSimple.IsKnownSimple T L,
      E.IsMinimalFullModule → ¬ (T : Subgroup G) ≤ normalizer (L : Set G) →
      ¬ Nonempty (SourceA5TensorModel E e)) :
    (T : Subgroup G) ≤ normalizer (L : Set G) := by
  by_contra hn
  obtain ⟨E,hE⟩ := FundamentalSetup.exists_minimal_fullModule_of_source hG hL hf hq
  exact hnot E hE hn (source_a5_minimal_tensor_of_many E e hn hE hmany)

/-- The remaining earlier tensor-exclusion theorem, for the actual original
minimal setups. This proposition is not installed as an assumption or instance. -/
def SourceA5TensorExclusionAt (T : Sylow 2 G) : Prop :=
  ∀ (L : Subgroup G) (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)),
    D.IsMinimalFullModule →
    1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard →
    ¬ (T : Subgroup G) ≤ normalizer (L : Set G) →
    ¬ Nonempty (SourceA5TensorModel D e)

end CFSG.Quasithin.Chapter10
