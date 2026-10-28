module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.PointBlocks.Conditions
public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.FusionReducibleNormalizerSetup

/-!
# The literal MS pair supplied by Sylow-normalizer escape

For H=LT, the subgroup N_H(T) has odd index and two-core T. It is
proper: otherwise T is a nontrivial characteristic subgroup of itself
normal in LT, contradicting the original source escape condition. That
same condition supplies MS3, with normality relative to LT. The chosen
module puts LT in a genuine two-local subgroup and supplies its SQTK,
characteristic-two and component hypotheses.

The final theorem constructs all C.1.31 inputs for the original pair
(L,T), preserving the full marked quotient in each natural family.
Its symplectic consumer is LineAction.Sp4. The remaining symplectic
classification and G₂ exclusion are not asserted here.
Source: Aschbacher--Smith 3.3.6(d), 3.3.16 and C.1.31, pp.585,591,135.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped Pointwise
open CFSG.Quasithin.Chapter12.Section02
open CFSG.Quasithin.ChapterB.QuasisimpleSource
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.SylowNormalizer
open PointBlocks RecognitionSource.FusionReducibleNormalizer
open Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)

include D S in
/-- The original Sylow normalizer inside LT is the proper odd-index MS witness. -/
theorem sylow_ms_oddIndex
    (hescape : ¬ normalizer (T : Set G) ≤ normalizer (L : Set G)) :
    MSOddIndex L (T : Subgroup G) := by
  let H := L ⊔ (T : Subgroup G)
  let N := H ⊓ normalizer (T : Set G)
  have hTN : (T : Subgroup G) ≤ N := le_inf le_sup_right (T : Subgroup G).le_normalizer
  refine ⟨N, ?_, ?_, ?_⟩
  · apply lt_of_le_of_ne inf_le_left
    intro he
    have hn : H ≤ normalizer (T : Set G) := he ▸ (show N ≤ _ from inf_le_right)
    have hh := characteristic_eq_bot_of_escape S.source D hescape
      (⊤ : Subgroup (T : Subgroup G)) (by
        simpa only [← MonoidHom.range_eq_map, range_subtype, Sylow.coe_coe] using hn)
    have ht : (T : Subgroup G) = ⊥ := by
      have hh' := congrArg (map (T : Subgroup G).subtype) hh
      simpa only [← MonoidHom.range_eq_map,range_subtype,Subgroup.map_bot] using hh'
    exact D.ne_bot (bot_unique (D.le_sylow.trans_eq ht))
  · apply Odd.of_dvd_nat _ (index_dvd_of_le (show
      (T.subtype (show (T : Subgroup G) ≤ H from le_sup_right) : Subgroup H) ≤
        N.subgroupOf H from fun x hx => hTN hx))
    exact Nat.not_even_iff_odd.mp (fun he =>
      (T.subtype (show (T : Subgroup G) ≤ H from le_sup_right)).not_dvd_index
        (even_iff_two_dvd.mp he))
  · apply le_antisymm
    · have hh := pCoreIn_le_sylow N (T.subtype hTN)
      simpa only [Sylow.coe_subtype,map_subgroupOf_eq_of_le hTN] using hh
    · exact le_pCoreIn_of_normalizes T.isPGroup' hTN inf_le_right

include D S in
/-- Normality of characteristic subgroups is relative to LT in the actual escape. -/
theorem sylow_ms_characteristic
    (hescape : ¬ normalizer (T : Set G) ≤ normalizer (L : Set G)) :
    MSNoCharacteristicNormal L (T : Subgroup G) := by
  intro C hc hn
  let := hc
  apply characteristic_eq_bot_of_escape S.source D hescape C
  exact (normal_subgroupOf_iff_le_normalizer
    ((map_subtype_le C).trans le_sup_right)).mp hn

/-- All genuine C.1.31 premises for (L,T), with the original natural marking. -/
theorem sylow_msPair_of_escape (c : Coordinates D S.field)
    (hescape : ¬ normalizer (T : Set G) ≤ normalizer (L : Set G)) :
    NonbinaryMSPair S.field L (T : Subgroup G) := by
  refine ⟨S.nonbinary, ?_, ?_, ?_, S.source.maximal_faithful.1.1.1, ?_,
    sylow_ms_oddIndex D S hescape, sylow_ms_characteristic D S hescape⟩
  · have hn : L ⊔ (T : Subgroup G) ≤ normalizer (V : Set G) :=
      sup_le D.normalizes S.sylow_normalizes
    have ht : IsTwoLocal (normalizer (V : Set G)) := by
      let := D.elementary
      exact ⟨V,D.ne_bot,IsElementaryAbelian.isPGroup 2 V,rfl⟩
    have hq := (S.source.simpleQTKE.twoLocal_sqtk ht).subgroup
      ((L ⊔ (T : Subgroup G)).subgroupOf _)
    exact ⟨hq.stronglyQuasithin.of_injective
      (subgroupOfEquivOfLe hn).symm.toMonoidHom (subgroupOfEquivOfLe hn).symm.injective,
      hq.isKGroup.of_injective (subgroupOfEquivOfLe hn).symm.toMonoidHom
        (subgroupOfEquivOfLe hn).symm.injective⟩
  · exact generalizedFitting_eq_pCore_of_selfCentralizing 2 (join_characteristicTwo S.source)
  · intro g hg
    have hp : g ∈ (L : Set G) * ((T : Subgroup G) : Set G) := by
      rw [←coe_mul_of_right_le_normalizer_left L (T : Subgroup G) D.sylow_normalizes_component]
      exact hg
    exact hp
  · cases c with
    | sl3 m => exact Or.inl ⟨m.groupEquiv⟩
    | sp4 m => exact Or.inr (Or.inl ⟨m.groupEquiv⟩)
    | g2 m => exact Or.inr (Or.inr ⟨m.groupEquiv⟩)

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.SylowNormalizer
