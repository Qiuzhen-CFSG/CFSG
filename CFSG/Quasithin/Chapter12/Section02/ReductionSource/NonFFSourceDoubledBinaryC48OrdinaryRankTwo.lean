module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceDoubledBinaryC48OrdinaryModels
public import CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinaryPlacedLocals

/-!
# The original ordinary doubled-binary quotient has no rank-two row

The original residual LH is perfect and contains the whole doubled orbit.
C.2.8 gives the literal equality W=[W,LH]. Thus W survives the full center
of every ordinary component containing LH, and its image is a nontrivial
two-subgroup of the perfect residual image. The latter still has its actual
SL₃(2) quotient. These are precisely the hypotheses of the previously proved
two-local model exclusions, so all Theorem C rank-two families disappear.

No parabolic placement, simple residual embedding, or extra module marking
is supplied as an assumption. The remaining ordinary models are PSL₅(2),
M₂₄, J₄, He and Ru; their original module arguments are separate duties.
Source: Aschbacher--Smith C.3.5 and C.4.8, printed pp.150--154,
applied to the original Chapter 12 non-FF doubled-binary reciprocal witness.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter4 Chapter4.Section04 Chapter4.Section02.RankOneReciprocalEscape
open ChapterB.QuasisimpleSource Chapter7.NormalizedSource ChapterA.Section02
open ClassificationModels
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)

/-- The full moved orbit supplies the contained nontrivial two-subgroup
in the literal ordinary component's central quotient. -/
theorem sourceOrbit_binary_witness_ordinary_moved_local_data
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (hd : D.MarkedDoubled)
    (F : BinaryField) (hF : F.degree = 1) (hmodel : D.HasNaturalThreeSeed F)
    {A J H U : Subgroup G} (hw : Witness L V A J H U)
    (hWJ : D.sourceOrbit ≤ J.pCoreIn 2)
    (hJC : J.pCoreIn 2 ≤ sectionCentralizerIn (normalizer (L : Set G)) L)
    (K : Subgroup H) (hK : IsComponent H K) :
    DoubledBinaryPlacedLocals.LocalData (K ⧸ center K) := by
  let LH := (solvableResidual (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype
  have hc := D.sourceOrbit_binary_witness_hypothesisC28 h hd F hF hmodel hw hWJ hJC
  have hLH : LH ≤ H := hc.component_le.trans hc.local_le
  have hLK : LH ≤ K.map H.subtype := by
    intro l hl
    exact ⟨⟨l,hLH hl⟩,hc.ordinary_component_contains_original K hK hl,rfl⟩
  have hn := (normal_subgroupOf_iff_le_normalizer hc.component_le).mp
    hw.2.2.2.2.2.2.2.2.1
  have hspan : conjugateSpanBy LH (H ⊓ normalizer (L : Set G)) = LH :=
    le_antisymm (conjugateSpanBy_le le_rfl hn) (le_conjugateSpanBy _ _)
  let : Group.IsPerfect LH := hspan ▸ hc.span_perfect
  have hWL : D.sourceOrbit ≤ LH := hspan ▸ hc.module_le
  have hm : D.sourceOrbit = ⁅D.sourceOrbit,LH⁆ := hspan ▸ hc.module_commutator
  have hLN : LH ≤ normalizer (D.sourceOrbit : Set G) :=
    (map_subtype_le _).trans (inf_le_left.trans D.sourceOrbit_component_normalizes)
  obtain ⟨_,_,_,_,_,_,e,_,_⟩ :=
    D.sourceOrbit_binary_witness_coordinates h hd F hF hmodel hw
  let a : K.map H.subtype ≃* K := (K.equivMapOfInjective H.subtype H.subtype_injective).symm
  let i : LH →* K := a.toMonoidHom.comp (inclusion hLK)
  exact DoubledBinaryPlacedLocals.localData_of_moved_subgroup LH D.sourceOrbit
    (IsElementaryAbelian.isPGroup 2 D.sourceOrbit) hc.module_nontrivial hWL hLN hm
    i (a.injective.comp (inclusion_injective hLK)) e

/-- Every rank-two family, including the derived and Tits endpoints,
is excluded on the original ordinary component and full center quotient. -/
theorem sourceOrbit_binary_witness_ordinary_not_rank_two
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (hd : D.MarkedDoubled)
    (F : BinaryField) (hF : F.degree = 1) (hmodel : D.HasNaturalThreeSeed F)
    {A J H U : Subgroup G} (hw : Witness L V A J H U)
    (hWJ : D.sourceOrbit ≤ J.pCoreIn 2)
    (hJC : J.pCoreIn 2 ≤ sectionCentralizerIn (normalizer (L : Set G)) L)
    (K : Subgroup H) (hK : IsComponent H K) (n : ℕ) :
    ¬ IsTheoremCRankTwoModel (K ⧸ center K) n := by
  have hr := (D.sourceOrbit_binary_witness_ordinary_quotient
    h hd F hF hmodel hw hWJ hJC K hK).1
  have hl := D.sourceOrbit_binary_witness_ordinary_moved_local_data
    h hd F hF hmodel hw hWJ hJC K hK
  exact fun hm => hl.not_rank_two hr n hm.toRankTwoModel

/-- The actual ordinary component now has just the binary linear-five
or four named sporadic central quotients. -/
theorem sourceOrbit_binary_witness_ordinary_five_or_sporadic
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (hd : D.MarkedDoubled)
    (F : BinaryField) (hF : F.degree = 1) (hmodel : D.HasNaturalThreeSeed F)
    {A J H U : Subgroup G} (hw : Witness L V A J H U)
    (hWJ : D.sourceOrbit ≤ J.pCoreIn 2)
    (hJC : J.pCoreIn 2 ≤ sectionCentralizerIn (normalizer (L : Set G)) L)
    (K : Subgroup H) (hK : IsComponent H K) :
    ClassicalGroup.IsPSL (K ⧸ center K) 5 2 ∨
      ∃ name : SporadicName, (name = .m24 ∨ name = .j4 ∨ name = .he ∨ name = .ru) ∧
        Nonempty ((K ⧸ center K) ≃* name.Carrier) := by
  exact (D.sourceOrbit_binary_witness_ordinary_three_cases
    h hd F hF hmodel hw hWJ hJC K hK).resolve_left (by
      rintro ⟨n,hn⟩
      exact D.sourceOrbit_binary_witness_ordinary_not_rank_two
        h hd F hF hmodel hw hWJ hJC K hK n hn)

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
