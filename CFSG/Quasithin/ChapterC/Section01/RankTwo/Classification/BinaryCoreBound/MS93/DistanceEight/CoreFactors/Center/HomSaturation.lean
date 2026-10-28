module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.CoreFactors.Higher.Quotients.FirstDirect.CenterIntersection
public import Theory.Representation.BinaryThreeHomSaturation.Groups

/-!
# Saturation of the marked core commutator rows

The source projection is onto SL₃(2), and CommonFacts supplies its fixed
marking. Applying a conjugation equation at a preimage of the inverse actor
shows that the row image is stable under the literal dual precomposition.
The binary Hom saturation theorem then makes the row map onto.

For rows from the actual core into Hom(first dual,H), original core
normalization and the source H-layer's elementary structure and order four
supply all model premises. Hence the literal row kernel has index 64.
The independent commutator-row construction supplies the conjugation and
evaluation-generation equations; the center assembly owns the comparison
of this kernel with the second hat. No quotient-normality premise is used.

Source: Meierfrankenfeld–Stellmacher, Pushing up weak BN-pairs of rank two
(1993), the core-center argument (4.5), printed pp.895 and 899.
-/

@[expose] public section
open Subgroup Stellmacher.PushingUp.AmalgamGraph
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.CoreFactors.Center.HomSaturation
open DistanceFour.Linear (W S dual)
open Representation.BinaryThreeHom (dualAction dualAction_inv_apply surjective_of_dual_evaluation_ranges card_hom)
variable {M : Type*} [Group M] {L R : Subgroup M}
  {source : LocalSource L R} {geometry : Geometry R}

/-- The image of a row map with the literal marked source action is stable
under every dual precomposition. The marking is the one in CommonFacts. -/
theorem marked_row_stable (common : CommonFacts R source geometry)
    {T : Type*} [Group T] [IsElementaryAbelian 2 T]
    {B : Subgroup (FreeAmalgam R)} (hB : Mbar R ≤ normalizer B)
    (row : B →* (Multiplicative W →* T))
    (hrow : ∀ (m : M) (x y : B),
      (y : FreeAmalgam R) = embedM R m * (x : FreeAmalgam R) * (embedM R m)⁻¹ →
      ∀ v : W, row y (Multiplicative.ofAdd (dual (common.natural.marking (source.projection m)) v)) =
        row x (Multiplicative.ofAdd v)) :
    ∀ (g : S) (b : B), ∃ c : B,
      ∀ v : W, row c (Multiplicative.ofAdd v) = row b (Multiplicative.ofAdd (dualAction g v)) := by
  intro g b
  obtain ⟨m,hm⟩ := source.projection_surjective (common.natural.marking.symm g⁻¹)
  have hmg : common.natural.marking (source.projection m) = g⁻¹ := by simp [hm]
  have hc : embedM R m * b.val * (embedM R m)⁻¹ ∈ B :=
    le_normalizer_iff.mp hB _ ⟨m,rfl⟩ _ b.property
  let c : B := ⟨embedM R m * b.val * (embedM R m)⁻¹,hc⟩
  refine ⟨c, ?_⟩
  intro v
  have he := hrow m b c rfl (dualAction g v)
  rw [hmg] at he
  change row c (Multiplicative.ofAdd (dualAction g⁻¹ (dualAction g v))) = _ at he
  simpa only [dualAction_inv_apply] using he

/-- Full Hom image from the literal marked action and the actual evaluation ranges. -/
theorem marked_row_surjective (common : CommonFacts R source geometry)
    {T : Type*} [Group T] [IsElementaryAbelian 2 T]
    {B : Subgroup (FreeAmalgam R)} (hB : Mbar R ≤ normalizer B)
    (row : B →* (Multiplicative W →* T))
    (hrow : ∀ (m : M) (x y : B),
      (y : FreeAmalgam R) = embedM R m * (x : FreeAmalgam R) * (embedM R m)⁻¹ →
      ∀ v : W, row y (Multiplicative.ofAdd (dual (common.natural.marking (source.projection m)) v)) =
        row x (Multiplicative.ofAdd v))
    (hgen : (⨆ b : B, (row b).range) = ⊤) : Function.Surjective row :=
  surjective_of_dual_evaluation_ranges row (marked_row_stable common hB row hrow) hgen

/-- The original core is normalized by the original M-vertex stabilizer. -/
theorem core_normalized : Mbar R ≤ normalizer (core R (alpha R)) := by
  rw [← stabilizer_m_base, ← alpha]
  exact DistanceTwo.core_normalized _

variable [Finite M] (common : CommonFacts R source geometry) (earlier : Earlier R geometry)
  [IsMulCommutative (H R (alpha R))]
include earlier

omit [Finite M] in
/-- The actual core row into Hom(first dual,H) is onto, retaining the literal
conjugation and first-dual markings supplied by the commutator producer. -/
theorem core_row_surjective
    (row : core R (alpha R) →* (Multiplicative W →* H R (alpha R)))
    (hrow : ∀ (m : M) (x y : core R (alpha R)),
      (y : FreeAmalgam R) = embedM R m * (x : FreeAmalgam R) * (embedM R m)⁻¹ →
      ∀ v : W, row y (Multiplicative.ofAdd (dual (common.natural.marking (source.projection m)) v)) =
        row x (Multiplicative.ofAdd v))
    (hgen : (⨆ b : core R (alpha R), (row b).range) = ⊤) : Function.Surjective row := by
  let := H_elementary_of_central R (alpha R)
    (geometry.V_local (alpha R) rfl common.large_distance) (earlier.centrality (alpha R) rfl)
  exact marked_row_surjective common core_normalized row hrow hgen

/-- The source H-layer has order four, so saturation gives exact kernel index
64 in the original core. No quotient-normality premise is added. -/
theorem core_row_kernel_index
    (row : core R (alpha R) →* (Multiplicative W →* H R (alpha R)))
    (hrow : ∀ (m : M) (x y : core R (alpha R)),
      (y : FreeAmalgam R) = embedM R m * (x : FreeAmalgam R) * (embedM R m)⁻¹ →
      ∀ v : W, row y (Multiplicative.ofAdd (dual (common.natural.marking (source.projection m)) v)) =
        row x (Multiplicative.ofAdd v))
    (hgen : (⨆ b : core R (alpha R), (row b).range) = ⊤) : row.ker.index = 64 := by
  let := H_elementary_of_central R (alpha R)
    (geometry.V_local (alpha R) rfl common.large_distance) (earlier.centrality (alpha R) rfl)
  have hcard : Nat.card (H R (alpha R)) = 4 :=
    Nat.le_antisymm (Early.H_card_le_four common earlier rfl)
      (Early.First.Layer.H_card_lower common earlier (alpha R) rfl)
  rw [Subgroup.index_ker, MonoidHom.range_eq_top.mpr (core_row_surjective common earlier row hrow hgen),
    Subgroup.card_top, card_hom, hcard]
  norm_num
end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.CoreFactors.Center.HomSaturation
