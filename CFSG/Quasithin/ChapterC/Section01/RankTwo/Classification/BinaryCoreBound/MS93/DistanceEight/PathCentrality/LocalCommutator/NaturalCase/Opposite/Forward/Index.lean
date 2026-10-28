module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.LocalCommutator.NaturalCase.Opposite.Forward.Generation
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.PairingControl.FirstPairing.StepThree.RankOne.FixedSection.Coordinates
public import Theory.Representation.PSL3Two.ResidualFFForms.ConstituentBudget.Dimension


/-!
# Order-four image of the full forward orbit span

The literal continuation span is elementary abelian inside the endpoint radius
and lies in the center stabilizer. Its image under the selected frame's marked
projection is therefore an elementary subgroup of SL₃(2), of order at most four.
An image of order at most two would have natural displacement of order at most
two: the displacement of an involution on the eight-element natural space has
image contained in its kernel. The previously proved order-four natural
commutator excludes this case. The projection's exact kernel then identifies
the image order with the required relative index.

This discharges the index field of ForwardFacts without assuming that record.
Source: Meierfrankenfeld--Stellmacher (1993), (4.4.1)(1), printed p.891.
-/

public section

open Subgroup Matrix Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.LocalCommutator.NaturalCase.Opposite.SelectedPath.Continuation
open Escape.PairingControl.FirstPairing.StepThree.RankOne.FixedSection
private abbrev NaturalSpace := Multiplicative (Fin 3 → ZMod 2)

private def delta (g : SL) : NaturalSpace →* NaturalSpace where
  toFun v := Multiplicative.ofAdd (g.val.mulVec v.toAdd - v.toAdd)
  map_one' := by simp
  map_mul' x y := by
    apply Multiplicative.toAdd.injective
    change g.val.mulVec (x.toAdd + y.toAdd) - (x.toAdd + y.toAdd) =
      (g.val.mulVec x.toAdd - x.toAdd) + (g.val.mulVec y.toAdd - y.toAdd)
    rw [mulVec_add]
    abel

-- The square-zero displacement has image contained in its kernel; their
-- cardinalities multiply to eight.
private theorem involution_displacement_card_le_two (g : SL) (hg : g ^ 2 = 1) :
    Nat.card (delta g).range ≤ 2 := by
  have hgg (v : Fin 3 → ZMod 2) : g.val.mulVec (g.val.mulVec v) = v := by
    have he : (g.val * g.val) = (1 : Matrix (Fin 3) (Fin 3) (ZMod 2)) := by
      change (g * g).val = (1 : SL).val
      rw [← pow_two, hg]
    rw [mulVec_mulVec, he, one_mulVec]
  have hn (v : NaturalSpace) : delta g (delta g v) = 1 := by
    apply Multiplicative.toAdd.injective
    change g.val.mulVec (g.val.mulVec v.toAdd - v.toAdd) -
      (g.val.mulVec v.toAdd - v.toAdd) = 0
    rw [mulVec_sub, hgg]
    simp only [ZModModule.sub_eq_add]
    calc
      (v.toAdd + g.val.mulVec v.toAdd) + (g.val.mulVec v.toAdd + v.toAdd) =
        (v.toAdd + v.toAdd) + (g.val.mulVec v.toAdd + g.val.mulVec v.toAdd) := by abel
      _ = 0 := by simp only [ZModModule.add_self]
  have hle : (delta g).range ≤ (delta g).ker := by
    rintro _ ⟨v, rfl⟩
    exact hn v
  have hcard := (delta g).ker.card_mul_index
  rw [index_ker] at hcard
  have hspace : Nat.card NaturalSpace = 8 := by
    change Nat.card (Fin 3 → ZMod 2) = 8
    norm_num only [Nat.card_fun, Nat.card_zmod, Nat.card_fin]
  rw [hspace] at hcard
  have hmono := card_le_of_le hle
  nlinarith

private theorem matrixDisplacement_card_le_two (E : Subgroup SL) (hE : Nat.card E ≤ 2) :
    Nat.card (matrixDisplacement E) ≤ 2 := by
  by_cases hsmall : Nat.card E ≤ 1
  · have hbot : E = ⊥ := eq_bot_of_card_le E hsmall
    have hd : matrixDisplacement E = ⊥ := by
      apply le_bot_iff.mp
      apply (Subgroup.closure_le _).mpr
      rintro _ ⟨g, hg, v, rfl⟩
      have hg1 : g = 1 := by simpa only [hbot, mem_bot] using hg
      simp [hg1]
    rw [hd, card_bot]
    omega
  · have htwo : Nat.card E = 2 := by omega
    obtain ⟨g, _, hall⟩ := (Nat.card_eq_two_iff' (1 : E)).mp htwo
    have hg2 : (g : SL) ^ 2 = 1 := by
      have hpow := pow_card_eq_one' (x := g)
      rw [htwo] at hpow
      exact congrArg Subtype.val hpow
    have hle : matrixDisplacement E ≤ (delta (g : SL)).range := by
      apply (Subgroup.closure_le _).mpr
      rintro _ ⟨x, hx, v, rfl⟩
      by_cases hx1 : x = 1
      · have hz : Multiplicative.ofAdd (x.val.mulVec v - v) = (1 : NaturalSpace) := by
          simp [hx1]
        rw [hz]
        exact (delta (g : SL)).range.one_mem
      · have hxg : (⟨x, hx⟩ : E) = g := hall ⟨x,hx⟩ (by
          intro h; exact hx1 (congrArg Subtype.val h))
        have hxe : x = g := congrArg Subtype.val hxg
        exact ⟨Multiplicative.ofAdd v, by simp only [hxe]; rfl⟩
    exact (card_le_of_le hle).trans (involution_displacement_card_le_two g hg2)

private theorem elementary_card_le_four (E : Subgroup SL) [IsElementaryAbelian 2 E] :
    Nat.card E ≤ 4 := by
  by_cases hn : E = ⊥
  · simp [hn]
  have htwo : Representation.BinaryOffender.IsElementaryTwo E := ⟨hn, inferInstance⟩
  rw [htwo.card_eq_two_pow_rank]
  exact Nat.pow_le_pow_right (by decide : 0 < 2)
    (BinaryLinearThree.ResidualFFForms.ConstituentBudget.elementary_rank_le_two E inferInstance)

variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}
variable {source : LocalSource L R} {geometry : Geometry R} {a c : Vertex R}
variable {s : SelectedPath R geometry a c} (w : s.Continuation)

/-- The full endpoint-stabilizer orbit span has order-four image at the center.
The projection and the natural action use the selected frame's original marking. -/
theorem span_index (common : CommonFacts R source geometry)
    (hb : 4 < geometry.b R) :
    (Q R s.center).relIndex (s.continuationSpan w) = 4 := by
  let S := stabilizer R s.center
  let T := (s.continuationSpan w).subgroupOf S
  let U₀ := (U R s.center).subgroupOf S
  let e := s.frame.naturalU.marking.toMonoidHom.comp s.frame.sectionData.projection
  let E := T.map e
  have hT : s.continuationSpan w ≤ S := w.span_le_center_stabilizer (by omega)
  have hU : U R s.center ≤ S := (U_le_Z R s.center).trans (Z_le_stabilizer R s.center)
  have hker : e.ker = (Q R s.center).subgroupOf S := by
    ext x
    change s.frame.naturalU.marking (s.frame.sectionData.projection x) = 1 ↔ _
    rw [s.frame.naturalU.marking.map_eq_one_iff]
    change x ∈ s.frame.sectionData.projection.ker ↔ _
    rw [s.frame.sectionData.module_section.projection_kernel]
  have hcard : Nat.card E = (Q R s.center).relIndex (s.continuationSpan w) := by
    rw [show E = T.map e from rfl, ← relIndex_ker, hker, relIndex_subgroupOf hT]
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let := V_elementary_of_four_lt R s.path.end_color hb
  let : IsElementaryAbelian 2 (s.continuationSpan w) :=
    IsElementaryAbelian.of_le (w.span_le_radius (by omega))
  let : IsElementaryAbelian 2 T := IsElementaryAbelian.subgroupOf hT
  let : IsElementaryAbelian 2 E := IsElementaryAbelian.map e
  have hd : Nat.card (matrixDisplacement E) = 4 := by
    rw [show E = T.map (s.frame.naturalU.marking.toMonoidHom.comp
      s.frame.sectionData.projection) from rfl,
      Escape.PairingControl.FirstPairing.StepThree.RankOne.FixedSection.natural_commutator_card
        s.frame.naturalU T]
    have he : (⁅U₀,T⁆).map S.subtype = ⁅U R s.center, s.continuationSpan w⁆ := by
      rw [map_commutator, map_subgroupOf_eq_of_le hU, map_subgroupOf_eq_of_le hT]
    calc
      Nat.card (⁅U₀,T⁆ : Subgroup S) = Nat.card ((⁅U₀,T⁆).map S.subtype) :=
        (card_map_of_injective S.subtype_injective).symm
      _ = 4 := by rw [he]; exact w.natural_commutator_card common hb
  have hupp := elementary_card_le_four E
  have hnot : ¬ Nat.card E ≤ 2 := by
    intro h
    have hh := matrixDisplacement_card_le_two E h
    rw [hd] at hh
    omega
  have hdiv := (IsElementaryAbelian.isPGroup 2 E).card_eq_or_dvd
  have hfour : Nat.card E = 4 := by omega
  exact hcard.symm.trans hfour
end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.LocalCommutator.NaturalCase.Opposite.SelectedPath.Continuation
