module
public import CFSG.Quasithin.ChapterF.Section04.UnitaryFiveSource.FixedSylowOrders
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalUnitaryFiveSource.AmbientClasses
public import Theory.GroupTheory.CharacteristicCentralizerSylow

/-!
# Full fixed-Sylow order obstruction in the original U₅(4) group

The literal inner-preimage equation and inner saturation clause transport
C_S(t) to a Sylow subgroup of the graph twist's inner centralizer, giving
order 256. The original index [T:S] divides four, so the full C_T(t) has
order at most 1024. All outer actors remain in this latter intersection.

In the original ambient group, every involution is fused into the plane-core
center. Its conjugate centralizer contains the entire plane core of order
65536. Hence every ambient involution-centralizer Sylow has order at least
65536, excluding Sylow placement of the represented fixed intersection.

This proves the order contradiction after F.4.37, printed pp.293--294 of
refs/quasithin.pdf, under the concrete representation input. The missing
invariant long-root geometry must still prove ambient Sylow placement;
S=T, both F.4.42 arguments and same-extension completion remain open.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
open ChapterF.GreenBook.UnitaryFive ChapterF.SourceCompletion.UnitaryNonbinary
open Theory.SpecificGroups.UnitaryFive.Descent Theory.SpecificGroups.UnitaryFive.GraphFixed
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L W H A C : Subgroup G} {n : ℕ}
variable (d : Preparation T L H A C (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hp : Group.IsPerfect (residual H)) (U : Model 4)
    (hc : Nonempty (RankTwoAmalgam.Iso
        (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) U.amalgam) ∨
      Nonempty (RankTwoAmalgam.Iso
        (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) U.amalgam.reverse))
include d h hH hp hc

/-- Every ambient involution is conjugate to a point centralized by the whole
original plane core, so its centralizer order is divisible by 2¹⁶. -/
theorem Preparation.unitaryFive_involution_centralizer_two_power_dvd
    (r : UnitaryFiveNormalizerMarking L (residual H) ((T : Subgroup G) ⊓ L) U)
    (x : G) (hx : orderOf x=2) :
    2^16 ∣ Nat.card (centralizer ({x} : Set G)) := by
  obtain ⟨z,hz,hxz⟩ := d.unitaryFive_involution_fused_into_plane_center h hH hp U hc r x hx
  have hQcard : Nat.card (L.pCoreIn 2)=2^16 := by
    rw [pCoreIn,card_map_of_injective L.subtype_injective]
    rcases hc with ho | hr
    · exact (d.not_unitaryFive_unreversed h hH.1.1.2 hp U ho).elim
    exact (d.unitaryFive_local_structure h hH.1.1.2 hp U hr.some).2.2.2.2.1
  have hle : L.pCoreIn 2 ≤ centralizer ({z} : Set G) := by
    obtain ⟨v,hv,rfl⟩ := hz
    intro q hq
    exact mem_centralizer_singleton_iff.mpr (congrArg Subtype.val
      ((mem_center_iff.mp hv) ⟨q,hq⟩))
  rw [card_centralizer_eq_of_isConj x z hxz,←hQcard]
  exact card_dvd_of_le hle

/-- The original plane core gives a uniform lower bound for every ambient
involution-centralizer Sylow, without assuming any particular Sylow placement. -/
theorem Preparation.unitaryFive_involution_centralizer_sylow_lower
    (r : UnitaryFiveNormalizerMarking L (residual H) ((T : Subgroup G) ⊓ L) U)
    (x : G) (hx : orderOf x=2) (P : Sylow 2 (centralizer ({x} : Set G))) :
    65536 ≤ Nat.card P := by
  exact Nat.le_of_dvd Nat.card_pos (P.pow_dvd_card_of_pow_dvd_card
    (d.unitaryFive_involution_centralizer_two_power_dvd h hH hp U hc r x hx))

/-- Count the full fixed Sylow through its intersection with the original S.
The actual PSL₂(16) field degree bounds the remaining index by four. -/
theorem Preparation.unitaryFive_centralizer_card_le_four_mul (t : G) :
    Nat.card ((T : Subgroup G) ⊓ centralizer ({t} : Set G) : Subgroup G) ≤
      4 * Nat.card (sourceS L H ⊓ centralizer ({t} : Set G) : Subgroup G) := by
  let B := (T : Subgroup G) ⊓ centralizer ({t} : Set G)
  have hST := sourceS_le_sylow h.sylow_normalizes hH.1.1.2
  have he : sourceS L H ⊓ B = sourceS L H ⊓ centralizer ({t} : Set G) := by
    dsimp only [B]
    rw [←inf_assoc,inf_eq_left.mpr hST]
  have hi : (sourceS L H).relIndex B ≤ 4 :=
    (relIndex_le_of_le_right (show B ≤ (T : Subgroup G) from inf_le_left)
      ((sourceS L H).subgroupOf (T : Subgroup G)).index_ne_zero_of_finite).trans
      (Nat.le_of_dvd (by decide) (d.unitaryFive_source_sylow_index_dvd h hH hp U hc))
  have hcount := relIndex_mul_relIndex (⊥ : Subgroup G) (sourceS L H ⊓ B) B bot_le inf_le_right
  rw [relIndex_bot_left,relIndex_bot_left,inf_relIndex_right,he] at hcount
  change Nat.card B ≤ _
  rw [←hcount,mul_comm]
  exact Nat.mul_le_mul_right _ hi

/-- The selected inner saturation clause and a represented actor give inner
order 256 and full fixed-Sylow order at most 1024 on the same original maps.
The ambient lower bound then excludes Sylow placement. The independent
F.4.37 root argument must establish that placement to obtain a contradiction. -/
theorem Preparation.unitaryFive_represented_fixed_sylow_orders
    (r : UnitaryFiveNormalizerMarking L (residual H) ((T : Subgroup G) ⊓ L) U)
    (F : RankTwoAmalgam.Iso (UnitaryCompletion.normalizerDiagram L (residual H))
      r.extension.amalgam.reverse)
    (P : Sylow 2 r.extension.middle)
    (hinner : (P : Subgroup r.extension.middle) ⊓
      (inner U.Carrier).comap r.extension.middle.subtype =
      ((sourceS L H).subgroupOf (normalizer (L : Set G) ⊓ normalizer (residual H : Set G))).map
        F.middle.toMonoidHom)
    (t : ↥(normalizer (L : Set G) ⊓ normalizer (residual H : Set G)))
    (ht : orderOf t=2) (u : U.form.unitarySubgroup)
    (hf : (F.middle t).val=unitaryConj U.form u*projectiveAut U.form U.matrix)
    (hsat : let j := inclusion (inf_le_left.trans r.extension.left_le :
        r.extension.middle ≤ r.extension.carrier)
      ∃ R : Sylow 2 (r.extension.baseHom.range ⊓
          centralizer ({j (F.middle t)} : Set r.extension.carrier) : Subgroup r.extension.carrier),
        (R : Subgroup _).map (r.extension.baseHom.range ⊓
          centralizer ({j (F.middle t)} : Set r.extension.carrier)).subtype =
          ((P : Subgroup r.extension.middle).map j) ⊓
            (r.extension.baseHom.range ⊓ centralizer ({j (F.middle t)} : Set r.extension.carrier))) :
    Nat.card (sourceS L H ⊓ centralizer ({t.val} : Set G) : Subgroup G)=256 ∧
      Nat.card ((T : Subgroup G) ⊓ centralizer ({t.val} : Set G) : Subgroup G) ≤ 1024 ∧
      ¬ ∃ Q : Sylow 2 (centralizer ({t.val} : Set G)),
        (Q : Subgroup _).map (centralizer ({t.val} : Set G)).subtype =
          (T : Subgroup G) ⊓ centralizer ({t.val} : Set G) := by
  let D := normalizer (L : Set G) ⊓ normalizer (residual H : Set G)
  have hTD : (T : Subgroup G) ≤ D :=
    le_inf h.sylow_normalizes (hH.1.1.2.trans (le_normalizer_residual H))
  have hSD := (sourceS_le_sylow h.sylow_normalizes hH.1.1.2).trans hTD
  have he : (sourceS L H ⊓ centralizer ({t.val} : Set G)).subgroupOf D =
      (sourceS L H).subgroupOf D ⊓ centralizer ({t} : Set D) := by
    ext x
    change (x.val ∈ sourceS L H ∧ x.val ∈ centralizer ({t.val} : Set G)) ↔
      (x.val ∈ sourceS L H ∧ x ∈ centralizer ({t} : Set D))
    simp only [mem_centralizer_singleton_iff,Subtype.ext_iff,Subgroup.coe_mul]
  have hcard : Nat.card (sourceS L H ⊓ centralizer ({t.val} : Set G) : Subgroup G)=256 := by
    rw [←Nat.card_congr (subgroupOfEquivOfLe (inf_le_left.trans hSD :
      sourceS L H ⊓ centralizer ({t.val} : Set G) ≤ D)).toEquiv,he]
    exact five_represented_inner_sylow_card U r.extension F.middle _ P hinner t
      (by rw [←ht]; exact pow_orderOf_eq_one t) u hf hsat
  have hb := d.unitaryFive_centralizer_card_le_four_mul h hH hp U hc t.val
  rw [hcard] at hb
  refine ⟨hcard,hb,?_⟩
  rintro ⟨Q,hQ⟩
  have hlarge := d.unitaryFive_involution_centralizer_sylow_lower h hH hp U hc r t.val
    ((Subgroup.orderOf_coe t).trans ht) Q
  rw [←hQ,card_map_of_injective (centralizer ({t.val} : Set G)).subtype_injective] at hb
  omega

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
