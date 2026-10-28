module
public import CFSG.Quasithin.ChapterF.Section01.SourceCartan
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.OriginalExtension.Action
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange.MarkedTitsSystem
public import Theory.GroupTheory.Amalgam.GeneratedCompletion.Overlap
public import Theory.GroupTheory.Amalgam.RankTwoCompletion.CoreFaithfulness

/-!
# The actual source Cartan in the universal reduced amalgam

Use F.1.3(5) for the genuine F.1.11 pair reduced over S₀ = O₂(B).
The complete reduced overlap still contains both original odd Borel factors.
Pull its normal two-subgroup and compatible Cartan into that intrinsic overlap,
then map both through its injective universal middle map. This proves the Hall,
normality, commutativity and literal product inputs of the split quotient.
No homomorphism from the original ambient completion to the universal group is
introduced. Both original middle-to-endpoint maps are retained.

Faithfulness of the reduced source triple also proves the universal middle
core trivial, using transport between faithful completions. Regular paths,
reflection choices, root groups and the Chapter 14 exchange alternative are
separate geometric obligations; these algebraic results do not assert them.

Source: Aschbacher--Smith F.1.3(5), F.1.9, printed pp.260--262;
DGS, *Groups and Graphs* (1985), Part II, pp.95--96, (14.2), pp.210--211,
and the split factorization in the proof of Theorem D, p.224.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory RankTwoAmalgam
open scoped Pointwise
open CFSG.Quasithin.ChapterF.Source
open CFSG.Quasithin.ChapterF.Source.SuzukiContainment
open CFSG.Quasithin.ChapterF.Source.DGS85.OriginalExtension
namespace CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange
namespace ReducedCartan
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}

/-- The full reduced overlap enters the universal group through its original left inclusion. -/
def middleMap (L : Fin 2 → Subgroup G) (S : Subgroup G) :
    commonBorel L (reducedSylow L S) →* (reducedAmalgam L S).Universal :=
  (Universal.left (reducedAmalgam L S)).comp (reducedAmalgam L S).left

/-- The same middle map is also the original right inclusion followed by its universal map. -/
theorem middleMap_right : middleMap L S =
    (Universal.right (reducedAmalgam L S)).comp (reducedAmalgam L S).right :=
  Universal.compatible _

/-- The whole reduced overlap embeds, with neither odd factor removed. -/
theorem middleMap_injective : Function.Injective (middleMap L S) := by
  apply (Monoid.PushoutI.of_injective (Universal.structureMap_injective
    (reducedAmalgam L S) (inclusion_injective (commonBorel_le_parabolic 0))
      (inclusion_injective (commonBorel_le_parabolic 1))) false).comp
  exact inclusion_injective (commonBorel_le_parabolic 0)

/-- The original Borel two-core, transported through the intrinsic reduced overlap. -/
def twoGroup (L : Fin 2 → Subgroup G) (S : Subgroup G) :
    Subgroup (reducedAmalgam L S).Universal :=
  ((reducedSylow L S).subgroupOf (commonBorel L (reducedSylow L S))).map (middleMap L S)

/-- The same compatible odd Cartan, transported through the full reduced overlap. -/
def cartan (c : CompatibleCartans L (reducedSylow L S)) :
    Subgroup (reducedAmalgam L S).Universal :=
  ((c.D 0 ⊔ c.D 1).subgroupOf (commonBorel L (reducedSylow L S))).map (middleMap L S)

/-- The source hypotheses supply compatible Cartans without an extra existence premise. -/
def chosenCartans (h : HypothesisF11 L S) : CompatibleCartans L (reducedSylow L S) :=
  Classical.choice (reduced_hypothesis h).exists_compatibleCartans

/-- The transported Cartan lies in the marked universal Borel. -/
theorem cartan_le (c : CompatibleCartans L (reducedSylow L S)) :
    cartan c ≤ originalMiddle (reducedAmalgam L S) := map_le_range _ _

/-- The transported two-core lies in the marked universal Borel. -/
theorem twoGroup_le : twoGroup L S ≤ originalMiddle (reducedAmalgam L S) :=
  map_le_range _ _

/-- The source two-core remains a two-group in the universal completion. -/
theorem twoGroup_isTwo (h : HypothesisF11 L S) : IsPGroup 2 (twoGroup L S) :=
  (reduced_hypothesis h).S_isP.comap_subtype.map (middleMap L S)

/-- Normality is relative to the actual universal Borel. -/
theorem twoGroup_normalized (h : HypothesisF11 L S) :
    originalMiddle (reducedAmalgam L S) ≤ normalizer (twoGroup L S : Set _) := by
  let U := (reducedSylow L S).subgroupOf (commonBorel L (reducedSylow L S))
  let : U.Normal := reduced_sylow_normal h
  have hh := U.le_normalizer_map (middleMap L S)
  change (middleMap L S).range ≤ normalizer (U.map (middleMap L S) : Set _)
  simpa only [normalizer_eq_top, ← MonoidHom.range_eq_map] using hh

/-- F.1.3(5) makes the transported joint Cartan abelian. -/
theorem cartan_abelian (h : HypothesisF11 L S)
    (c : CompatibleCartans L (reducedSylow L S)) : IsMulCommutative (cartan c) := by
  let := c.joint_abelian (reduced_hypothesis h)
  exact inferInstanceAs (IsMulCommutative
    (((c.D 0 ⊔ c.D 1).subgroupOf (commonBorel L (reducedSylow L S))).map (middleMap L S)))

/-- The two transported factors generate exactly the full marked reduced Borel. -/
theorem factorization (c : CompatibleCartans L (reducedSylow L S)) :
    twoGroup L S ⊔ cartan c = originalMiddle (reducedAmalgam L S) := by
  change _ ⊔ _ = (middleMap L S).range
  unfold twoGroup cartan
  rw [← Subgroup.map_sup, c.joint_complement.sup_eq_top, ← MonoidHom.range_eq_map]

/-- Injectivity of the middle map preserves the Cartan order and relative index. -/
theorem cartan_hall (c : CompatibleCartans L (reducedSylow L S)) :
    IsHallSubgroup OddHall.oddPrimes
      ((cartan c).subgroupOf (originalMiddle (reducedAmalgam L S))) := by
  let C := (c.D 0 ⊔ c.D 1).subgroupOf (commonBorel L (reducedSylow L S))
  have hc : Nat.card ((cartan c).subgroupOf (originalMiddle (reducedAmalgam L S))) =
      Nat.card C := by
    rw [Nat.card_congr (subgroupOfEquivOfLe (cartan_le c)).toEquiv]
    exact card_map_of_injective middleMap_injective
  have hi : ((cartan c).subgroupOf (originalMiddle (reducedAmalgam L S))).index =
      C.index := by
    change (C.map (middleMap L S)).relIndex (middleMap L S).range = C.index
    rw [MonoidHom.range_eq_map]
    rw [relIndex_map_map_of_injective C ⊤ middleMap_injective, relIndex_top_right]
  constructor
  · intro p hp
    exact c.joint_hall.p_in_pi_of_p_dvd_card p (hc ▸ hp)
  · intro p hp
    exact c.joint_hall.p_in_pi_of_p_dvd_index p (hi ▸ hp)

/-- The transported Cartan has odd order. -/
theorem cartan_odd (c : CompatibleCartans L (reducedSylow L S)) :
    Nat.Coprime 2 (Nat.card (cartan c)) := by
  unfold cartan
  rw [card_map_of_injective middleMap_injective,
    Nat.card_congr (subgroupOfEquivOfLe c.joint_le).toEquiv]
  exact c.joint_odd

/-- The source split factorization is an actual subgroup product, not merely a join. -/
theorem factorization_set (h : HypothesisF11 L S)
    (c : CompatibleCartans L (reducedSylow L S)) :
    (originalMiddle (reducedAmalgam L S) : Set (reducedAmalgam L S).Universal) =
      (twoGroup L S : Set (reducedAmalgam L S).Universal) *
        (cartan c : Set (reducedAmalgam L S).Universal) := by
  rw [← factorization c]
  exact coe_mul_of_right_le_normalizer_left _ _
    ((cartan_le c).trans (twoGroup_normalized h))

/-- Source faithfulness transfers the trivial overlap core to the universal completion. -/
theorem original_core_eq_bot (h : HypothesisF11 L S) :
    ((Universal.left (reducedAmalgam L S)).range ⊓
      (Universal.right (reducedAmalgam L S)).range).normalCore = ⊥ := by
  let d := FaithfulCompletion.ofGeneratedSubgroups
    (parabolic L (reducedSylow L S) 0) (commonBorel L (reducedSylow L S))
    (parabolic L (reducedSylow L S) 1)
    (commonBorel_le_parabolic 0) (commonBorel_le_parabolic 1)
  have hd : d.middle.range.normalCore = ⊥ := by
    rw [FaithfulCompletion.ofGeneratedSubgroups_middle_range, parabolics_generate]
    exact (reduced_hypothesis h).generatedLocallyRankOneTriple.faithful
      _ inferInstance (normalCore_le _)
  rw [Universal.overlap_eq _ (inclusion_injective (commonBorel_le_parabolic 0))
    (inclusion_injective (commonBorel_le_parabolic 1))]
  exact FaithfulCompletion.middle_normalCore_eq_bot_of_model
    (Universal.completion (reducedAmalgam L S) d) d hd

end ReducedCartan
end CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange
