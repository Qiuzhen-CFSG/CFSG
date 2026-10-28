module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.Preparation
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.Graph
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Source

/-!
# Applying the exceptional source generators to the entire core

The constructed rank-one generators identify the graph component under the
literal factor embedding. Commutator bounds on both generators consequently
control the whole graph core. Intrinsically, their two bounds in [X,K]
imply [Q,K] = [X,K] and feed the existing exceptional C.1.32 consumer.

The local commutator bounds remain explicit: their critical-distance proof
belongs to this reconstruction owner. Neither this reduction nor the
unconditional preparation proves the full reconstruction. Source:
Meierfrankenfeld--Stellmacher (1993), (3.6), pp.870--872, and the definition
of the source rank-one generators on p.828.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Exceptional.Exhaustion
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}

/-- The ordered source generators are exactly the graph component under
its actual factor embedding. This supplies the generation premise used by
local commutator arguments on the original holomorph graph. -/
theorem PreparedSource.graph_rank_one_generation
    {h : SmallMSPair KnownSimple.IsKnownSimple L R} (d : PreparedSource h) :
    (rankOne ((d.localData.parabolic false).comap
      (QuotientGroup.mk' (extensionKernel h)))).map (embedM (edge L R)) ⊔
    (rankOne ((d.localData.parabolic true).comap
      (QuotientGroup.mk' (extensionKernel h)))).map (embedM (edge L R)) =
        Ltilde (edge L R) (alpha (edge L R)) := by
  rw [← Subgroup.map_sup, d.rank_one_generation, graph_component h]

/-- A bound on the two actual source generators extends to the full
commutator core. The bounding subgroup need not be normal in the ambient
free amalgam; normalization by the two specified generators suffices. -/
theorem PreparedSource.graph_core_le
    {h : SmallMSPair KnownSimple.IsKnownSimple L R} (d : PreparedSource h)
    (N : Subgroup (FreeAmalgam (edge L R)))
    (hn : ∀ i, (rankOne ((d.localData.parabolic i).comap
      (QuotientGroup.mk' (extensionKernel h)))).map (embedM (edge L R)) ≤
        normalizer (N : Set (FreeAmalgam (edge L R))))
    (hc : ∀ i, ⁅Q (edge L R) (alpha (edge L R)),
      (rankOne ((d.localData.parabolic i).comap
        (QuotientGroup.mk' (extensionKernel h)))).map (embedM (edge L R))⁆ ≤ N) :
    core (edge L R) (alpha (edge L R)) ≤ N := by
  rw [graph_core h]
  rw [← d.rank_one_generation, map_commutator, Subgroup.map_sup,
    ← Q_alpha (edge L R) h.relative_radical.isPGroup h.relative_radical.twoCore_le]
  rw [commutator_comm]
  exact (commutator_mono
    (sup_le (le_commutatorPreimage (hn false) (by rw [commutator_comm]; exact hc false))
      (le_commutatorPreimage (hn true) (by rw [commutator_comm]; exact hc true)))
      le_rfl).trans
    (commutator_commutatorPreimage_le
      (normalizer (N : Set (FreeAmalgam (edge L R)))) _ N le_rfl)

end AlternatingSixReconstruction.Exceptional.Exhaustion
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS

namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Exceptional.Exhaustion
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}

private theorem commutator_sup_le_of_normal
    {M : Type*} [Group M] (Q A B N : Subgroup M) [N.Normal]
    (hA : ⁅Q,A⁆ ≤ N) (hB : ⁅Q,B⁆ ≤ N) : ⁅Q,A ⊔ B⁆ ≤ N := by
  rw [commutator_comm]
  have ha : A ≤ commutatorPreimage (normalizer (N : Set M)) Q N :=
    le_commutatorPreimage le_normalizer_of_normal (by rwa [commutator_comm])
  have hb : B ≤ commutatorPreimage (normalizer (N : Set M)) Q N :=
    le_commutatorPreimage le_normalizer_of_normal (by rwa [commutator_comm])
  exact (commutator_mono (sup_le ha hb) le_rfl).trans
    (commutator_commutatorPreimage_le _ Q N le_rfl)

/-- Exhaustion reduces to the two lifted rank-one commutator bounds. All
normalization and generation hypotheses follow from the original source
pair and its constructed preparation. -/
theorem PreparedSource.coreExhaustion_of_rankOne_bounds
    {h : SmallMSPair KnownSimple.IsKnownSimple L R} (d : PreparedSource h)
    (hc : ∀ i, ⁅pCore 2 (L ⊔ R : Subgroup G),
      rankOne ((d.localData.parabolic i).comap (QuotientGroup.mk' (extensionKernel h)))⁆ ≤
        ⁅centralOmega L R, L.subgroupOf (L ⊔ R)⁆) : CoreExhaustion L R := by
  let := h.relative_normal
  let N := ⁅centralOmega L R, L.subgroupOf (L ⊔ R)⁆
  have : N.Normal := inferInstance
  apply le_antisymm
  · have hb := commutator_sup_le_of_normal _ _ _ N (hc false) (hc true)
    rw [d.rank_one_generation] at hb
    exact hb
  · exact commutator_mono (fun x hx => ((mem_omegaCenterIn_iff _ _).mp hx).1) le_rfl

/-- Actual C.1.32 consumer for the two remaining local bounds. The complete
source preparation is constructed here from h, e and the cubic center. -/
theorem rankTwo_of_rankOne_bounds
    (h : SmallMSPair KnownSimple.IsKnownSimple L R) (e : CentralMarking L)
    (hz : Nat.card (center (L ⧸ pCore 2 L)) = 3)
    (hc : ∀ d : PreparedSource h, ∀ i,
      ⁅pCore 2 (L ⊔ R : Subgroup G),
        rankOne ((d.localData.parabolic i).comap (QuotientGroup.mk' (extensionKernel h)))⁆ ≤
          ⁅centralOmega L R, L.subgroupOf (L ⊔ R)⁆) : RankTwoAlternatives L R := by
  obtain ⟨d⟩ := preparedSource_nonempty h e hz
  exact rankTwo_of_exhaustion h e hz (d.coreExhaustion_of_rankOne_bounds (hc d))

end AlternatingSixReconstruction.Exceptional.Exhaustion
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
