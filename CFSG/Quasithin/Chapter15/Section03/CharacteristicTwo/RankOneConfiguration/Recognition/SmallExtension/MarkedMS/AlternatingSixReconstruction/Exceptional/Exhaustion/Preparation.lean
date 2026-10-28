module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LocalModels
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.Generation
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.Parabolics
public import CFSG.Quasithin.ChapterF.Section01.SourceDefs
public import BenderSuzuki.External.Huppert.II.theorem_6_14
public import Theory.GroupTheory.GeneralizedFitting.SelfCentralizingPrimeCore
public import Theory.GroupTheory.SpecificGroups.SLTwoPermThree

/-!
# Weak-BN preparation for the original exceptional MS pair

The faithful permutation embedding of M/E identifies it with A₆ or S₆.
The concrete local models give an incident rank-one pair containing the
original radical image. A Sylow above that same flag contains the radical,
and source (A) proves that the lifted ordered residuals generate exactly K.
The construction verifies every field of the existing locally-rank-one
interface, including its actual quotient maps and Sylow normalizers.

E retains its cubic quotient over O₂(M). All inputs here are consequences
of the original SmallMSPair, its central marking and the cubic center;
no exhaustion premise occurs. Source: Meierfrankenfeld--Stellmacher (1993),
WBN and hypotheses (P), (A), (B), pp.827--829.
-/

public section
open Subgroup Theory.GroupTheory

namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Exceptional.Exhaustion
open Theory.SpecificGroups.SymmetricSix
universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}

/-- The actual quotient by the retained cubic kernel has a source flag
containing the original radical image. -/
theorem exists_source_localData
    (h : SmallMSPair KnownSimple.IsKnownSimple L R) (e : CentralMarking L)
    (hz : Nat.card (center (L ⧸ pCore 2 L)) = 3) :
    ∃ d : SixLocalData ((L ⊔ R : Subgroup G) ⧸ extensionKernel h),
      (R.subgroupOf (L ⊔ R)).map (QuotientGroup.mk' (extensionKernel h)) ≤
        (d.sylow : Subgroup _) := by
  let f := extensionPermutationAction h e hz
  have hf := extensionPermutationAction_injective h e hz
  have hn : Nonempty (SixLocalData ((L ⊔ R : Subgroup G) ⧸ extensionKernel h)) := by
    rcases extensionPermutationAction_range h e hz with he | he
    · let a := (MonoidHom.ofInjective hf).trans (MulEquiv.subgroupCongr he)
      exact ⟨SixLocalData.alternating.map a.symm⟩
    · let a := ((MonoidHom.ofInjective hf).trans (MulEquiv.subgroupCongr he)).trans topEquiv
      exact ⟨SixLocalData.symmetric.map a.symm⟩
  obtain ⟨d⟩ := hn
  exact d.exists_aligned _ (h.relative_radical.isPGroup.map _)

end AlternatingSixReconstruction.Exceptional.Exhaustion
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS

namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Exceptional.Exhaustion
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}

/-- MS93 preparation on the original relative group. Every field precedes
core exhaustion; the cubic covering kernel is retained in the quotient. -/
structure PreparedSource (h : SmallMSPair KnownSimple.IsKnownSimple L R) where
  localData : SixLocalData ((L ⊔ R : Subgroup G) ⧸ extensionKernel h)
  sylow : Sylow 2 (L ⊔ R : Subgroup G)
  edge_le : R.subgroupOf (L ⊔ R) ≤ (sylow : Subgroup _)
  sylow_le : (sylow : Subgroup _) ≤ (localData.sylow : Subgroup _).comap
    (QuotientGroup.mk' (extensionKernel h))
  faithful : ∀ N : Subgroup ((L ⊔ R : Subgroup G) ⧸ extensionKernel h),
    N.Normal → N ≤ (localData.sylow : Subgroup _) → N = ⊥
  rank_one_generation :
    rankOne ((localData.parabolic false).comap (QuotientGroup.mk' (extensionKernel h))) ⊔
      rankOne ((localData.parabolic true).comap (QuotientGroup.mk' (extensionKernel h))) =
        L.subgroupOf (L ⊔ R)

/-- The original exceptional pair supplies the whole weak-BN preparation,
including lifted ordered-residual generation and the actual radical. -/
theorem preparedSource_nonempty
    (h : SmallMSPair KnownSimple.IsKnownSimple L R) (e : CentralMarking L)
    (hz : Nat.card (center (L ⧸ pCore 2 L)) = 3) : Nonempty (PreparedSource h) := by
  obtain ⟨d, hd⟩ := exists_source_localData h e hz
  obtain ⟨S, hRS, hSB⟩ := exists_sylow_over_quotient
    (QuotientGroup.mk' (extensionKernel h)) (QuotientGroup.mk'_surjective _) d.sylow
    (R.subgroupOf (L ⊔ R)) h.relative_radical.isPGroup hd
  refine ⟨{
    localData := d
    sylow := S
    edge_le := hRS
    sylow_le := hSB
    faithful := ?_
    rank_one_generation := rankOne_generation_of_extension h
      (d.parabolic false) (d.parabolic true) S
      (hSB.trans (comap_mono (d.sylow_le false)))
      (hSB.trans (comap_mono (d.sylow_le true))) d.generation
      (d.primeToResidual_eq_top false) (d.primeToResidual_eq_top true) }⟩
  intro N hN hNB
  have hp : IsPGroup 2 N := d.sylow.isPGroup'.to_le hNB
  exact le_bot_iff.mp ((show N ≤ pCore 2 _ from le_sSup ⟨hN, hp⟩).trans_eq
    (extensionQuotient_twoCore h e))

/-- The source rank-one quotients are literally SL2(2). -/
theorem PreparedSource.rank_one
    {h : SmallMSPair KnownSimple.IsKnownSimple L R} (d : PreparedSource h) (i : Bool) :
    Nonempty (d.localData.parabolic i ⧸ pCore 2 (d.localData.parabolic i) ≃*
      Matrix.SpecialLinearGroup (Fin 2) (ZMod 2)) := by
  obtain ⟨a⟩ := d.localData.quotient i
  obtain ⟨b⟩ := SLTwoPermThree.sl2Two_equiv_perm_three
  exact ⟨a.trans b.symm⟩

/-- The chosen Sylow restricts to the source inverse-image Borel. -/
noncomputable def PreparedSource.borelSylow
    {h : SmallMSPair KnownSimple.IsKnownSimple L R} (d : PreparedSource h) :
    Sylow 2 ((d.localData.sylow : Subgroup _).comap
      (QuotientGroup.mk' (extensionKernel h))) := d.sylow.subtype d.sylow_le

theorem PreparedSource.edge_le_borelSylow
    {h : SmallMSPair KnownSimple.IsKnownSimple L R} (d : PreparedSource h) :
    R.subgroupOf (L ⊔ R) ≤
      (d.borelSylow : Subgroup ((d.localData.sylow : Subgroup _).comap
        (QuotientGroup.mk' (extensionKernel h)))).map
          ((d.localData.sylow : Subgroup _).comap
            (QuotientGroup.mk' (extensionKernel h))).subtype := by
  change R.subgroupOf (L ⊔ R) ≤
    ((d.sylow : Subgroup (L ⊔ R : Subgroup G)).subgroupOf
      ((d.localData.sylow : Subgroup _).comap
        (QuotientGroup.mk' (extensionKernel h)))).map _
  rw [map_subgroupOf_eq_of_le d.sylow_le]
  exact d.edge_le

end AlternatingSixReconstruction.Exceptional.Exhaustion
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS


namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Exceptional.Exhaustion
open ChapterF.Source
universe u
namespace SixLocalData
variable {H : Type u} [Group H] [Finite H]

/-- The concrete local data verifies the Chapter F weak-BN interface with
Pstar equal to P. Its rank-one quotient and Borel-normalizer clause are
proved on the original parabolic and Sylow, not just on abstract models. -/
noncomputable def localRankOneData (d : SixLocalData H) (i : Bool) :
    LocalRankOneData (d.parabolic i) (d.sylow : Subgroup H) := by
  let S := d.sylow.subtype (d.sylow_le i)
  have hm : (S : Subgroup (d.parabolic i)).map (d.parabolic i).subtype =
      (d.sylow : Subgroup H) := map_subgroupOf_eq_of_le (d.sylow_le i)
  have hn : normalizer ((d.sylow : Subgroup H) : Set H) ⊓ d.parabolic i = (d.sylow : Subgroup H) := by
    have hh := congrArg (fun N : Subgroup (d.parabolic i) => N.map (d.parabolic i).subtype)
      (d.sylow_normalizer i)
    rw [← (d.sylow.subtype (d.sylow_le i)).coe_coe, Sylow.coe_subtype,
      ← subgroupOf_normalizer_eq (d.sylow_le i), subgroupOf_map_subtype] at hh
    exact hh.trans hm
  refine {
    finite_P := inferInstance
    Pstar := d.parabolic i
    Pstar_le := le_rfl
    normal := by rw [subgroupOf_self]; infer_instance
    same_core := rfl
    supplement := sup_eq_left.mpr (d.sylow_le i)
    characteristic_two := generalizedFitting_eq_pCore_of_selfCentralizing 2
      (d.self_centralizing i)
    sylow := S
    borel_eq := ?_
    quotient := ?_ }
  · rw [hm, inf_eq_right.mpr (d.sylow_le i), inf_comm, hn]
  · obtain ⟨a⟩ := d.quotient i
    obtain ⟨b⟩ := BenderSuzuki.External.huppert_II_6_14_a_psl2_card_two
      (K := ZMod 2) (by simp)
    exact .linear 1 (by decide)
      ⟨ZMod 2, inferInstance, inferInstance, by simp, ⟨a.trans b.symm⟩⟩

/-- The distinguished subgroup in this source witness is the entire parabolic. -/
theorem localRankOneData_Pstar (d : SixLocalData H) (i : Bool) :
    (d.localRankOneData i).Pstar = d.parabolic i := by rfl

end SixLocalData
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}

/-- All WBN clauses on the actual quotient M/E, with the original cubic
extension kernel. The source extension and pushing-up clauses remain the
already-proved properties of the original SmallMSPair. -/
theorem PreparedSource.weakBN
    {h : SmallMSPair KnownSimple.IsKnownSimple L R} (d : PreparedSource h) :
    LocallyRankOneTriple ![d.localData.parabolic false, d.localData.parabolic true]
      (d.localData.sylow : Subgroup _) where
  generate := d.localData.generation
  intersection := d.localData.intersection
  faithful := d.faithful
  local_data i := by
    fin_cases i
    · exact ⟨d.localData.localRankOneData false⟩
    · exact ⟨d.localData.localRankOneData true⟩

/-- Generation uses precisely the distinguished Pstar witnesses of WBN. -/
theorem PreparedSource.rank_one_star_generation
    {h : SmallMSPair KnownSimple.IsKnownSimple L R} (d : PreparedSource h) :
    CFSG.Quasithin.ChapterC.BinaryMS.MS93.rankOne
      ((d.localData.localRankOneData false).Pstar.comap
        (QuotientGroup.mk' (extensionKernel h))) ⊔
    CFSG.Quasithin.ChapterC.BinaryMS.MS93.rankOne
      ((d.localData.localRankOneData true).Pstar.comap
        (QuotientGroup.mk' (extensionKernel h))) = L.subgroupOf (L ⊔ R) := by
  rw [d.localData.localRankOneData_Pstar, d.localData.localRankOneData_Pstar]
  exact d.rank_one_generation

end AlternatingSixReconstruction.Exceptional.Exhaustion
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
