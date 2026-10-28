module

public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.LineNormalizers.Offenders.BestReduction.FullCoreTransfer.RankOneDispatch.Sections
public import Theory.SpecificGroups.Classical.BinaryLinearThreeRank
public import Theory.Mathieu.M22.ValueBoundParabolics.SmallQuotients
public import Theory.GroupTheory.CComponent.QuasisimpleFactors

/-!
# Exhausting the full quasisimple source conclusion at three-rank one

The complete B.5.1 action list leaves the actual natural SL₂ and SL₃
sections, two identical SL₃ copies, and the natural S₅ action. The other
rows have three-rank at least two, including the small derived endpoints,
the triple cover (via cyclic Sylow subgroups and its A₆ quotient), and all
binary degree-four/five actions. The outer alternatives are checked on the
whole actor, and F*(S₅) = A₅ supplies the literal subgroup marking.

The existing moved-space and quotient constructions retain both nonsplit
extension orientations and restrict the S₅ section only to its embedded A₅.
This is a conditional consequence of the full source conclusion, not a
proof of the universal B.5.1 classification input.

Source: Aschbacher–Smith, combined 1 March 2004 manuscript, B.5.1 and
B.5.6(1), printed pp.99–105, and the proof of 15.3.67, printed p.1154.
-/

public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.Offenders.BestReduction.FullCoreTransfer.RankOneDispatch
open ChapterB.SourceInduction ChapterB.QuasisimpleSource
open Theory.SpecificGroups.Classical
universe u v w z
variable {D : Type u} [Group D] [Finite D]
  {W : Type v} [AddCommGroup W] [Module (ZMod 2) W]
  {ρ : Representation (ZMod 2) D W}

private theorem rankOne_subgroup {L : Subgroup D} (hr : primeRank 3 D ≤ 1) :
    primeRank 3 L ≤ 1 :=
  (primeRank_le_of_injective 3 L.subtype L.subtype_injective).trans hr

private theorem exclude_subgroup {E : Type*} [Group E] [Finite E]
    {L : Subgroup D} (e : L ≃* E) (he : 2 ≤ primeRank 3 E)
    (hr : primeRank 3 D ≤ 1) : False := by
  have hh := rankOne_subgroup (L := L) hr
  rw [primeRank_equiv 3 e] at hh
  omega

private theorem symplectic_rank (F : BinaryField) :
    2 ≤ primeRank 3 (Matrix.symplecticGroup (Fin 2) F.Carrier) :=
  Theory.SpecificGroups.Classical.BinaryDerivedCubicRank.symplectic.trans
    (primeRank_le_of_injective 3 _ (commutator _).subtype_injective)

private theorem g2_rank {F : Type*} [Field F] [Finite F] [CharP F 2] :
    2 ≤ primeRank 3 (Atlas.G2.Model F) :=
  Theory.SpecificGroups.Classical.BinaryDerivedCubicRank.g2.trans
    (primeRank_le_of_injective 3 _ (commutator _).subtype_injective)

private theorem symmetric_rank {n : ℕ} (hn : 6 ≤ n) :
    2 ≤ primeRank 3 (Equiv.Perm (Fin n)) :=
  (alternatingGroup.TwoThreeCycles.two_le_primeRank hn).trans
    (primeRank_le_of_injective 3 _ (alternatingGroup (Fin n)).subtype_injective)

private theorem exclude_tripleSix {L : Subgroup D}
    (e : (L ⧸ center L) ≃* alternatingGroup (Fin 6))
    (hr : primeRank 3 D ≤ 1) : False := by
  let P : Sylow 3 L := Classical.choice inferInstance
  have hc := P.isCyclic_of_odd_of_primeRank_le_one (by decide) (rankOne_subgroup hr)
  have hb := P.primeRank_quotient_le_one hc (center L)
  rw [primeRank_equiv 3 e] at hb
  have := alternatingGroup.TwoThreeCycles.two_le_primeRank (by decide : 6 ≤ 6)
  omega

private def wholeActionEquiv {E : Type w} [Group E]
    {X : Type z} [AddCommGroup X] [Module (ZMod 2) X]
    {σ : Representation (ZMod 2) E X}
    (e : ActionEquiv (ρ.comp (⊤ : Subgroup D).subtype) σ) : ActionEquiv ρ σ where
  groupEquiv := Subgroup.topEquiv.symm.trans e.groupEquiv
  linearEquiv := e.linearEquiv
  intertwines g v := e.intertwines ⟨g, mem_top g⟩ v

omit [Finite D] in
private theorem symmetricFive_section {L : Subgroup D} (hL : L = generalizedFitting D)
    (s : MovedSection ρ L)
    (e : ActionEquiv s.action (BinaryPermutation.naturalRepresentation (Fin 5))) :
    RankOneModel ρ := by
  apply symmetricFive_model_of_moved_quotient s e
  exact (congrArg (Subgroup.map e.groupEquiv.toMonoidHom) hL).trans
    ((map_generalizedFitting_equiv e.groupEquiv).trans
      Sporadic.Mathieu.M22ValueBound.SmallQuotients.symmetricFive_generalizedFitting_eq_alternating)

private theorem outer_model {L : Subgroup D} (hL : L = generalizedFitting D)
    (s : MovedSection ρ L) (h : OuterNaturalAction s.action)
    (hr : primeRank 3 D ≤ 1) : RankOneModel ρ := by
  unfold OuterNaturalAction at h
  rcases h with hsym | hg
  · obtain ⟨n, hn, _, ⟨e⟩⟩ := hsym
    by_cases h5 : n = 5
    · subst n
      exact symmetricFive_section hL s e
    · have hb := symmetric_rank (by omega : 6 ≤ n)
      rw [← primeRank_equiv 3 e.groupEquiv] at hb
      omega
  · obtain ⟨e⟩ := hg
    have hb := g2_rank (F := ZMod 2)
    rw [← primeRank_equiv 3 e.groupEquiv] at hb
    omega

private theorem whole_irreducible_model {L H : Subgroup D}
    (hL : L = generalizedFitting D) (s : MovedSection ρ L) (whole : L = ⊤)
    (h : ProjectiveLine.IrreducibleActionCase s.action L H)
    (hr : primeRank 3 D ≤ 1) : RankOneModel ρ := by
  cases h with
  | linearTwo F _ e _ _ => exact linearTwo_model_of_moved_quotient s F whole e
  | linearThree F _ e _ => exact linearThree_model_of_moved_quotient s F whole e hr
  | symplectic F _ _ e _ => exact (exclude_subgroup e.groupEquiv (symplectic_rank F) hr).elim
  | symplecticTwo e _ =>
    exact (exclude_subgroup e.subgroupEquiv
      Theory.SpecificGroups.Classical.BinaryDerivedCubicRank.symplectic hr).elim
  | g2 F _ _ e _ _ => exact (exclude_subgroup e.groupEquiv g2_rank hr).elim
  | g2Two e _ _ =>
    exact (exclude_subgroup e.subgroupEquiv
      Theory.SpecificGroups.Classical.BinaryDerivedCubicRank.g2 hr).elim
  | symmetric n hn e _ _ =>
    rcases hn with rfl | rfl
    · have hH : H = ⊤ := by
        apply top_unique
        rw [← whole]
        exact e.contained
      subst H
      exact symmetricFive_section hL s (wholeActionEquiv e.action)
    · exact (exclude_subgroup e.subgroupEquiv
        (alternatingGroup.TwoThreeCycles.two_le_primeRank (by decide)) hr).elim
  | alternatingSix _ e _ _ =>
    exact (exclude_subgroup e.groupEquiv
      (alternatingGroup.TwoThreeCycles.two_le_primeRank (by decide)) hr).elim
  | alternatingSeven _ _ e _ _ _ =>
    exact (exclude_subgroup e
      (alternatingGroup.TwoThreeCycles.two_le_primeRank (by decide)) hr).elim
  | tripleSix _ a _ => exact (exclude_tripleSix a.quotientEquiv hr).elim
  | binaryLinear d hd _ e _ =>
    exact (exclude_subgroup e.groupEquiv
      (BinaryLinearThreeRank.two_le_primeRank (by omega)) hr).elim
  | orthogonalSix _ _ e _ _ =>
    exact (exclude_subgroup e.groupEquiv
      (alternatingGroup.TwoThreeCycles.two_le_primeRank (by decide)) hr).elim
  | symmetricEight _ e _ =>
    exact (exclude_subgroup e.subgroupEquiv
      (alternatingGroup.TwoThreeCycles.two_le_primeRank (by decide)) hr).elim
  | exteriorFive _ _ e _ _ _ =>
    exact (exclude_subgroup e
      (BinaryLinearThreeRank.two_le_primeRank (by decide)) hr).elim

/-- The full source B.5.1 conclusion at three-rank one supplies the actual
SL₂, S₅, or odd-degree SL₃ section, including both central extension orientations. -/
theorem quasisimple_model (hr : primeRank 3 D ≤ 1)
    (c : ProjectiveLine.QuasisimpleSourceConclusion ρ (generalizedFitting D)) :
    RankOneModel ρ := by
  cases c.clause_one with
  | irreducible _ _ _ h ext =>
    rcases ext with whole | ⟨_, outer⟩
    · exact whole_irreducible_model rfl c.sectionData whole h hr
    · exact outer_model rfl c.sectionData outer hr
  | doubleThree F whole e _ _ => exact doubleThree_model c.sectionData F whole e hr
  | naturalDual d hd _ natural =>
    obtain ⟨e⟩ := natural
    exact (exclude_subgroup e.groupEquiv
      (BinaryLinearThreeRank.two_le_primeRank (by omega)) hr).elim
  | repeatedNatural d r hd _ _ _ natural =>
    obtain ⟨e⟩ := natural
    exact (exclude_subgroup e.groupEquiv
      (BinaryLinearThreeRank.two_le_primeRank (by omega)) hr).elim
end CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.Offenders.BestReduction.FullCoreTransfer.RankOneDispatch
