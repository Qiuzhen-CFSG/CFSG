module
public import CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.ModuleOrbits.Classification.QuasisimpleRows

/-!
# The small irreducible actions on the actual component

The full corrected B.4.2 alternatives are intersected with the component's
binary rank two and cubic rank one. This leaves SL₂(4) natural, SL₃(2)
natural, or the marked S₅ deleted action on the same central quotient.
Every B.5.1 clause remains attached to the original section.

Source: Aschbacher--Smith 13.1.10, pp.871--872; B.4.2 and B.5.1.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.ModuleOrbits.Classification
open Chapter1 Chapter1.Section02 Chapter12.Section02 ChapterB.SourceInduction
open ChapterB.QuasisimpleSource
universe u

private theorem two_degree {D : Type*} [Group D] [Finite D]
    (F : BinaryField) (e : D ≃* Matrix.SpecialLinearGroup (Fin 2) F.Carrier)
    (hr : primeRank 2 D = 2) : F.degree = 2 := by
  have hle : F.degree ≤ 2 := by
    have hh := Theory.PSL2.root_two_rank_ge F.Carrier F.card_eq
    rw [primeRank_equiv 2 (e.trans Atlas.RankOneFieldAutomorphisms.slEquivPSL)] at hr
    omega
  have hne : F.degree ≠ 1 := by
    intro he
    let es := e.trans ((ExtensionConsequences.degreeOneNaturalEquiv F he 2).groupEquiv.trans
      ((BinaryLinear.OuterCyclic.slEquivLinear 2).trans
        BinaryLinear.SmallParabolicLevi.linearTwoEquivSymmetricThree))
    have hc : Nat.card D = 6 := by
      rw [Nat.card_congr es.toEquiv]
      simp [Nat.card_eq_fintype_card, Fintype.card_perm, Nat.factorial]
    have hd : primeRank 2 D ≤ 1 := primeRank_le_one_of_square_not_dvd
      (by rw [hc]; norm_num)
    omega
  have := F.degree_pos
  omega

/-- The two-rank determines the field of a natural linear-two component. -/
theorem linearTwo_degree_of_two_rank {D : Type*} [Group D] [Finite D]
    (F : BinaryField) (e : D ≃* Matrix.SpecialLinearGroup (Fin 2) F.Carrier)
    (hr : primeRank 2 D = 2) : F.degree = 2 :=
  two_degree F e hr

private theorem three_degree {D : Type*} [Group D] [Finite D]
    (F : BinaryField) (e : D ≃* Matrix.SpecialLinearGroup (Fin 3) F.Carrier)
    (hr2 : primeRank 2 D = 2) (hr3 : primeRank 3 D = 1) : F.degree = 1 := by
  have ho : Odd F.degree := by
    by_contra hn
    have hh := Theory.SpecificGroups.SignedThreeCubicRank.linear_special F.card_eq
      (Nat.not_odd_iff_even.mp hn)
    rw [primeRank_equiv 3 e] at hr3
    omega
  let ep := e.trans
    (Matrix.PSL3.OddDegreeProjectiveComparison.specialProjectiveEquiv F.card_eq ho)
  have hh := Matrix.PSL3Even.two_rank F.Carrier F.degree_pos F.card_eq
  rw [primeRank_equiv 2 ep] at hr2
  omega

/-- The surviving irreducible actions, with the component marking retained. -/
@[expose] def SmallIrreducibleAction {D V : Type*} [Group D] [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) D V) (K H : Subgroup D) : Prop :=
  (∃ F : BinaryField, F.degree = 2 ∧ IsLinearNatural (ρ.comp K.subtype) F 2) ∨
    IsLinearNatural (ρ.comp K.subtype) BinaryField.two 3 ∨
    Nonempty (MarkedActionEquiv ρ H K (BinaryPermutation.naturalRepresentation (Fin 5))
      (alternatingGroup (Fin 5)))

/-- Intersect all B.4.2 actions with the actual component ranks. -/
theorem irreducible_action_of_small_ranks {D V : Type*} [Group D] [Finite D]
    [AddCommGroup V] [Module (ZMod 2) V]
    {ρ : Representation (ZMod 2) D V} {K H : Subgroup D}
    (hc : ProjectiveLine.IrreducibleActionCase ρ K H)
    (hr2 : primeRank 2 K = 2) (hr3 : primeRank 3 K = 1) :
    SmallIrreducibleAction ρ K H := by
  have no_rank {E : Type} [Group E] [Finite E] (e : K ≃* E)
      (hh : 2 ≤ primeRank 3 E) : False := by
    rw [primeRank_equiv 3 e] at hr3
    omega
  have no_alt {n : ℕ} (hn : 6 ≤ n) (e : K ≃* alternatingGroup (Fin n)) : False :=
    no_rank e (alternatingGroup.TwoThreeCycles.two_le_primeRank hn)
  have no_linear {n : ℕ} (hn : 4 ≤ n)
      (e : K ≃* Matrix.SpecialLinearGroup (Fin n) (ZMod 2)) : False :=
    no_rank e (Theory.SpecificGroups.Classical.BinaryLinearThreeRank.two_le_primeRank hn)
  cases hc with
  | linearTwo F hg e ho hr =>
    exact Or.inl ⟨F, two_degree F e.groupEquiv hr2, ⟨e⟩⟩
  | linearThree F hg e hr =>
    let b := ExtensionConsequences.degreeOneNaturalEquiv F
      (three_degree F e.groupEquiv hr2 hr3) 3
    exact Or.inr (Or.inl ⟨⟨e.groupEquiv.trans b.groupEquiv,
      e.linearEquiv.trans b.linearEquiv, fun g v =>
        (congrArg b.linearEquiv (e.intertwines g v)).trans (b.intertwines _ _)⟩⟩)
  | symplectic F hl hg e hr =>
    exact (no_rank e.groupEquiv
      (Theory.SpecificGroups.Classical.BinaryDerivedCubicRank.symplectic.trans
        (Theory.GroupTheory.primeRank_le_of_injective 3 (commutator _).subtype (commutator _).subtype_injective))).elim
  | symplecticTwo e hr =>
    exact (no_rank e.subgroupEquiv
      Theory.SpecificGroups.Classical.BinaryDerivedCubicRank.symplectic).elim
  | g2 F hl hg e ho hr =>
    exact (no_rank e.groupEquiv
      (Theory.SpecificGroups.Classical.BinaryDerivedCubicRank.g2.trans
        (Theory.GroupTheory.primeRank_le_of_injective 3 (commutator _).subtype (commutator _).subtype_injective))).elim
  | g2Two e ho hr =>
    exact (no_rank e.subgroupEquiv
      Theory.SpecificGroups.Classical.BinaryDerivedCubicRank.g2).elim
  | symmetric n hn e ho hr =>
    rcases hn with rfl | rfl
    · exact Or.inr (Or.inr ⟨e⟩)
    · exact (no_alt (by decide) e.subgroupEquiv).elim
  | alternatingSix hg e ho hr => exact (no_alt (by decide) e.groupEquiv).elim
  | alternatingSeven hg hw e hd ho hr => exact (no_alt (by decide) e).elim
  | tripleSix hg a hr =>
    obtain ⟨P⟩ := Sylow.nonempty (p := 3) (G := K)
    have hu := P.primeRank_quotient_le_one
      (P.isCyclic_of_odd_of_primeRank_le_one (by decide) hr3.le) (center K)
    rw [primeRank_equiv 3 a.quotientEquiv] at hu
    have hh := alternatingGroup.TwoThreeCycles.two_le_primeRank (n := 6) (by decide)
    omega
  | binaryLinear n hn hg e hr => exact (no_linear (by omega) e.groupEquiv).elim
  | orthogonalSix hg hw e ho hr => exact (no_alt (by decide) e.groupEquiv).elim
  | symmetricEight hw e hr => exact (no_alt (by decide) e.subgroupEquiv).elim
  | exteriorFive hg hw e hd ho hr => exact (no_linear (by decide) e).elim

variable {G : Type u} [Group G] [Finite G]

/-- The same source section retains all six B.5.1 clauses and all irreducible
clauses, now equipped with its actual small B.4.2 action. -/
theorem irreducibleReduced_small
    {T : Sylow 2 G} (h : Hypothesis1311 T)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {L : Subgroup G} (hL : FaithfulMaximalLocal T L)
    (hn : ¬ IsQuasisimple (XiQuotient L))
    (hmove : L = ⁅L, ChapterB.thompsonJ (T : Subgroup G) 0⁆)
    (hi : IrreducibleReducedCase L) :
    ∃ d : ProjectiveLine.QuasisimpleSourceConclusion
      ((reducedRepresentation L).comp (offenderSubgroup (reducedRepresentation L)).subtype)
      ((NormalizerReducedAction.componentImage L).subgroupOf
        (offenderSubgroup (reducedRepresentation L))),
      IrreducibleSectionCase d.sectionData ∧
      SmallIrreducibleAction d.sectionData.action
        ((NormalizerReducedAction.componentImage L).subgroupOf
          (offenderSubgroup (reducedRepresentation L)))
        (offenderSubgroup d.sectionData.action) := by
  obtain ⟨d,hi⟩ := (irreducibleReducedCase_iff L).mp hi
  have hj := componentImage_le_reducedOffender h hL hn hmove
  let e := (subgroupOfEquivOfLe hj).trans (reducedImageEquivMovedImage h hmany hL hn)
  obtain ⟨p,hp,hp3,hm⟩ := moved_component_pslTwo h hmany hL hn
  obtain ⟨hr2,hr3⟩ := prime_model_ranks hp hp3 (hm.of_mulEquiv e)
  exact ⟨d,hi,irreducible_action_of_small_ranks
    ((irreducibleSectionCase_iff d.sectionData).mp hi).2.2.2.1 hr2 hr3⟩

end CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.ModuleOrbits.Classification
