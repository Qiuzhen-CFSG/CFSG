module

public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.ComponentReduction.PreliminaryActions.Comparison
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.ComponentReduction.PreliminaryActions.Assembly
public import Theory.SpecificGroups.BinaryLinear.SmallCubicRank

/-!
# Exhausting the B.5.1 rows at three-rank one

We compare the actual group isomorphism in every projective-line-correct
B.5.1 row with the three-rank of its marked component. The symplectic and G₂
arguments use the derived subgroups even at the small endpoints. For a
central cover of A₆, rank one would force a cyclic Sylow three-subgroup;
its image in A₆ would still be cyclic, contradicting the two independent
three-cycles. No unrestricted quotient monotonicity of prime rank is used.

The surviving alternatives retain their original actions, offender families
and ratios. This is a reduction of the full source conclusion, not yet the
module-extension or offender comparison required for `ComparedCase`.
The last theorem applies the reduction to the literal seed quotient using
the faithful restriction of the original component.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, B.4.2,
B.5.1 and the first half of the proof of B.5.9, printed pp.86, 99 and 107.
-/

@[expose] public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
namespace CFSG.Quasithin.ChapterB.SourceInduction.ComponentReduction.PreliminaryActions
open QuasisimpleSource
universe u v

private theorem exclude_equiv {L H : Type*} [Group L] [Group H]
    [Finite L] [Finite H] (hr : primeRank 3 L = 1) (e : L ≃* H)
    (hh : 2 ≤ primeRank 3 H) : False := by
  have he := primeRank_equiv 3 e
  omega

private theorem linearThree_odd {L : Type*} [Group L] [Finite L]
    (hr : primeRank 3 L = 1) (F : BinaryField)
    (e : L ≃* Matrix.SpecialLinearGroup (Fin 3) F.Carrier) : Odd F.degree := by
  apply Nat.not_even_iff_odd.mp
  intro he
  exact not_even_linearThree_of_threeRank_one F e he hr

/-- Even the central cover of A₆ cannot have three-rank one. The proof
passes a cyclic Sylow subgroup through the actual central quotient. -/
theorem not_alternatingSix_central_cover_of_threeRank_one
    {L : Type*} [Group L] [Finite L] (hr : primeRank 3 L = 1)
    (e : (L ⧸ center L) ≃* alternatingGroup (Fin 6)) : False := by
  let P : Sylow 3 L := Classical.choice inferInstance
  have hP := P.isCyclic_of_odd_of_primeRank_le_one (by decide) hr.le
  have hq := P.primeRank_quotient_le_one hP (center L)
  rw [primeRank_equiv 3 e] at hq
  have ha := alternatingGroup.TwoThreeCycles.two_le_primeRank (n := 6) (by decide)
  omega

variable {D : Type u} [Group D] {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
    (σ : Representation (ZMod 2) D V)

/-- The three surviving B.4.2 rows, with their full original data. -/
inductive RankOneIrreducibleCase (L H : Subgroup D) : Prop
  | linearTwo (F : BinaryField) (generated : H = L)
      (action : ActionEquiv (σ.comp L.subtype) (linearNatural F 2))
      (offenders : ∀ B, IsBestOffender σ B → ∃ S : Sylow 2 L,
        B = (S : Subgroup L).map L.subtype)
      (ratio : quadraticRatio σ = 1)
  | linearThree (F : BinaryField) (odd_degree : Odd F.degree) (generated : H = L)
      (action : ActionEquiv (σ.comp L.subtype) (linearNatural F 3))
      (ratio : quadraticRatio σ = 1 / 2)
  | symmetricFive
      (action : MarkedActionEquiv σ H L (BinaryPermutation.naturalRepresentation (Fin 5))
        (alternatingGroup (Fin 5)))
      (offenders : ∀ B, IsBestOffender σ B →
        ChapterB.Offenders.CaseAFamily 5
          ((B.subgroupOf H).map action.action.groupEquiv.toMonoidHom))
      (ratio : quadraticRatio σ = 1)

/-- Exhaust all fourteen constructors of the full B.4.2 interface. -/
theorem rankOneIrreducible_of_source [Finite D] {L H : Subgroup D}
    (hr : primeRank 3 L = 1) (c : ProjectiveLine.IrreducibleActionCase σ L H) :
    RankOneIrreducibleCase σ L H := by
  cases c with
  | linearTwo F hg e ho hq => exact .linearTwo F hg e ho hq
  | linearThree F hg e hq =>
      exact .linearThree F (linearThree_odd hr F e.groupEquiv) hg e hq
  | symplectic F _ _ e _ =>
      exact False.elim (exclude_equiv hr e.groupEquiv
        (Theory.SpecificGroups.Classical.BinaryDerivedCubicRank.symplectic.trans
          (primeRank_le_of_injective 3 (_root_.commutator _).subtype
            (_root_.commutator _).subtype_injective)))
  | symplecticTwo e _ =>
      exact False.elim (exclude_equiv hr e.subgroupEquiv
        Theory.SpecificGroups.Classical.BinaryDerivedCubicRank.symplectic)
  | g2 F _ _ e _ _ =>
      exact False.elim (exclude_equiv hr e.groupEquiv
        (Theory.SpecificGroups.Classical.BinaryDerivedCubicRank.g2.trans
          (primeRank_le_of_injective 3 (_root_.commutator _).subtype
            (_root_.commutator _).subtype_injective)))
  | g2Two e _ _ =>
      exact False.elim (exclude_equiv hr e.subgroupEquiv
        Theory.SpecificGroups.Classical.BinaryDerivedCubicRank.g2)
  | symmetric n hn e ho hq =>
      rcases hn with rfl | rfl
      · exact .symmetricFive e ho hq
      · exact False.elim (exclude_equiv hr e.subgroupEquiv
          (alternatingGroup.TwoThreeCycles.two_le_primeRank (by decide)))
  | alternatingSix _ e _ _ =>
      exact False.elim (exclude_equiv hr e.groupEquiv
        (alternatingGroup.TwoThreeCycles.two_le_primeRank (by decide)))
  | alternatingSeven _ _ e _ _ _ =>
      exact False.elim (exclude_equiv hr e
        (alternatingGroup.TwoThreeCycles.two_le_primeRank (by decide)))
  | tripleSix _ a _ =>
      exact False.elim (not_alternatingSix_central_cover_of_threeRank_one hr a.quotientEquiv)
  | binaryLinear d hd _ e _ =>
      exact False.elim (exclude_equiv hr e.groupEquiv
        (BinaryLinear.SmallCubicRank.four_or_five hd))
  | orthogonalSix _ _ e _ _ =>
      exact False.elim (exclude_equiv hr e.groupEquiv
        (alternatingGroup.TwoThreeCycles.two_le_primeRank (by decide)))
  | symmetricEight _ e _ =>
      exact False.elim (exclude_equiv hr e.subgroupEquiv
        (alternatingGroup.TwoThreeCycles.two_le_primeRank (by decide)))
  | exteriorFive _ _ e _ _ _ =>
      exact False.elim (exclude_equiv hr e BinaryLinear.SmallCubicRank.five)

/-- The remaining B.5.1(1) cases, before identifying its moved section with
the full seed or comparing the central extension of its irreducible section. -/
inductive RankOneActionCase (L : Subgroup D) (s : MovedSection σ L) : Prop
  | irreducible (irrPlus : IsIrrPlus σ L s.space.toSubmodule)
      (faithful : Function.Injective s.action)
      (irreducible : IsIrreducible (s.action.comp L.subtype))
      (source : RankOneIrreducibleCase s.action L (offenderSubgroup s.action))
      (extension : L = ⊤ ∨ (∀ T : Sylow 2 D, L ⊔ (T : Subgroup D) = ⊤) ∧
        OuterNaturalAction s.action)
  | doubleThree (F : BinaryField) (odd_degree : Odd F.degree) (whole : L = ⊤)
      (action : ActionEquiv (s.space.toRepresentation.comp L.subtype)
        (repeated (linearNatural F 3) 2))
      (offenders : ∀ B, IsBestOffender s.space.toRepresentation B ↔
        IsFullAxisGroup F 3 ((B.subgroupOf L).map action.groupEquiv.toMonoidHom))
      (ratio : quadraticRatio σ = 1)

/-- The rank hypothesis eliminates the two binary degree-four/five families
and makes the degree of the doubled natural module odd. -/
theorem rankOneAction_of_source [Finite D] {L : Subgroup D} {s : MovedSection σ L}
    (hr : primeRank 3 L = 1) (c : ProjectiveLine.QuasisimpleActionCase σ L s) :
    RankOneActionCase σ L s := by
  cases c with
  | irreducible hi hf hir c he =>
      exact .irreducible hi hf hir (rankOneIrreducible_of_source _ hr c) he
  | doubleThree F ht e ho hq =>
      exact .doubleThree F (linearThree_odd hr F e.groupEquiv) ht e ho hq
  | naturalDual d hd _ he =>
      obtain ⟨e⟩ := he
      exact False.elim (exclude_equiv hr e.groupEquiv
        (BinaryLinear.SmallCubicRank.four_or_five hd))
  | repeatedNatural d r hd _ _ _ he =>
      obtain ⟨e⟩ := he
      exact False.elim (exclude_equiv hr e.groupEquiv
        (BinaryLinear.SmallCubicRank.four_or_five hd))

variable {G : Type u} [Group G] [Finite G]
    (ρ : Representation (ZMod 2) G V)

/-- Faithfulness on U identifies L with its *literal* image in LA/C_LA(U). -/
noncomputable def seedComponentEquiv {K : GroupClass.{u}} {A L : Subgroup G}
    (hLA : ⁅L,A⁆ = L) (p : Prepared ρ K hLA) : L ≃* seedComponentImage ρ hLA :=
  seedSubgroupEquiv ρ hLA L le_sup_left p.component_faithful

/-- Actual application to the prepared B.5.9 seed and the complete B.5.1
conclusion. It needs no reduced model-list premise. -/
theorem seed_rankOneAction_of_source {K : GroupClass.{u}} {A L : Subgroup G}
    (hLA : ⁅L,A⁆ = L) (p : Prepared ρ K hLA) (hr : primeRank 3 L = 1)
    (c : ProjectiveLine.QuasisimpleSourceConclusion
      (seedQuotientAction ρ hLA) (seedComponentImage ρ hLA)) :
    RankOneActionCase (seedQuotientAction ρ hLA) (seedComponentImage ρ hLA) c.sectionData := by
  have hi : primeRank 3 (seedComponentImage ρ hLA) = 1 :=
    (primeRank_equiv 3 (seedComponentEquiv ρ hLA p)).symm.trans hr
  exact rankOneAction_of_source _ hi c.clause_one

end CFSG.Quasithin.ChapterB.SourceInduction.ComponentReduction.PreliminaryActions
