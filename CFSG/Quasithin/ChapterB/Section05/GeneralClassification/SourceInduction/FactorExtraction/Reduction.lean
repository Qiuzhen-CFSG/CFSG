module
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.FactorExtraction.Rows

/-!
# Reducing full rank-one extraction to the binary upper extension

The exhaustive rank-one comparison retains three irreducible rows and the
doubled row. The proved row extractions settle SL₂, S₅ and doubled SL₃. For
natural SL₃ of odd field degree, comparison of the actual binary dimensions
excludes every outer row in B.5.1(1i), proving that the component is the whole
actor. If a fixed supplement fails, the established cohomology calculation
forces degree one and B.5.1(5) removes the central kernel of the moved space.

The final alternative is an actual natural moved SL₃(2)-module without a
fixed supplement. It remains to construct its four-dimensional fixed quotient
and invoke the complete earlier B.4.8(3) implication. This reduction assumes
neither that extension nor the desired extraction conclusion.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, B.5.1(1),(5),
B.5.8 and B.5.11(2), printed pp.99–109; I.1.6(4), p.408.
-/

@[expose] public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
namespace CFSG.Quasithin.ChapterB.SourceInduction.FactorExtraction
open QuasisimpleSource QuasisimpleSource.ExtensionConsequences
open ComponentReduction.PreliminaryActions
universe u v
variable {D : Type u} [Group D] {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
    {ρ : Representation (ZMod 2) D V}

private theorem binary_field_finrank (F : BinaryField) :
    Module.finrank (ZMod 2) F.Carrier = F.degree := by
  apply Nat.pow_right_injective (by decide : 2 ≤ 2)
  calc
    2 ^ Module.finrank (ZMod 2) F.Carrier = Nat.card F.Carrier := by
      simpa using (Module.natCard_eq_pow_finrank (K := ZMod 2) (V := F.Carrier)).symm
    _ = _ := F.card_eq

/-- The odd-degree natural SL₃ row cannot be any of the retained outer natural
extensions: its binary dimension is three times an odd number, rather than
four or six. This uses the full source module identifications. -/
theorem linearThree_whole_of_odd {L : Subgroup D} (s : MovedSection ρ L)
    (F : BinaryField) (ho : Odd F.degree)
    (e : ActionEquiv (s.action.comp L.subtype) (linearNatural F 3))
    (hext : L = ⊤ ∨ (∀ T : Sylow 2 D, L ⊔ (T : Subgroup D) = ⊤) ∧
      OuterNaturalAction s.action) : L = ⊤ := by
  rcases hext with ht | ⟨_, hext⟩
  · exact ht
  exfalso
  have hd : Module.finrank (ZMod 2) (s.space.toSubmodule ⧸ s.central.toSubmodule) =
      3 * F.degree := by
    rw [e.linearEquiv.finrank_eq, Module.finrank_pi_fintype]
    simp [binary_field_finrank]
  obtain ⟨k, hk⟩ := ho
  rcases hext with ⟨n, hn, hN, ⟨a⟩⟩ | ⟨a⟩
  · have ha := a.linearEquiv.finrank_eq
    rw [hd] at ha
    have hm : Module.finrank (ZMod 2) (BinaryPermutation.natural (Fin n)) =
        if n = 5 ∨ n = 6 then 4 else 6 := by
      interval_cases n <;>
        first
        | simpa using BinaryPermutation.finrank_natural_odd (Fin _) (by decide)
        | simpa using BinaryPermutation.finrank_natural_even (Fin _) (by decide)
    rw [hm] at ha
    split_ifs at ha <;> omega
  · obtain ⟨a⟩ := a
    have ha := a.linearEquiv.finrank_eq
    rw [hd, Atlas.G2.Natural.finrank_space] at ha
    omega

/-- With no central kernel, the actual moved space carries the given natural
module, using the same group identification as its quotient. -/
noncomputable def movedActionOfCentralBot {L : Subgroup D} (s : MovedSection ρ L)
    (hc : s.space.toSubmodule ⊓ fixedSpace ρ L = ⊥) :
    ActionEquiv (s.space.toRepresentation.comp L.subtype) (s.action.comp L.subtype) := by
  have hz : s.central.toSubmodule = ⊥ := by
    apply bot_unique
    intro v hv
    rw [s.central_eq] at hv
    apply Subtype.ext
    have h : (v : V) ∈ s.space.toSubmodule ⊓ fixedSpace ρ L :=
      ⟨v.property, fun g => congrArg Subtype.val (hv g)⟩
    exact hc.le h
  let q := s.central.toSubmodule.quotEquivOfEqBot hz
  refine ⟨MulEquiv.refl L, q.symm, ?_⟩
  intro g v
  apply q.injective
  rw [LinearEquiv.apply_symm_apply]
  have h (w : s.space.toSubmodule ⧸ s.central.toSubmodule) :
      q ((MovedSection.action ρ s) g w) = s.space.toRepresentation g (q w) := by
    induction w using Submodule.Quotient.induction_on with | _ w => rfl
  change s.space.toRepresentation g v = q ((MovedSection.action ρ s) g (q.symm v))
  rw [h, q.apply_symm_apply]

/-- The sole nonsupplemented row is an actual binary natural moved module.
The full B.5.1(5) clause supplies its zero central kernel. No statement about
the remaining quotient extension is assumed. -/
theorem linearThree_binary_of_no_supplement [Finite D] [Module.Finite (ZMod 2) V]
    {L : Subgroup D} (c : ProjectiveLine.QuasisimpleSourceConclusion ρ L)
    (hi : IsIrrPlus ρ L c.sectionData.space.toSubmodule)
    (F : BinaryField) (ho : Odd F.degree)
    (e : ActionEquiv (c.sectionData.action.comp L.subtype) (linearNatural F 3))
    (hext : L = ⊤ ∨ (∀ T : Sylow 2 D, L ⊔ (T : Subgroup D) = ⊤) ∧
      OuterNaturalAction c.sectionData.action)
    (hs : c.sectionData.space.toSubmodule ⊔ ρ.invariants ≠ ⊤) :
    ∃ s : MovedSection ρ ⊤,
      IsLinearNatural (s.space.toRepresentation.comp (⊤ : Subgroup D).subtype)
        BinaryField.two 3 ∧ s.space.toSubmodule ⊔ ρ.invariants ≠ ⊤ := by
  have ht := linearThree_whole_of_odd c.sectionData F ho e hext
  subst L
  have hF : F.degree = 1 := by
    have hpos := F.degree_pos
    by_contra hn
    have hc := linearThree_large_isCompl c.sectionData hi F (by omega) e
    apply hs
    simpa only [fixedSpace_top] using hc.sup_eq_top
  let q := degreeOneNaturalEquiv F hF 3
  let a := transAction e q
  have hz : c.sectionData.space.toSubmodule ⊓ fixedSpace ρ ⊤ = ⊥ :=
    (c.clause_five.resolve_left hs).2.2
      ⟨a.groupEquiv.trans Matrix.PSL3Two.equiv⟩
  exact ⟨c.sectionData, ⟨transAction (movedActionOfCentralBot c.sectionData hz) a⟩, hs⟩

/-- Exhaustive reduction of the classified quasisimple action. The remaining
branch specifies a natural moved module with a genuine missing supplement;
it does not assume the desired four-dimensional extension. -/
theorem quasisimple_factor_or_binary [Finite D] [Nontrivial D] [Module.Finite (ZMod 2) V]
    (c : ProjectiveLine.QuasisimpleSourceConclusion ρ (generalizedFitting D))
    (hj : offenderSubgroup ρ = ⊤) (hr : primeRank 3 D ≤ 1) :
    Nonempty (FactorModuleConclusion ρ) ∨
      ∃ s : MovedSection ρ ⊤,
        IsLinearNatural (s.space.toRepresentation.comp (⊤ : Subgroup D).subtype)
          BinaryField.two 3 ∧ s.space.toSubmodule ⊔ ρ.invariants ≠ ⊤ := by
  cases c.rank_one_action hr with
  | doubleThree F ho ht e _ _ =>
      exact Or.inl (doubleThree_factor_module c.sectionData F ho ht (ff_of_generated hj) e)
  | irreducible hi hf hir hrow hext =>
      cases hrow with
      | linearTwo F hg e hoff hq =>
          exact Or.inl (linearTwo_factor_module c.sectionData F hj hg e hoff hq)
      | symmetricFive e _ hq =>
          exact Or.inl (symmetricFive_factor_module c.sectionData hi hj e hq)
      | linearThree F ho _ e _ =>
          by_cases hs : c.sectionData.space.toSubmodule ⊔ ρ.invariants = ⊤
          · exact Or.inl (linearThree_supplement_factor_module c.sectionData F ho
              (linearThree_whole_of_odd c.sectionData F ho e hext) e hs)
          · exact Or.inr (linearThree_binary_of_no_supplement c hi F ho e hext hs)

/-- Actual application to an established smaller classification, without
assuming a universal B.5.6 theorem or dropping any surviving source row. -/
theorem classified_factor_or_binary [Finite D] [Nontrivial D]
    {K : GroupClass.{u}} (hyp : FFHypothesis K ρ) (hr : primeRank 3 D ≤ 1)
    (h : AdequateAlternative ρ) :
    Nonempty (FactorModuleConclusion ρ) ∨
      ∃ s : MovedSection ρ ⊤,
        IsLinearNatural (s.space.toRepresentation.comp (⊤ : Subgroup D).subtype)
          BinaryField.two 3 ∧ s.space.toSubmodule ⊔ ρ.invariants ≠ ⊤ := by
  let := hyp.finite_module
  rcases h.at_three_rank_le_one hr with ⟨_, ⟨c⟩⟩ | ⟨c⟩
  · exact quasisimple_factor_or_binary c hyp.generated hr
  · exact Or.inl ((Classical.choice c).factor_module ρ hyp.faithful)
end CFSG.Quasithin.ChapterB.SourceInduction.FactorExtraction
