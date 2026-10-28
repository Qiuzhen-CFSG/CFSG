module
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceCompletion.AlternatingSevenActor
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceImplication.ExtensionConsequences.IrreducibleCohomology.CohomologyReduction

public import Theory.Representation.FactorDegreeFiltration.FiniteDual

/-!
# The full natural moved module of an A7 FF component

The corrected B.5.1 catalogue leaves the natural six-space or the exceptional
four-space. Vanishing of H1 and dual H1 splits the actual moved space from
the component fixed space in either case. A contained subgroup of order
larger than sixteen excludes the four-space. The quotient coordinates then
lift to an action equivalence on the whole original moved space.

The nonsingular Section12.6 consumer supplies its actual subgroup V_v of
order32; the canonical FF witness remains with that source assembly.
Source: Aschbacher--Smith B.5.1 and I.1.6, printed pp.99--103 and408,
applied in12.6.18, p.827, combined manuscript of 1 March 2004.
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterB.QuasisimpleSource.SourceCompletion.AlternatingSevenActor
open ExtensionConsequences

private theorem no_higher_linear {C : Type*} [Group C]
    (e : C ≃* alternatingGroup (Fin 7)) {d : ℕ} (hd : d = 4 ∨ d = 5)
    (a : C ≃* SL(d,ZMod 2)) : False := by
  have hc : Nat.card SL(d,ZMod 2) = 2520 := by
    rw [←Nat.card_congr a.toEquiv,Nat.card_congr e.toEquiv,nat_card_alternatingGroup]
    norm_num [Nat.factorial]
  rw [Nat.card_congr (BinaryLinear.OuterCyclic.slEquivLinear d).toEquiv,
    ←Nat.card_congr (BinaryLinear.OuterCyclic.matrixEquivLinear d).toEquiv,
    Matrix.card_GL_field] at hc
  rcases hd with rfl | rfl <;> norm_num [Fin.prod_univ_succ] at hc

private theorem no_three {C : Type*} [Group C]
    (e : C ≃* alternatingGroup (Fin 7)) (F : BinaryField)
    (a : C ≃* SL(3,F.Carrier)) : False := by
  have hc : Nat.card SL(3,F.Carrier) = 2520 := by
    rw [←Nat.card_congr a.toEquiv,Nat.card_congr e.toEquiv,nat_card_alternatingGroup]
    norm_num [Nat.factorial]
  have hd := (Matrix.PSL3.LinearThree.unipotentSL F.Carrier).card_subgroup_dvd_card
  rw [Matrix.PSL3.LinearThree.card_unipotentSL,F.card_eq,←pow_mul,hc] at hd
  have hn : F.degree = 1 := by
    have hp := F.degree_pos
    by_contra h
    have hdiv : 16 ∣ 2520 := (pow_dvd_pow 2 (by omega : 4 ≤ F.degree * 3)).trans hd
    norm_num at hdiv
  rw [Matrix.PSL3.LinearThree.DefiningSylow.card_specialLinear,F.card_eq,hn] at hc
  norm_num at hc

variable {G V : Type*} [Group G] [Finite G] [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V] {ρ : Representation (ZMod 2) G V} {C : Subgroup G}

omit [Finite G] [FiniteDimensional (ZMod 2) V] in
private theorem central_bot (s : MovedSection ρ C)
    (hs : IsCompl s.space.toSubmodule (fixedSpace ρ C)) : s.central.toSubmodule = ⊥ := by
  rw [s.central_eq]
  apply bot_unique
  intro x hx
  apply Subtype.ext
  exact (disjoint_iff.mp hs.disjoint).le ⟨x.property,fun g => congrArg Subtype.val (hx g)⟩

private theorem four_vanishing {D X : Type*} [Group D] [AddCommGroup X]
    [Module (ZMod 2) X] [FiniteDimensional (ZMod 2) X]
    (σ : Representation (ZMod 2) D X) [IsIrreducible σ]
    (e : D ≃* alternatingGroup (Fin 7)) (hd : Module.finrank (ZMod 2) X = 4) :
    Subsingleton (OneCohomology.H1 σ) := by
  let τ := σ.comp e.symm.toMonoidHom
  let : IsIrreducible τ := (irreducible_comp_surjective_iff _ e.symm.surjective σ).mpr inferInstance
  let : Subsingleton (OneCohomology.H1 τ) :=
    (Module.finrank_zero_iff (R := ZMod 2)).mp
      (binaryAlternatingSeven_finrank_H1_eq_zero_of_irreducible_four τ hd)
  let a : ActionEquiv σ τ := ⟨e,LinearEquiv.refl _ _,fun g x => by
    change σ g x = σ (e.symm (e g)) x
    rw [e.symm_apply_apply]⟩
  exact a.H1_subsingleton

private theorem four_split (s : MovedSection ρ C)
    (hi : IsIrrPlus ρ C s.space.toSubmodule)
    (hirr : IsIrreducible (s.action.comp C.subtype))
    (e : C ≃* alternatingGroup (Fin 7))
    (hd : Module.finrank (ZMod 2) (s.space.toSubmodule ⧸ s.central.toSubmodule) = 4) :
    IsCompl s.space.toSubmodule (fixedSpace ρ C) := by
  let := hirr
  let := four_vanishing (s.action.comp C.subtype) e hd
  let : IsIrreducible (Representation.dual (s.action.comp C.subtype)) := Representation.isIrreducible_dual
  let := four_vanishing (Representation.dual (s.action.comp C.subtype)) e (by rw [Subspace.dual_finrank_eq]; exact hd)
  exact moved_isCompl_of_cohomology s hi

/-- An A7 component with a moved subgroup of order greater than sixteen has
its entire moved module natural, and this module complements the fixed space. -/
theorem natural_moved_of_card_gt_sixteen
    (c : ChapterB.SourceInduction.ProjectiveLine.QuasisimpleSourceConclusion ρ C) (e : C ≃* alternatingGroup (Fin 7))
    (hcard : 16 < Nat.card c.sectionData.space.toSubmodule) :
    IsCompl c.sectionData.space.toSubmodule (fixedSpace ρ C) ∧
      IsAlternatingNatural (c.sectionData.space.toRepresentation.comp C.subtype) 7 := by
  let s := c.sectionData
  cases c.clause_one with
  | irreducible hi hf hirr hs he =>
    rcases natural_or_four s.action hs e with hn | hd
    · obtain ⟨a⟩ := hn
      let σ : Representation (ZMod 2) (alternatingGroup (Fin 7)) (BinaryPermutation.natural (Fin 7)) := alternatingNatural 7
      let : Subsingleton (OneCohomology.H1 σ) := by
        apply (Module.finrank_zero_iff (R := ZMod 2)).mp
        exact BinaryPermutation.alternatingSeven_natural_finrank_H1
      let sd : ActionEquiv σ σ.dual := ⟨MulEquiv.refl _,BinaryPermutation.naturalDualEquiv (Fin 7),
        fun g v => BinaryPermutation.naturalDualEquiv_equivariant (Fin 7) g.val v⟩
      let : Subsingleton (OneCohomology.H1 σ.dual) := (actionSymm sd).H1_subsingleton
      have hsplit := moved_isCompl_of_equiv s hi a
      have hz := central_bot s hsplit
      let p := (s.central.toSubmodule.quotEquivOfEqBot hz).symm
      refine ⟨hsplit,⟨⟨a.groupEquiv,p.trans a.linearEquiv,?_⟩⟩⟩
      intro g x
      exact a.intertwines g (Submodule.Quotient.mk x)
    · have hsplit := four_split s hi hirr e hd
      have hz := central_bot s hsplit
      have hc : Nat.card s.space.toSubmodule = 16 := by
        rw [←Nat.card_congr (s.central.toSubmodule.quotEquivOfEqBot hz).toEquiv,
          Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod,hd]
        rfl
      change 16 < Nat.card s.space.toSubmodule at hcard
      omega
  | doubleThree F _ a _ _ => exact (no_three e F a.groupEquiv).elim
  | naturalDual d hd _ hn =>
    obtain ⟨a⟩ := hn
    exact (no_higher_linear e hd a.groupEquiv).elim
  | repeatedNatural d r hd _ _ _ hn =>
    obtain ⟨a⟩ := hn
    exact (no_higher_linear e hd a.groupEquiv).elim
end CFSG.Quasithin.ChapterB.QuasisimpleSource.SourceCompletion.AlternatingSevenActor
