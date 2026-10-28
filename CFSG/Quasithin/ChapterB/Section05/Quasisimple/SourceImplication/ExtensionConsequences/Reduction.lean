module
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceImplication.ExtensionConsequences.BinaryThree

/-!
# Reduction of the extension clauses to the irreducible action

Every reducible alternative in B.5.1(1) gives the actual direct sum
V = [V,L] ⊕ C_V(G), and has G = L. Thus the hypotheses of clauses (2), (4),
and (5) each select the full irreducible alternative, with its action marking
and outer-extension data retained. The separate binary-three consumer proves
the literal fixed-kernel clause once G = L has been established.

These are deductions from the action alternatives, not assumptions of the
requested extension conclusions. No earlier-source parameter remains in
these reductions. The irreducible cohomology sieve and the exceptional action
on C_V(L) still have to be supplied for the complete clauses (2), (4), and (5).

Source: Aschbacher–Smith, combined manuscript (1 March 2004), B.5.1,
printed pp.99 and 102–103.
-/

@[expose] public section
open Subgroup Representation Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterB.QuasisimpleSource.ExtensionConsequences
universe u v
variable {G : Type u} [Group G] {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
  {ρ : Representation (ZMod 2) G V}

/-- The full irreducible alternative, retaining the actual B.4.2 action and
outer extension data. It is extracted from the proved action alternative,
never assumed to describe an arbitrary module. -/
structure IrreducibleAlternative (L : Subgroup G) (s : MovedSection ρ L) : Prop where
  irrPlus : IsIrrPlus ρ L s.space.toSubmodule
  faithful : Function.Injective s.action
  irreducible : IsIrreducible (s.action.comp L.subtype)
  source : IrreducibleActionCase s.action L (offenderSubgroup s.action)
  extension : L = ⊤ ∨ (∀ T : Sylow 2 G, L ⊔ (T : Subgroup G) = ⊤) ∧
    OuterNaturalAction s.action

/-- All three reducible alternatives split over the whole-group fixed space.
This is the common reduction for clauses (2), (4), and (5). -/
theorem irreducible_or_split [Finite G] {K : CFSG.Quasithin.GroupClass.{u}}
    {L : Subgroup G} (h : QuasisimpleSourceHypothesis ρ K L)
    (s : MovedSection ρ L) (hc : QuasisimpleActionCase ρ L s) :
    IrreducibleAlternative L s ∨ (L = ⊤ ∧ IsCompl s.space.toSubmodule ρ.invariants) := by
  let := h.finite_module
  cases hc with
  | irreducible hi hf hirr hs he => exact Or.inl ⟨hi, hf, hirr, hs, he⟩
  | doubleThree F hL e _ _ =>
    exact Or.inr ⟨hL, doubleThree_isCompl s F hL (source_isFF h) e⟩
  | naturalDual d hd hL hn =>
    exact Or.inr ⟨hL, naturalDual_isCompl s (by rcases hd with rfl | rfl <;> decide) hL hn⟩
  | repeatedNatural d r hd _ _ hL hn =>
    exact Or.inr ⟨hL, repeated_binary_isCompl s (by rcases hd with rfl | rfl <;> decide) hL hn⟩

/-- Nonsplitting over C_V(L) forces the full irreducible alternative. -/
theorem irreducible_of_not_compl_fixed [Finite G] {K : CFSG.Quasithin.GroupClass.{u}}
    {L : Subgroup G} (h : QuasisimpleSourceHypothesis ρ K L)
    (s : MovedSection ρ L) (hc : QuasisimpleActionCase ρ L s)
    (hn : ¬ IsCompl s.space.toSubmodule (fixedSpace ρ L)) : IrreducibleAlternative L s := by
  rcases irreducible_or_split h s hc with hi | ⟨hL, hs⟩
  · exact hi
  · subst L
    rw [fixedSpace_top] at hn
    exact False.elim (hn hs)

/-- Failure of the whole-group direct sum forces the full irreducible case. -/
theorem irreducible_of_not_compl_invariants [Finite G]
    {K : CFSG.Quasithin.GroupClass.{u}} {L : Subgroup G}
    (h : QuasisimpleSourceHypothesis ρ K L)
    (s : MovedSection ρ L) (hc : QuasisimpleActionCase ρ L s)
    (hn : ¬ IsCompl s.space.toSubmodule ρ.invariants) : IrreducibleAlternative L s := by
  rcases irreducible_or_split h s hc with hi | ⟨_, hs⟩
  · exact hi
  · exact False.elim (hn hs)

/-- Failure of the supplement in clause (5) is sufficient for the reduction;
no hyperplane hypothesis is introduced. -/
theorem irreducible_of_no_supplement [Finite G]
    {K : CFSG.Quasithin.GroupClass.{u}} {L : Subgroup G}
    (h : QuasisimpleSourceHypothesis ρ K L)
    (s : MovedSection ρ L) (hc : QuasisimpleActionCase ρ L s)
    (hn : s.space.toSubmodule ⊔ ρ.invariants ≠ ⊤) : IrreducibleAlternative L s :=
  irreducible_of_not_compl_invariants h s hc
    (fun hs => hn (codisjoint_iff.mp hs.codisjoint))

/-- The literal fixed-kernel conclusion for L₃(2), after the source argument
has established G = L. The SL/PSL comparison is the actual quotient map. -/
theorem linearThree_fixed_kernel [Finite G]
    {K : CFSG.Quasithin.GroupClass.{u}} {L : Subgroup G}
    (h : QuasisimpleSourceHypothesis ρ K L) (s : MovedSection ρ L) (hL : L = ⊤)
    (he : Nonempty (L ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 3) (ZMod 2)))
    (hn : s.space.toSubmodule ⊔ ρ.invariants ≠ ⊤) :
    s.space.toSubmodule ⊓ fixedSpace ρ L = ⊥ := by
  let := h.finite_module
  subst L
  obtain ⟨e⟩ := he
  let E := Subgroup.topEquiv.symm.trans (e.trans Matrix.PSL3Two.equiv.symm)
  rw [fixedSpace_top]
  exact binary_fixed_kernel_of_no_supplement s E h.faithful (source_isFF h) hn

end CFSG.Quasithin.ChapterB.QuasisimpleSource.ExtensionConsequences
