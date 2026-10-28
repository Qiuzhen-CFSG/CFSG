module
public import CFSG.Quasithin.Chapter16.Section03.FourGroupTransfer.ExceptionalAction.CentralizerCalculation.Bounds
public import Theory.GroupTheory.PerfectSubgroupAutomorphismFixer
public import Mathlib.GroupTheory.SpecificGroups.KleinFour
/-!
# From the faithful action to the full-centralizer problem

The inner action of L is identified with conjugation by L viewed inside I.
Perfectness then identifies its automorphism centralizer with the pointwise
fixer. The ambient faithful action of E embeds into that fixer, providing
the lower cardinality bound. A model upper bound and the square identities
recognize the fixer as E₄, without presupposing the structure of E.

Source: Aschbacher–Smith 16.3.5, printed pp.1178–1179, combined manuscript
of 1 March 2004. The intrinsic model bounds remain separate obligations.
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter16.FourGroupTransfer.ExceptionalAction.CentralizerCalculation
open Subgroup Theory.GroupTheory

variable {G : Type*} [Group G]
/-- The ambient action of L is its inner action in the actual enlargement. -/
theorem inducedAction_range_eq_inner {L I : Subgroup G} (hLI : L ≤ I) :
    (inducedAction L I (hLI.trans I.le_normalizer)).range =
      (L.subgroupOf I).map (MulAut.conj : I →* MulAut I) := by
  ext a
  constructor
  · rintro ⟨l, rfl⟩
    refine ⟨⟨l, hLI l.property⟩, l.property, ?_⟩
    ext x
    rfl
  · rintro ⟨l, hl, rfl⟩
    refine ⟨⟨l, hl⟩, ?_⟩
    ext x
    rfl

/-- The full automorphism centralizer equals the embedded pointwise fixer. -/
theorem action_centralizer_eq_pairFixer {L I : Subgroup G}
    [Group.IsPerfect L] (hLI : L ≤ I) :
    centralizer ((inducedAction L I (hLI.trans I.le_normalizer)).range : Set (MulAut I)) =
      pairFixer L I := by
  let : Group.IsPerfect (L.subgroupOf I) :=
    Group.IsPerfect.ofSurjective (f := (subgroupOfEquivOfLe hLI).symm.toMonoidHom)
      (subgroupOfEquivOfLe hLI).symm.surjective
  rw [inducedAction_range_eq_inner hLI]
  exact PerfectSubgroupAutomorphismFixer.inner_centralizer_eq_fixer _

/-- A faithful centralizing actor embeds in the pointwise fixer. -/
theorem card_le_pairFixer [Finite G] {E L I : Subgroup G}
    (hn : E ≤ normalizer (I : Set G)) (hc : E ≤ centralizer (L : Set G))
    (hf : Function.Injective (inducedAction E I hn)) :
    Nat.card E ≤ Nat.card (pairFixer L I) := by
  let f : E → pairFixer L I := fun e => ⟨inducedAction E I hn e, by
    rw [pairFixer, mem_fixingSubgroup_iff]
    intro l hl
    apply Subtype.ext
    change (e : G) * (l : G) * (e : G)⁻¹ = (l : G)
    rw [← mem_centralizer_iff.mp (hc e.property) l hl]
    group⟩
  exact Nat.card_le_card_of_injective f (fun a b hab => hf (congrArg Subtype.val hab))

private theorem exponent_two_of_square {A : Type*} [Group A] [Nontrivial A]
    (h : ∀ a : A, a ^ 2 = 1) : Monoid.exponent A = 2 := by
  have hd := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr h
  rcases (Nat.dvd_prime Nat.prime_two).mp hd with he | he
  · have hs : Subsingleton A := Monoid.exp_eq_one_iff.mp he
    exact False.elim (not_subsingleton A hs)
  · exact he

/-- The lower order bound and intrinsic square calculation give an actual E₄ isomorphism. -/
theorem FourBound.nonempty_equiv [Finite G] {L I : Subgroup G} (h : FourBound L I)
    (hl : 4 ≤ Nat.card (pairFixer L I)) :
    Nonempty (pairFixer L I ≃* (Fin 2 → Multiplicative (ZMod 2))) := by
  have hc : Nat.card (pairFixer L I) = 4 := le_antisymm h.card_le hl
  let : Nontrivial (pairFixer L I) := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  let : IsKleinFour (pairFixer L I) := ⟨hc, exponent_two_of_square h.square⟩
  let : IsKleinFour (Fin 2 → Multiplicative (ZMod 2)) :=
    ⟨by simp [Nat.card_eq_fintype_card], exponent_two_of_square (by decide)⟩
  exact IsKleinFour.nonempty_mulEquiv
end CFSG.Quasithin.Chapter16.FourGroupTransfer.ExceptionalAction.CentralizerCalculation
