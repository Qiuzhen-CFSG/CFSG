module
public import Theory.GroupAction.Invariant
public import Mathlib.GroupTheory.PGroup

/-!
# Order-thirty-one automorphisms on a group of order thirty-two

An automorphism subgroup A of order thirty-one acts irreducibly on any group
E of order thirty-two: every subgroup preserved by A is trivial or full.
The action is the canonical evaluation action of the actual automorphisms.
No elementary-abelian hypothesis is required.

The A-fixed subgroup has cardinal congruent to one modulo thirty-one and
cardinal at most thirty-two. Its only possibilities are therefore one and
thirty-two. Faithful evaluation excludes the latter, since A is nontrivial.
The action on any invariant subgroup still has only the identity fixed, and
the same cardinal congruence leaves only the trivial and full subgroups.

This elementary orbit-counting fact supplies the irreducibility used in the
solvable automorphism-group reduction for Parrott, "A Characterization of
the Tits' Simple Group", Canadian Journal of Mathematics 24 (1972), Lemma 2,
printed p.673, independently of the surrounding recognition hypotheses.
-/

public theorem irreducible_of_card_thirtyone
    {E : Type*} [Group E] [Finite E] (hE : Nat.card E = 32)
    (A : Subgroup (MulAut E)) (hA : Nat.card A = 31) :
    ∀ D : Subgroup E, (∀ a : A, ∀ x : E, x ∈ D → a • x ∈ D) →
      D = ⊥ ∨ D = ⊤ := by
  let : Fact (Nat.Prime 31) := ⟨by decide⟩
  have hp : IsPGroup 31 A := IsPGroup.of_card (n := 1) (by simpa using hA)
  have hfixed : FixedPoints.subgroup A E = ⊥ := by
    have hmod := hp.card_modEq_card_fixedPoints E
    change Nat.ModEq 31 (Nat.card E) (Nat.card (FixedPoints.subgroup A E)) at hmod
    have hbound := Subgroup.card_le_card_group (H := FixedPoints.subgroup A E)
    have hpos : 0 < Nat.card (FixedPoints.subgroup A E) := Nat.card_pos
    rw [hE] at hmod hbound
    change 1 = Nat.card (FixedPoints.subgroup A E) % 31 at hmod
    have hcases : Nat.card (FixedPoints.subgroup A E) = 1 ∨
        Nat.card (FixedPoints.subgroup A E) = 32 := by omega
    rcases hcases with h | h
    · exact Subgroup.card_eq_one.mp h
    · have htop : FixedPoints.subgroup A E = ⊤ :=
        Subgroup.eq_top_of_card_eq _ (h.trans hE.symm)
      have hbot : A = ⊥ := by
        apply bot_unique
        intro a ha
        apply Subgroup.mem_bot.mpr
        apply MulEquiv.ext
        intro x
        have hx : x ∈ FixedPoints.subgroup A E := by rw [htop]; trivial
        exact hx ⟨a, ha⟩
      simp [hbot] at hA
  intro D hD
  let : IsInvariant A E D := ⟨by
    intro a x
    constructor
    · exact hD a x
    · intro hx
      simpa only [inv_smul_smul] using hD a⁻¹ (a • x) hx⟩
  have hfixedD : FixedPoints.subgroup A D = ⊥ := by
    apply bot_unique
    intro x hx
    apply Subtype.ext
    apply hfixed.le
    intro a
    exact congrArg Subtype.val (hx a)
  have hmod := hp.card_modEq_card_fixedPoints D
  change Nat.ModEq 31 (Nat.card D) (Nat.card (FixedPoints.subgroup A D)) at hmod
  rw [hfixedD, Subgroup.card_bot] at hmod
  have hbound := Subgroup.card_le_card_group (H := D)
  have hpos : 0 < Nat.card D := Nat.card_pos
  rw [hE] at hbound
  have hcases : Nat.card D = 1 ∨ Nat.card D = 32 := by
    change Nat.card D % 31 = 1 at hmod
    omega
  exact hcases.elim (fun h => Or.inl (Subgroup.card_eq_one.mp h))
    (fun h => Or.inr (Subgroup.eq_top_of_card_eq D (h.trans hE.symm)))
