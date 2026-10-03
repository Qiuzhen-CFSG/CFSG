module

public import Theory.GroupAction.Lemmas
public import Mathlib.Algebra.Group.Subgroup.Finite
public import Mathlib.GroupTheory.PGroup
public import Mathlib.Tactic

/-!
# Intrinsic fixed-support transport

Order-three actor lines have fixed subgroups of order one or four in a
faithful action on a group of order sixteen. Conjugating an actor line
transports its fixed subgroup by the given action. Thus a normal actor
subgroup preserves the collection of intrinsic order-four fixed supports;
if that collection consists of two distinct subgroups, it permutes them.

This module does not construct that two-element collection. Its construction
is the separate elementary-nine support-counting step in Stellmacher (9.1)(8).
-/

@[expose] public section

namespace Stellmacher.SectionOne

theorem nineCoreSupportDecomposition_line_fixed_card
    {K V : Type*} [Group K] [Group V] [Finite V] [MulDistribMulAction K V]
    (line : Subgroup K) (hlinecard : Nat.card line = 3) (hVcard : Nat.card V = 16)
    (hfaith : fixingSubgroup K (Set.univ : Set V) = ⊥) :
    Nat.card (FixedPoints.subgroup line V) = 1 ∨
      Nat.card (FixedPoints.subgroup line V) = 4 := by
  let : Finite line := Nat.finite_of_card_ne_zero (by omega)
  let : Fact (Nat.Prime 3) := ⟨by decide⟩
  have hnotop : FixedPoints.subgroup line V ≠ ⊤ := by
    intro htop
    have hbot : line = ⊥ := by
      apply le_antisymm ?_ bot_le
      intro actor hactor
      have hfix : actor ∈ fixingSubgroup K (Set.univ : Set V) := by
        rw [mem_fixingSubgroup_iff]
        intro value _
        have hvalue : value ∈ FixedPoints.subgroup line V := htop ▸ Subgroup.mem_top value
        exact hvalue (⟨actor, hactor⟩ : line)
      simpa [hfaith] using hfix
    simp [hbot] at hlinecard
  have hpgroup : IsPGroup 3 line :=
    IsPGroup.of_card (p := 3) (n := 1) (by simpa using hlinecard)
  have hmod := hpgroup.card_modEq_card_fixedPoints V
  change Nat.ModEq 3 (Nat.card V) (Nat.card (FixedPoints.subgroup line V)) at hmod
  have hdvd : Nat.card (FixedPoints.subgroup line V) ∣ 2 ^ 4 := by
    simpa [hVcard] using (FixedPoints.subgroup line V).card_subgroup_dvd_card
  obtain ⟨exponent, hbound, hpower⟩ :=
    (Nat.dvd_prime_pow (by decide : Nat.Prime 2)).mp hdvd
  interval_cases exponent
  · exact Or.inl (by simpa using hpower)
  · rw [hpower, hVcard] at hmod
    norm_num [Nat.ModEq] at hmod
  · exact Or.inr (by simpa using hpower)
  · rw [hpower, hVcard] at hmod
    norm_num [Nat.ModEq] at hmod
  · exact (hnotop (Subgroup.eq_top_of_card_eq _ (by simpa [hVcard] using hpower))).elim

theorem nineCoreSupportDecomposition_map_fixedPoints
    {K V : Type*} [Group K] [Group V] [MulDistribMulAction K V]
    (line : Subgroup K) (element : K) :
    (FixedPoints.subgroup line V).map
        (MulDistribMulAction.toMulAut K V element).toMonoidHom =
      FixedPoints.subgroup (line.map (MulAut.conj element).toMonoidHom) V := by
  ext value
  constructor
  · rintro ⟨original, horiginal, rfl⟩ actor
    obtain ⟨source, hsource, hactor⟩ := actor.property
    have hfix := horiginal (⟨source, hsource⟩ : line)
    change (actor : K) • (element • original) = element • original
    rw [← hactor]
    simpa [MulAut.conj_apply, ← mul_smul, mul_assoc] using
      congrArg (fun point : V => element • point) hfix
  · intro hvalue
    refine Subgroup.mem_map.mpr ⟨element⁻¹ • value, ?_, by simp⟩
    intro actor
    have hfix := hvalue
      (⟨(MulAut.conj element) actor,
        Subgroup.mem_map.mpr ⟨actor, actor.property, rfl⟩⟩ :
          line.map (MulAut.conj element).toMonoidHom)
    change (element * (actor : K) * element⁻¹) • value = value at hfix
    change (actor : K) • (element⁻¹ • value) = element⁻¹ • value
    simpa [MulAut.conj_apply, ← mul_smul, mul_assoc] using
      congrArg (fun point : V => element⁻¹ • point) hfix

def NineCoreSupportDecompositionIntrinsic
    {K V : Type*} [Group K] [Group V] [MulDistribMulAction K V]
    (core : Subgroup K) (support : Subgroup V) : Prop :=
  Nat.card support = 4 ∧ ∃ line : Subgroup K,
    line ≤ core ∧ Nat.card line = 3 ∧ support = FixedPoints.subgroup line V

theorem nineCoreSupportDecomposition_intrinsic_map
    {K V : Type*} [Group K] [Group V] [MulDistribMulAction K V]
    (core : Subgroup K) (hnormal : core.Normal) (support : Subgroup V)
    (hsupport : NineCoreSupportDecompositionIntrinsic core support) (element : K) :
    NineCoreSupportDecompositionIntrinsic core
      (support.map (MulDistribMulAction.toMulAut K V element).toMonoidHom) := by
  obtain ⟨hcard, line, hle, hlinecard, rfl⟩ := hsupport
  refine ⟨(Subgroup.card_map_of_injective
    (MulDistribMulAction.toMulAut K V element).injective).trans hcard,
    line.map (MulAut.conj element).toMonoidHom, ?_, ?_,
    nineCoreSupportDecomposition_map_fixedPoints line element⟩
  · rintro actor ⟨source, hsource, rfl⟩
    exact hnormal.conj_mem source (hle hsource) element
  · exact (Subgroup.card_map_of_injective (MulAut.conj element).injective).trans hlinecard

theorem nineCoreSupportDecomposition_permuted_of_intrinsic_pair
    {K V : Type*} [Group K] [Group V] [MulDistribMulAction K V]
    (core : Subgroup K) (hnormal : core.Normal) (first second : Subgroup V)
    (hne : first ≠ second)
    (hpair : ∀ support : Subgroup V,
      NineCoreSupportDecompositionIntrinsic core support ↔
        support = first ∨ support = second) (element : K) :
    (first.map (MulDistribMulAction.toMulAut K V element).toMonoidHom = first ∧
     second.map (MulDistribMulAction.toMulAut K V element).toMonoidHom = second) ∨
    (first.map (MulDistribMulAction.toMulAut K V element).toMonoidHom = second ∧
     second.map (MulDistribMulAction.toMulAut K V element).toMonoidHom = first) := by
  have hfirst := (hpair _).mp (nineCoreSupportDecomposition_intrinsic_map core hnormal
    first ((hpair first).mpr (Or.inl rfl)) element)
  have hsecond := (hpair _).mp (nineCoreSupportDecomposition_intrinsic_map core hnormal
    second ((hpair second).mpr (Or.inr rfl)) element)
  have hmapne : first.map (MulDistribMulAction.toMulAut K V element).toMonoidHom ≠
      second.map (MulDistribMulAction.toMulAut K V element).toMonoidHom :=
    fun heq => hne (Subgroup.map_injective
      (MulDistribMulAction.toMulAut K V element).injective heq)
  rcases hfirst with hfirst | hfirst <;> rcases hsecond with hsecond | hsecond
  · exact (hmapne (hfirst.trans hsecond.symm)).elim
  · exact Or.inl ⟨hfirst, hsecond⟩
  · exact Or.inr ⟨hfirst, hsecond⟩
  · exact (hmapne (hfirst.trans hsecond.symm)).elim

end Stellmacher.SectionOne
