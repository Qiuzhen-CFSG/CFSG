module

public import Mathlib.GroupTheory.Perm.Centralizer
public import Mathlib.GroupTheory.SpecificGroups.Alternating
public import Mathlib.GroupTheory.IsPerfect
public import Mathlib.Tactic

/-!
# Recognizing the transposition and its six-point alternating subgroup

An involution in S₈ whose centralizer has order divisible by 360 is a
transposition: the other involution centralizers have orders 192, 96 and
384. A perfect subgroup centralizing the marked transposition fixes both
of its moved points, because its action on that pair has abelian image.
The even permutations fixing those points have order 360.

These elementary permutation facts supply the compatible A₈–A₆ marking
in Aschbacher–Smith, 16.3.11(3) and the following setup, printed p.1181
of the combined manuscript of 1 March 2004.
-/

public section
namespace Theory.SpecificGroups.SymmetricEight.ComponentMarking
open Subgroup Equiv Equiv.Perm

theorem isSwap_of_centralizer_card (q : Perm (Fin 8)) (hq : orderOf q = 2)
    (hcard : 360 ∣ Nat.card (centralizer ({q} : Set (Perm (Fin 8))))) : q.IsSwap := by
  obtain ⟨r, hr⟩ := cycleType_prime_order (σ := q) (by rw [hq]; exact Nat.prime_two)
  rw [hq] at hr
  have hsum := q.sum_cycleType_le
  rw [hr, Multiset.sum_replicate] at hsum
  simp only [smul_eq_mul, Fintype.card_fin] at hsum
  have hrle : r ≤ 3 := by omega
  interval_cases r
  · exact isSwap_iff_cycleType.mpr (by simpa using hr)
  all_goals
    rw [nat_card_centralizer, hr] at hcard
    norm_num [Multiset.replicate_succ, Nat.factorial] at hcard

/-- A perfect subgroup centralizing `(0 1)` fixes both points individually. -/
theorem perfect_le_pairFixer (P : Subgroup (Perm (Fin 8))) [Group.IsPerfect P]
    (hP : P ≤ centralizer ({swap (0 : Fin 8) 1} : Set (Perm (Fin 8)))) :
    P ≤ MulAction.stabilizer (Perm (Fin 8)) (0 : Fin 8) ⊓
      MulAction.stabilizer (Perm (Fin 8)) (1 : Fin 8) := by
  let p : Fin 8 → Prop := fun x => swap (0 : Fin 8) 1 x ≠ x
  have hpres (g : P) (x : Fin 8) : p (g.val x) ↔ p x := by
    have hc := mem_centralizer_singleton_iff.mp (hP g.property)
    have he := congrArg (fun q : Perm (Fin 8) => q x) hc
    change g.val (swap 0 1 x) = swap 0 1 (g.val x) at he
    apply not_congr
    constructor
    · intro h
      apply g.val.injective
      exact he.trans h
    · intro h
      exact he.symm.trans (congrArg g.val h)
  let ρ : P →* Perm {x // p x} :=
    { toFun := fun g => g.val.subtypePerm (hpres g)
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have htriv (g : P) : ρ g = 1 := by
    have hs : sign (ρ g) = 1 :=
      Abelianization.commutator_subset_ker (sign.comp ρ) (Group.IsPerfect.mem_commutator)
    have hm := mem_alternatingGroup.mpr hs
    rw [alternatingGroup.eq_bot_of_card_le_two
      (by rw [Nat.card_eq_fintype_card]; decide : Nat.card {x // p x} ≤ 2)] at hm
    exact hm
  intro g hg
  have he := htriv ⟨g, hg⟩
  constructor
  · exact congrArg (fun q : Perm {x // p x} => (q ⟨0, by decide⟩).val) he
  · exact congrArg (fun q : Perm {x // p x} => (q ⟨1, by decide⟩).val) he

/-- The even pointwise stabilizer of the marked pair has order 360. -/
theorem card_evenPairFixer : Nat.card (alternatingGroup (Fin 8) ⊓
    (MulAction.stabilizer (Perm (Fin 8)) (0 : Fin 8) ⊓
     MulAction.stabilizer (Perm (Fin 8)) (1 : Fin 8)) : Subgroup (Perm (Fin 8))) = 360 := by
  classical
  let s : Finset (Fin 8) := Finset.univ \ {0, 1}
  let f : alternatingGroup s →* Perm (Fin 8) :=
    (alternatingGroup (Fin 8)).subtype.comp (alternatingGroup.ofSubtype s)
  have hf : Function.Injective f :=
    (alternatingGroup (Fin 8)).subtype_injective.comp alternatingGroup.ofSubtype_injective
  have hr : f.range = alternatingGroup (Fin 8) ⊓
      (MulAction.stabilizer (Perm (Fin 8)) (0 : Fin 8) ⊓
       MulAction.stabilizer (Perm (Fin 8)) (1 : Fin 8)) := by
    ext g
    rw [MonoidHom.range_comp, alternatingGroup.range_ofSubtype,
      subgroupOf_map_subtype]
    rw [Subgroup.mem_inf, Subgroup.mem_inf]
    simp only [Equiv.Perm.mem_range_ofSubtype_iff, Set.subset_def, Set.mem_ofPred_eq,
      Finset.mem_coe, Equiv.Perm.mem_support]
    simp only [s, Finset.mem_sdiff, Finset.mem_univ, Finset.mem_insert,
      Finset.mem_singleton, true_and, not_or]
    constructor
    · rintro ⟨hs, ha⟩
      exact ⟨ha, by by_contra h; exact (hs 0 h).1 rfl,
        by by_contra h; exact (hs 1 h).2 rfl⟩
    · rintro ⟨ha, h0, h1⟩
      refine ⟨fun x hx => ⟨?_, ?_⟩, ha⟩ <;> intro he <;> subst x
      · exact hx h0
      · exact hx h1
  rw [← hr, ← Nat.card_congr (MonoidHom.ofInjective hf).toEquiv]
  have hs : Nat.card s = 6 := by rw [Nat.card_eq_fintype_card]; decide
  have : Nontrivial s := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  rw [nat_card_alternatingGroup, hs]
  norm_num [Nat.factorial]

end Theory.SpecificGroups.SymmetricEight.ComponentMarking
