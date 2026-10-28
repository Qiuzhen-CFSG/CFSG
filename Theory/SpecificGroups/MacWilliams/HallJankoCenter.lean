module
public import Theory.SpecificGroups.MacWilliams.SylowPresentations
public import Theory.GroupTheory.PresentedGroupBounds
public import Mathlib.GroupTheory.Subgroup.Centralizer
public import Mathlib.Data.Fintype.Card

/-!
# The center of the Hall–Janko Sylow presentation

The seven-generator power-commutator presentation has exactly 128 elements,
and its center has order two. A normal word uses each generator at most once,
in increasing order; its seven bits give a code in `Fin 128`.

The proof first certifies collection using only the defining square and
commutator relations. Explicit bit formulas describe left and right generator
multiplication. A permutation realization satisfying the same presentation
separates all the normal words. Finally, a finite check shows that the only
codes commuting with every generator are 0 and 64, corresponding to the
identity and the last generator. All finite checks use kernel reduction.

Source: the presentation in `SylowPresentations`, representing the Hall–Janko
alternative in Janko–Thompson, Math. Z. 113 (1970), Theorem 1.3, p.386.
The coordinate formulas are certified here directly; no group identification
or externally computed group order enters the proof.
-/

namespace MacWilliamsSylow
namespace HallJankoCalculation

private abbrev gen := generator hallJankoTable
private abbrev eval := word gen

private theorem eval_append (u v : List (Fin 7)) : eval (u ++ v) = eval u * eval v := by
  simp [word]

private theorem swap (i j : Fin 7) (h : i < j) :
    gen j * gen i = gen i * gen j * eval (hallJankoTable.commutator j i) := by
  have hc : rightComm (gen j) (gen i) = eval (hallJankoTable.commutator j i) :=
    (generator_relations hallJankoTable).commutator i j h
  rw [← hc]
  simp [rightComm, mul_assoc]

-- One collection step replaces the first repeated or out-of-order pair.
private def step : List (Fin 7) → List (Fin 7)
  | [] => []
  | [a] => [a]
  | a :: b :: rest =>
    if a = b then hallJankoTable.square a ++ rest
    else if b < a then b :: a :: (hallJankoTable.commutator a b ++ rest)
    else a :: step (b :: rest)

private theorem step_sound (w : List (Fin 7)) : eval (step w) = eval w := by
  induction w using step.induct with
  | case1 => rfl
  | case2 a => rfl
  | case3 a rest =>
    simp only [step, if_true, eval_append]
    have hs : gen a * gen a = eval (hallJankoTable.square a) :=
      (generator_relations hallJankoTable).square a
    rw [← hs]
    simp [word, mul_assoc]
  | case4 a b rest he hl =>
    simp only [step, if_neg he, if_pos hl]
    change gen b * (gen a * eval (hallJankoTable.commutator a b ++ rest)) =
      gen a * (gen b * eval rest)
    rw [eval_append]
    simp only [← mul_assoc]
    rw [← swap b a hl]
  | case5 a b rest he hl ih =>
    simp only [step, if_neg he, if_neg hl]
    change gen a * eval (step (b :: rest)) = gen a * eval (b :: rest)
    rw [ih]

-- Bounded collection suffices: the two transition certificates below
-- check every normal word and generator, with explicit fuel bounds.
private def collect : ℕ → List (Fin 7) → List (Fin 7)
  | 0, w => w
  | k + 1, w => collect k (step w)

private theorem collect_sound (k : ℕ) (w : List (Fin 7)) : eval (collect k w) = eval w := by
  induction k generalizing w with
  | zero => rfl
  | succ k ih => exact (ih (step w)).trans (step_sound w)

/-- The increasing normal word represented by the seven bits. -/
@[expose] public def normal (n : Fin 128) : List (Fin 7) :=
  (List.finRange 7).filter (fun i => n.val.testBit i.val)

-- Binary coordinate formulas; the following collection certificates prove
-- these formulas in the presented group itself.
/-- Right multiplication by a presentation generator, in binary coordinates. -/
@[expose] public def right (i : Fin 7) (n : Fin 128) : Fin 128 :=
  let b := n.val.testBit
  ⟨(match i.val with
    | 0 => n.val ^^^
      1 ^^^
      (if (b 1) then 8 else 0) ^^^
      (if (b 2) then 16 else 0) ^^^
      (if (b 1 && b 2) then 32 else 0) ^^^
      (if (b 3) ^^ (b 1 && b 3) ^^ (b 2 && b 3) ^^ (b 4) ^^ (b 2 && b 4) ^^ (b 5) then 64 else 0)
    | 1 => n.val ^^^ 2 ^^^ (if (b 4) then 32 else 0) ^^^ (if (b 3) ^^ (b 4) then 64 else 0)
    | 2 => n.val ^^^ 4 ^^^ (if (b 3) then 32 else 0) ^^^ (if (b 4) then 64 else 0)
    | 3 => n.val ^^^ 8 ^^^ (if (b 3) ^^ (b 4) then 64 else 0)
    | 4 => n.val ^^^ 16 ^^^ (if (b 4) then 64 else 0)
    | 5 => n.val ^^^ 32
    | _ => n.val ^^^ 64) % 128, Nat.mod_lt _ (by decide)⟩

private def left (i : Fin 7) (n : Fin 128) : Fin 128 :=
  let b := n.val.testBit
  ⟨(match i.val with
    | 0 => n.val ^^^ 1
    | 1 => n.val ^^^
      2 ^^^
      (if (b 0) then 8 else 0) ^^^
      (if (b 0 && b 2) then 32 else 0) ^^^
      (if (b 0 && b 1) ^^ (b 0 && b 3) then 64 else 0)
    | 2 => n.val ^^^
      4 ^^^
      (if (b 0) then 16 else 0) ^^^
      (if (b 0 && b 1) then 32 else 0) ^^^
      (if (b 0 && b 1) ^^ (b 0 && b 2) ^^ (b 0 && b 3) ^^ (b 0 && b 4) then 64 else 0)
    | 3 => n.val ^^^ 8 ^^^ (if (b 2) then 32 else 0) ^^^ (if (b 0) ^^ (b 1) ^^ (b 3) then 64 else 0)
    | 4 => n.val ^^^
      16 ^^^
      (if (b 1) then 32 else 0) ^^^
      (if (b 0) ^^ (b 1) ^^ (b 2) ^^ (b 3) ^^ (b 4) then 64 else 0)
    | 5 => n.val ^^^ 32 ^^^ (if (b 0) then 64 else 0)
    | _ => n.val ^^^ 64) % 128, Nat.mod_lt _ (by decide)⟩

set_option maxRecDepth 10000
private theorem collected_right : ∀ (i : Fin 7) (n : Fin 128),
    collect 22 (normal n ++ [i]) = normal (right i n) := by decide +kernel

private theorem collected_left : ∀ (i : Fin 7) (n : Fin 128),
    collect 18 (i :: normal n) = normal (left i n) := by decide +kernel

/-- Interpret a binary coordinate as its normal word in the presentation. -/
@[expose] public def representative (n : Fin 128) : HallJankoSylow :=
  word (generator hallJankoTable) (normal n)

/-- The binary right transition is multiplication in the presentation. -/
public theorem repr_right (i : Fin 7) (n : Fin 128) :
    representative n * generator hallJankoTable i = representative (right i n) := by
  calc
    representative n * gen i = eval (normal n ++ [i]) := by simp [representative, eval_append, word]
    _ = eval (collect 22 (normal n ++ [i])) := (collect_sound _ _).symm
    _ = representative (right i n) := congrArg eval (collected_right i n)

private theorem repr_left (i : Fin 7) (n : Fin 128) :
    gen i * representative n = representative (left i n) := by
  calc
    gen i * representative n = eval (i :: normal n) := rfl
    _ = eval (collect 18 (i :: normal n)) := (collect_sound _ _).symm
    _ = representative (left i n) := congrArg eval (collected_left i n)

private theorem right_fourth : ∀ (i : Fin 7) (n : Fin 128),
    right i (right i (right i (right i n))) = n := by decide +kernel

private theorem left_fourth : ∀ (i : Fin 7) (n : Fin 128),
    left i (left i (left i (left i n))) = n := by decide +kernel

-- Left multiplication gives a permutation model. Every generator has
-- fourth power one, so its cube supplies the inverse.
private def perm (i : Fin 7) : Equiv.Perm (Fin 128) where
  toFun := left i
  invFun := fun n => left i (left i (left i n))
  left_inv := left_fourth i
  right_inv := left_fourth i

private theorem perm_relations : Relations hallJankoTable perm where
  square := by decide +kernel
  commutator := by decide +kernel

private def action : HallJankoSylow →* Equiv.Perm (Fin 128) :=
  presentationHom perm_relations

private theorem perm_normal : ∀ n : Fin 128, word perm (normal n) 0 = n := by
  decide +kernel

private theorem action_repr (n : Fin 128) : action (representative n) 0 = n := by
  change presentationHom perm_relations (word gen (normal n)) 0 = n
  rw [map_word]
  simpa only [gen, presentationHom_generator] using perm_normal n

private theorem repr_injective : Function.Injective representative := by
  intro n m h
  have := congrArg (fun x => action x 0) h
  simpa only [action_repr] using this

/-- The zero code represents the identity. -/
public theorem repr_zero : representative 0 = 1 := rfl

-- The certified transitions cover the group, including inverse steps.
private def cover : Subgroup.GeneratorCosetCover (⊥ : Subgroup HallJankoSylow) gen (Fin 128) where
  repr := representative
  initial := 0
  initial_eq := repr_zero
  step n i := ⟨1, right i n, by simpa using repr_right i n⟩
  inv_step n i := by
    refine ⟨1, right i (right i (right i n)), ?_⟩
    have h := repr_right i (right i (right i (right i n)))
    rw [right_fourth] at h
    simpa using (eq_mul_inv_iff_mul_eq.mpr h).symm

private theorem repr_surjective : Function.Surjective representative := by
  intro x
  obtain ⟨h, n, he⟩ := cover.covers (generator_closure hallJankoTable) x
  change x = h.val * representative n at he
  have hh : h.val = 1 := h.property
  exact ⟨n, by simpa [hh] using he.symm⟩

/-- Every presented-group element has a unique binary normal word. -/
public theorem representative_bijective : Function.Bijective representative :=
  ⟨repr_injective, repr_surjective⟩

-- Equality of the left and right transitions is precisely commutation
-- with each generator. Only the identity and last generator pass.
private theorem center_check : ∀ n : Fin 128,
    (∀ i : Fin 7, left i n = right i n) ↔ n = 0 ∨ n = 64 := by decide +kernel

private theorem repr_mem_center (n : Fin 128) :
    representative n ∈ Subgroup.center HallJankoSylow ↔ n = 0 ∨ n = 64 := by
  rw [← center_check n]
  have hc : Subgroup.center HallJankoSylow = Subgroup.centralizer (Set.range gen) := by
    rw [← Subgroup.centralizer_closure, generator_closure, Subgroup.coe_top,
      Subgroup.centralizer_univ]
  rw [hc, Subgroup.mem_centralizer_iff]
  simp only [Set.forall_mem_range, repr_left, repr_right, repr_injective.eq_iff]

end HallJankoCalculation

open HallJankoCalculation

/-- The seven-generator Hall–Janko Sylow presentation is finite. -/
public instance hallJankoSylow_finite : Finite HallJankoSylow :=
  Finite.of_surjective representative repr_surjective

/-- The binary collected words give exactly 128 elements. -/
public theorem hallJankoSylow_card : Nat.card HallJankoSylow = 128 := by
  rw [← Nat.card_congr (Equiv.ofBijective representative ⟨repr_injective, repr_surjective⟩)]
  exact Nat.card_fin 128

/-- The center of the Hall–Janko Sylow presentation has order two. -/
public theorem hallJankoSylow_center_card : Nat.card (Subgroup.center HallJankoSylow) = 2 := by
  let z : Subgroup.center HallJankoSylow := ⟨representative 64, (repr_mem_center 64).mpr (Or.inr rfl)⟩
  apply (Nat.card_eq_two_iff' (1 : Subgroup.center HallJankoSylow)).mpr
  refine ⟨z, ?_, ?_⟩
  · intro h
    have hz : representative 64 = representative 0 := (congrArg Subtype.val h).trans repr_zero.symm
    have := repr_injective hz
    contradiction
  · intro y hy
    apply Subtype.ext
    obtain ⟨n, hn⟩ := repr_surjective y.val
    have hc := (repr_mem_center n).mp (by rw [hn]; exact y.property)
    rcases hc with rfl | rfl
    · exact False.elim (hy (Subtype.ext (hn.symm.trans repr_zero)))
    · exact hn.symm

end MacWilliamsSylow
