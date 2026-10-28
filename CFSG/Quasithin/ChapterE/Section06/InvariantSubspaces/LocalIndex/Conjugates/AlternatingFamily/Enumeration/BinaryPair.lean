module
public import CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.LocalIndex.Conjugates.AlternatingFamily.Enumeration.FourGeometry
public import Mathlib.Algebra.Group.Equiv.TypeTags
/-!
# Two binary natural planes as the five-letter permutation core

The coordinates (a,b) ↦ (a,a+b) turn a binary shear into a transposition.
Applying this to two planes identifies their direct product with the
even-weight core on five letters, equivariantly for the two commuting actors.
The actor image is the literal pair-swap four-group.

Source application: Aschbacher–Smith C.6.1, paired A₃ branch, printed p.165.
-/
public section
namespace CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.LocalIndex.Conjugates.AlternatingFamily
open Subgroup BinaryPermutation
namespace BinaryPair
abbrev Plane := Multiplicative (Fin 2 → ZMod 2)
abbrev Bit := Multiplicative (ZMod 2)

def split : Multiplicative Vector →* Plane × Plane where
  toFun v := (Multiplicative.ofAdd ![v.toAdd.val 0,v.toAdd.val 0+v.toAdd.val 1],
    Multiplicative.ofAdd ![v.toAdd.val 2,v.toAdd.val 2+v.toAdd.val 3])
  map_one' := by
    apply Prod.ext <;> apply Multiplicative.toAdd.injective <;> ext i <;> fin_cases i <;> rfl
  map_mul' u v := by
    apply Prod.ext
    · apply Multiplicative.toAdd.injective
      ext i
      fin_cases i
      · rfl
      · change (u.toAdd.val 0+v.toAdd.val 0)+(u.toAdd.val 1+v.toAdd.val 1) =
          (u.toAdd.val 0+u.toAdd.val 1)+(v.toAdd.val 0+v.toAdd.val 1)
        abel
    · apply Multiplicative.toAdd.injective
      ext i
      fin_cases i
      · rfl
      · change (u.toAdd.val 2+v.toAdd.val 2)+(u.toAdd.val 3+v.toAdd.val 3) =
          (u.toAdd.val 2+u.toAdd.val 3)+(v.toAdd.val 2+v.toAdd.val 3)
        abel

private def merge (v : Plane × Plane) : Vector :=
  ⟨![v.1.toAdd 0,v.1.toAdd 0+v.1.toAdd 1,v.2.toAdd 0,v.2.toAdd 0+v.2.toAdd 1,
    v.1.toAdd 1+v.2.toAdd 1],by
    change ∑ i : Fin 5, ![v.1.toAdd 0,v.1.toAdd 0+v.1.toAdd 1,v.2.toAdd 0,
      v.2.toAdd 0+v.2.toAdd 1,v.1.toAdd 1+v.2.toAdd 1] i = 0
    simp [Fin.sum_univ_succ,CharTwo.add_self_eq_zero,add_left_comm,add_comm]⟩

def coordinates : Multiplicative Vector ≃* Plane × Plane :=
  { split with
    invFun := fun v => Multiplicative.ofAdd (merge v)
    left_inv := by
      intro v
      apply Multiplicative.toAdd.injective
      apply Subtype.ext
      ext i
      fin_cases i
      · rfl
      · simp [merge,split,←add_assoc,CharTwo.add_self_eq_zero]
      · rfl
      · simp [merge,split,←add_assoc,CharTwo.add_self_eq_zero]
      · have hv := v.toAdd.property
        change ∑ i : Fin 5, v.toAdd.val i = 0 at hv
        simp only [Fin.sum_univ_succ,Fin.sum_univ_zero,add_zero] at hv
        change v.toAdd.val 0 + (v.toAdd.val 1 + (v.toAdd.val 2 + (v.toAdd.val 3 + v.toAdd.val 4))) = 0 at hv
        change v.toAdd.val 0 + v.toAdd.val 1 + (v.toAdd.val 2 + v.toAdd.val 3) = v.toAdd.val 4
        have hh := (eq_neg_iff_add_eq_zero).mpr (show (v.toAdd.val 0+v.toAdd.val 1+(v.toAdd.val 2+v.toAdd.val 3))+v.toAdd.val 4=0 by simpa only [add_assoc] using hv)
        simpa only [CharTwo.neg_eq] using hh
    right_inv := by
      intro v
      apply Prod.ext <;> apply Multiplicative.toAdd.injective <;> ext i <;> fin_cases i <;>
        simp [merge,split,←add_assoc,CharTwo.add_self_eq_zero] }

def bitActor (i : Fin 2) : Bit →* Perm where
  toFun b := if b.toAdd = 0 then 1 else transposition i
  map_one' := by simp
  map_mul' := by
    fin_cases i <;> decide +kernel

def actor : Bit × Bit →* Perm :=
  (bitActor 0).noncommCoprod (bitActor 1) (by
    change ∀ a b : Bit, bitActor 0 a * bitActor 1 b = bitActor 1 b * bitActor 0 a
    decide +kernel)

theorem actor_left : actor (Multiplicative.ofAdd 1,1) = transposition 0 := by decide +kernel

theorem actor_right : actor (1,Multiplicative.ofAdd 1) = transposition 1 := by decide +kernel

theorem actor_injective : Function.Injective actor := by decide +kernel

theorem actor_range : actor.range = ChapterB.Offenders.D 5 := by
  ext p
  rw [Enumeration.mem_actor]
  constructor
  · rintro ⟨⟨a,b⟩,rfl⟩
    revert a b
    decide +kernel
  · rintro (rfl|rfl|rfl|rfl)
    · exact ⟨(1,1),rfl⟩
    · exact ⟨(Multiplicative.ofAdd 1,1),by decide +kernel⟩
    · exact ⟨(1,Multiplicative.ofAdd 1),by decide +kernel⟩
    · exact ⟨(Multiplicative.ofAdd 1,Multiplicative.ofAdd 1),by decide +kernel⟩

theorem coordinate_action (b : Bit × Bit) (v : Vector) :
    (coordinates (Multiplicative.ofAdd (coreRepresentation (Fin 5) (actor b) v))).1.toAdd =
      ![(coordinates (Multiplicative.ofAdd v)).1.toAdd 0 + b.1.toAdd *
        (coordinates (Multiplicative.ofAdd v)).1.toAdd 1,
        (coordinates (Multiplicative.ofAdd v)).1.toAdd 1] ∧
    (coordinates (Multiplicative.ofAdd (coreRepresentation (Fin 5) (actor b) v))).2.toAdd =
      ![(coordinates (Multiplicative.ofAdd v)).2.toAdd 0 + b.2.toAdd *
        (coordinates (Multiplicative.ofAdd v)).2.toAdd 1,
        (coordinates (Multiplicative.ofAdd v)).2.toAdd 1] := by
  have hh : ∀ (b : Bit × Bit) (w : Fin 5 → ZMod 2),
      ![w ((actor b).symm 0),w ((actor b).symm 0)+w ((actor b).symm 1)] =
        ![w 0+b.1.toAdd*(w 0+w 1),w 0+w 1] ∧
      ![w ((actor b).symm 2),w ((actor b).symm 2)+w ((actor b).symm 3)] =
        ![w 2+b.2.toAdd*(w 2+w 3),w 2+w 3] := by decide +kernel
  exact hh b v.val
end BinaryPair
end CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.LocalIndex.Conjugates.AlternatingFamily
