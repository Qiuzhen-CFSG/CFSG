module

import Mathlib.Tactic.FinCases

public import
  Theory.SpecificGroups.Janko4.Model.Cardinality.LocalOrder.QuotientCount.UpperBound.PresentationBound.FirstStabilizer

/-!
# A 24-coset cover of the original local presentation

The immutable representatives and 48 paired transitions below replay
`source/scan.json` (relative to the parent directory). The 23 defining edges
are literal word extensions. Each of the 25 remaining edges follows by
cancelling the known prefix and suffix of an original relator loop or a whole
subgroup-generator loop. Every path is composed from earlier group equalities;
no permutation identity, finiteness assumption, or auxiliary relation is used.

The candidate trace and multiplication convention are documented in
`source/README.md`. This is the right-coset form of the Todd--Coxeter scan.
-/

namespace Janko4.Cardinality.QuotientCount.UpperBound.PresentationBound
open Subgroup.CosetWordCertificate

set_option maxRecDepth 16384

variable {G α : Type*} [Group G] {H : Subgroup G} {g : α → G} {ρ : Nat → G}
private theorem appendFacts {i j k : Nat} {u v : Word α}
    (hu : Holds H g ρ ⟨i, u, j⟩) (hv : Holds H g ρ ⟨j, v, k⟩) :
    Holds H g ρ ⟨i, u ++ v, k⟩ := by
  obtain ⟨h, hh⟩ := hu
  obtain ⟨h', hh'⟩ := hv
  refine ⟨h * h', ?_⟩
  change ρ i * eval g (u ++ v) = (h.val * h'.val) * ρ k
  rw [eval_append, ← mul_assoc, hh, mul_assoc, hh', ← mul_assoc]
private theorem scanFacts {i j k : Nat} {u v : Word α} {a : Letter α}
    (hu : Holds H g ρ ⟨i, u, j⟩) (hv : Holds H g ρ ⟨k, v, i⟩)
    (hw : Holds H g ρ ⟨i, (u ++ [a]) ++ v, i⟩) :
    Holds H g ρ ⟨j, [a], k⟩ := by
  obtain ⟨p, hp⟩ := hu
  obtain ⟨s, hs⟩ := hv
  obtain ⟨l, hl⟩ := hw
  change ρ i * eval g ((u ++ [a]) ++ v) = l.val * ρ i at hl
  change ρ i * eval g u = p.val * ρ j at hp
  change ρ k * eval g v = s.val * ρ i at hs
  refine ⟨p⁻¹ * l * s⁻¹, ?_⟩
  change ρ j * eval g [a] = (p.val⁻¹ * l.val * s.val⁻¹) * ρ k
  apply mul_right_cancel (b := eval g v)
  have hi : ρ i = s.val⁻¹ * (ρ k * eval g v) := by rw [hs]; simp
  have hj : ρ j = p.val⁻¹ * (ρ i * eval g u) := by rw [hp]; simp
  calc
    ρ j * eval g [a] * eval g v = p.val⁻¹ * (ρ i * eval g ((u ++ [a]) ++ v)) := by
      rw [hj, eval_append, eval_append]; simp only [mul_assoc]
    _ = (p.val⁻¹ * l.val * s.val⁻¹) * ρ k * eval g v := by
      rw [hl, hi]; simp only [mul_assoc]

private def representativeWord : Nat → Word Bool
  | 0 => []
  | 1 => [(false, true)]
  | 2 => [(true, true)]
  | 3 => [(true, true), (false, true)]
  | 4 => [(true, true), (false, true), (true, true)]
  | 5 => [(true, true), (false, true), (true, false)]
  | 6 => [(true, true), (false, true), (true, true), (false, true)]
  | 7 => [(true, true), (false, true), (true, false), (false, true)]
  | 8 => [(true, true), (false, true), (true, true), (false, true), (true, true)]
  | 9 => [(true, true), (false, true), (true, true), (false, true), (true, false)]
  | 10 => [(true, true), (false, true), (true, false), (false, true), (true, true)]
  | 11 => [(true, true), (false, true), (true, false), (false, true), (true, false)]
  | 12 => [(true, true), (false, true), (true, true), (false, true), (true, true), (false, true)]
  | 13 => [(true, true), (false, true), (true, true), (false, true), (true, false), (false, true)]
  | 14 => [(true, true), (false, true), (true, false), (false, true), (true, true), (false, true)]
  | 15 => [(true, true), (false, true), (true, false), (false, true), (true, false), (false, true)]
  | 16 => [(true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true,
    true)]
  | 17 => [(true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true,
    false)]
  | 18 => [(true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true,
    true), (false, true)]
  | 19 => [(true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true,
    false), (false, true)]
  | 20 => [(true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true,
    true), (false, true), (true, true)]
  | 21 => [(true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true,
    true), (false, true), (true, false)]
  | 22 => [(true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true,
    false), (false, true), (true, true)]
  | 23 => [(true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true,
    false), (false, true), (true, false)]
  | _ => []

private def representative (i : Nat) : Presentation :=
  eval PresentedGroup.of (representativeWord i)

-- Trace event 0: ['define', 0, 1, 1].
private theorem edge00 : Holds firstSubgroup PresentedGroup.of representative ⟨0, [(false, true)], 1⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [] [(false, true)]).symm

private theorem edge00Inv : Holds firstSubgroup PresentedGroup.of representative ⟨1, [(false, false)], 0⟩ :=
  holds_reverse edge00

-- Trace event 1: ['define', 0, 2, 2].
private theorem edge01 : Holds firstSubgroup PresentedGroup.of representative ⟨0, [(true, true)], 2⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [] [(true, true)]).symm

private theorem edge01Inv : Holds firstSubgroup PresentedGroup.of representative ⟨2, [(true, false)], 0⟩ :=
  holds_reverse edge01

-- Trace event 2: ['define', 2, 1, 3].
private theorem edge02 : Holds firstSubgroup PresentedGroup.of representative ⟨2, [(false, true)], 3⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(true, true)] [(false, true)]).symm

private theorem edge02Inv : Holds firstSubgroup PresentedGroup.of representative ⟨3, [(false, false)], 2⟩ :=
  holds_reverse edge02

-- Trace event 3: ['define', 3, 2, 4].
private theorem edge03 : Holds firstSubgroup PresentedGroup.of representative ⟨3, [(true, true)], 4⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(true, true), (false, true)] [(true, true)]).symm

private theorem edge03Inv : Holds firstSubgroup PresentedGroup.of representative ⟨4, [(true, false)], 3⟩ :=
  holds_reverse edge03

-- Trace event 4: ['define', 3, -2, 5].
private theorem edge04 : Holds firstSubgroup PresentedGroup.of representative ⟨3, [(true, false)], 5⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(true, true), (false, true)] [(true, false)]).symm

private theorem edge04Inv : Holds firstSubgroup PresentedGroup.of representative ⟨5, [(true, true)], 3⟩ :=
  holds_reverse edge04

-- Trace event 5: ['define', 4, 1, 6].
private theorem edge05 : Holds firstSubgroup PresentedGroup.of representative ⟨4, [(false, true)], 6⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(true, true), (false, true), (true, true)] [(false, true)]).symm

private theorem edge05Inv : Holds firstSubgroup PresentedGroup.of representative ⟨6, [(false, false)], 4⟩ :=
  holds_reverse edge05

-- Trace event 6: ['define', 5, 1, 7].
private theorem edge06 : Holds firstSubgroup PresentedGroup.of representative ⟨5, [(false, true)], 7⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(true, true), (false, true), (true, false)] [(false, true)]).symm

private theorem edge06Inv : Holds firstSubgroup PresentedGroup.of representative ⟨7, [(false, false)], 5⟩ :=
  holds_reverse edge06

-- Trace event 7: ['define', 6, 2, 8].
private theorem edge07 : Holds firstSubgroup PresentedGroup.of representative ⟨6, [(true, true)], 8⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(true, true), (false, true), (true, true), (false, true)] [(true,
    true)]).symm

private theorem edge07Inv : Holds firstSubgroup PresentedGroup.of representative ⟨8, [(true, false)], 6⟩ :=
  holds_reverse edge07

-- Trace event 8: ['define', 6, -2, 9].
private theorem edge08 : Holds firstSubgroup PresentedGroup.of representative ⟨6, [(true, false)], 9⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(true, true), (false, true), (true, true), (false, true)] [(true,
    false)]).symm

private theorem edge08Inv : Holds firstSubgroup PresentedGroup.of representative ⟨9, [(true, true)], 6⟩ :=
  holds_reverse edge08

-- Trace event 9: ['define', 7, 2, 10].
private theorem edge09 : Holds firstSubgroup PresentedGroup.of representative ⟨7, [(true, true)], 10⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(true, true), (false, true), (true, false), (false, true)] [(true,
    true)]).symm

private theorem edge09Inv : Holds firstSubgroup PresentedGroup.of representative ⟨10, [(true, false)], 7⟩ :=
  holds_reverse edge09

-- Trace event 10: ['define', 7, -2, 11].
private theorem edge10 : Holds firstSubgroup PresentedGroup.of representative ⟨7, [(true, false)], 11⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(true, true), (false, true), (true, false), (false, true)] [(true,
    false)]).symm

private theorem edge10Inv : Holds firstSubgroup PresentedGroup.of representative ⟨11, [(true, true)], 7⟩ :=
  holds_reverse edge10

-- Trace event 11: ['define', 8, 1, 12].
private theorem edge11 : Holds firstSubgroup PresentedGroup.of representative ⟨8, [(false, true)], 12⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(true, true), (false, true), (true, true), (false, true), (true,
    true)] [(false, true)]).symm

private theorem edge11Inv : Holds firstSubgroup PresentedGroup.of representative ⟨12, [(false, false)], 8⟩ :=
  holds_reverse edge11

-- Trace event 12: ['define', 9, 1, 13].
private theorem edge12 : Holds firstSubgroup PresentedGroup.of representative ⟨9, [(false, true)], 13⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(true, true), (false, true), (true, true), (false, true), (true,
    false)] [(false, true)]).symm

private theorem edge12Inv : Holds firstSubgroup PresentedGroup.of representative ⟨13, [(false, false)], 9⟩ :=
  holds_reverse edge12

-- Trace event 13: ['define', 10, 1, 14].
private theorem edge13 : Holds firstSubgroup PresentedGroup.of representative ⟨10, [(false, true)], 14⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(true, true), (false, true), (true, false), (false, true), (true,
    true)] [(false, true)]).symm

private theorem edge13Inv : Holds firstSubgroup PresentedGroup.of representative ⟨14, [(false, false)], 10⟩ :=
  holds_reverse edge13

-- Trace event 14: ['define', 11, 1, 15].
private theorem edge14 : Holds firstSubgroup PresentedGroup.of representative ⟨11, [(false, true)], 15⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(true, true), (false, true), (true, false), (false, true), (true,
    false)] [(false, true)]).symm

private theorem edge14Inv : Holds firstSubgroup PresentedGroup.of representative ⟨15, [(false, false)], 11⟩ :=
  holds_reverse edge14

-- Trace event 15: ['define', 14, 2, 16].
private theorem edge15 : Holds firstSubgroup PresentedGroup.of representative ⟨14, [(true, true)], 16⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(true, true), (false, true), (true, false), (false, true), (true,
    true), (false, true)] [(true, true)]).symm

private theorem edge15Inv : Holds firstSubgroup PresentedGroup.of representative ⟨16, [(true, false)], 14⟩ :=
  holds_reverse edge15

-- Trace event 16: ['define', 14, -2, 17].
private theorem edge16 : Holds firstSubgroup PresentedGroup.of representative ⟨14, [(true, false)], 17⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(true, true), (false, true), (true, false), (false, true), (true,
    true), (false, true)] [(true, false)]).symm

private theorem edge16Inv : Holds firstSubgroup PresentedGroup.of representative ⟨17, [(true, true)], 14⟩ :=
  holds_reverse edge16

-- Trace event 17: ['define', 16, 1, 18].
private theorem edge17 : Holds firstSubgroup PresentedGroup.of representative ⟨16, [(false, true)], 18⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(true, true), (false, true), (true, false), (false, true), (true,
    true), (false, true), (true, true)] [(false, true)]).symm

private theorem edge17Inv : Holds firstSubgroup PresentedGroup.of representative ⟨18, [(false, false)], 16⟩ :=
  holds_reverse edge17

-- Trace event 18: ['define', 17, 1, 19].
private theorem edge18 : Holds firstSubgroup PresentedGroup.of representative ⟨17, [(false, true)], 19⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(true, true), (false, true), (true, false), (false, true), (true,
    true), (false, true), (true, false)] [(false, true)]).symm

private theorem edge18Inv : Holds firstSubgroup PresentedGroup.of representative ⟨19, [(false, false)], 17⟩ :=
  holds_reverse edge18

-- Trace event 19: ['define', 18, 2, 20].
private theorem edge19 : Holds firstSubgroup PresentedGroup.of representative ⟨18, [(true, true)], 20⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(true, true), (false, true), (true, false), (false, true), (true,
    true), (false, true), (true, true), (false, true)] [(true, true)]).symm

private theorem edge19Inv : Holds firstSubgroup PresentedGroup.of representative ⟨20, [(true, false)], 18⟩ :=
  holds_reverse edge19

-- Trace event 20: ['define', 18, -2, 21].
private theorem edge20 : Holds firstSubgroup PresentedGroup.of representative ⟨18, [(true, false)], 21⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(true, true), (false, true), (true, false), (false, true), (true,
    true), (false, true), (true, true), (false, true)] [(true, false)]).symm

private theorem edge20Inv : Holds firstSubgroup PresentedGroup.of representative ⟨21, [(true, true)], 18⟩ :=
  holds_reverse edge20

-- Trace event 21: ['define', 19, 2, 22].
private theorem edge21 : Holds firstSubgroup PresentedGroup.of representative ⟨19, [(true, true)], 22⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(true, true), (false, true), (true, false), (false, true), (true,
    true), (false, true), (true, false), (false, true)] [(true, true)]).symm

private theorem edge21Inv : Holds firstSubgroup PresentedGroup.of representative ⟨22, [(true, false)], 19⟩ :=
  holds_reverse edge21

-- Trace event 22: ['define', 19, -2, 23].
private theorem edge22 : Holds firstSubgroup PresentedGroup.of representative ⟨19, [(true, false)], 23⟩ := by
  apply holds_defining
  exact (eval_append PresentedGroup.of [(true, true), (false, true), (true, false), (false, true), (true,
    true), (false, true), (true, false), (false, true)] [(true, false)]).symm

private theorem edge22Inv : Holds firstSubgroup PresentedGroup.of representative ⟨23, [(true, true)], 19⟩ :=
  holds_reverse edge22

-- Trace event 23: ['scan', 0, ['rel', 0], 1, 1, 1, 0].
private theorem edge23 : Holds firstSubgroup PresentedGroup.of representative ⟨1, [(false, true)], 0⟩ := by
  have hpre : Holds firstSubgroup PresentedGroup.of representative ⟨0, [(false, true)], 1⟩ :=
    edge00
  have hsuf : Holds firstSubgroup PresentedGroup.of representative ⟨0, [], 0⟩ :=
    (holds_refl 0)
  exact scanFacts hpre hsuf (holds_relator 0 (relatorLetters 0) (presentation_relator 0))

private theorem edge23Inv : Holds firstSubgroup PresentedGroup.of representative ⟨0, [(false, false)], 1⟩ :=
  holds_reverse edge23

-- Trace event 24: ['scan', 2, ['rel', 0], 1, 3, 1, 2].
private theorem edge24 : Holds firstSubgroup PresentedGroup.of representative ⟨3, [(false, true)], 2⟩ := by
  have hpre : Holds firstSubgroup PresentedGroup.of representative ⟨2, [(false, true)], 3⟩ :=
    edge02
  have hsuf : Holds firstSubgroup PresentedGroup.of representative ⟨2, [], 2⟩ :=
    (holds_refl 2)
  exact scanFacts hpre hsuf (holds_relator 2 (relatorLetters 0) (presentation_relator 0))

private theorem edge24Inv : Holds firstSubgroup PresentedGroup.of representative ⟨2, [(false, false)], 3⟩ :=
  holds_reverse edge24

-- Trace event 25: ['scan', 3, ['rel', 1], 1, 4, 2, 5].
private theorem edge25 : Holds firstSubgroup PresentedGroup.of representative ⟨4, [(true, true)], 5⟩ := by
  have hpre : Holds firstSubgroup PresentedGroup.of representative ⟨3, [(true, true)], 4⟩ :=
    edge03
  have hsuf : Holds firstSubgroup PresentedGroup.of representative ⟨5, [(true, true)], 3⟩ :=
    edge04Inv
  exact scanFacts hpre hsuf (holds_relator 3 (relatorLetters 1) (presentation_relator 1))

private theorem edge25Inv : Holds firstSubgroup PresentedGroup.of representative ⟨5, [(true, false)], 4⟩ :=
  holds_reverse edge25

-- Trace event 26: ['scan', 4, ['rel', 0], 1, 6, 1, 4].
private theorem edge26 : Holds firstSubgroup PresentedGroup.of representative ⟨6, [(false, true)], 4⟩ := by
  have hpre : Holds firstSubgroup PresentedGroup.of representative ⟨4, [(false, true)], 6⟩ :=
    edge05
  have hsuf : Holds firstSubgroup PresentedGroup.of representative ⟨4, [], 4⟩ :=
    (holds_refl 4)
  exact scanFacts hpre hsuf (holds_relator 4 (relatorLetters 0) (presentation_relator 0))

private theorem edge26Inv : Holds firstSubgroup PresentedGroup.of representative ⟨4, [(false, false)], 6⟩ :=
  holds_reverse edge26

-- Trace event 27: ['scan', 5, ['rel', 0], 1, 7, 1, 5].
private theorem edge27 : Holds firstSubgroup PresentedGroup.of representative ⟨7, [(false, true)], 5⟩ := by
  have hpre : Holds firstSubgroup PresentedGroup.of representative ⟨5, [(false, true)], 7⟩ :=
    edge06
  have hsuf : Holds firstSubgroup PresentedGroup.of representative ⟨5, [], 5⟩ :=
    (holds_refl 5)
  exact scanFacts hpre hsuf (holds_relator 5 (relatorLetters 0) (presentation_relator 0))

private theorem edge27Inv : Holds firstSubgroup PresentedGroup.of representative ⟨5, [(false, false)], 7⟩ :=
  holds_reverse edge27

-- Trace event 28: ['scan', 6, ['rel', 1], 1, 8, 2, 9].
private theorem edge28 : Holds firstSubgroup PresentedGroup.of representative ⟨8, [(true, true)], 9⟩ := by
  have hpre : Holds firstSubgroup PresentedGroup.of representative ⟨6, [(true, true)], 8⟩ :=
    edge07
  have hsuf : Holds firstSubgroup PresentedGroup.of representative ⟨9, [(true, true)], 6⟩ :=
    edge08Inv
  exact scanFacts hpre hsuf (holds_relator 6 (relatorLetters 1) (presentation_relator 1))

private theorem edge28Inv : Holds firstSubgroup PresentedGroup.of representative ⟨9, [(true, false)], 8⟩ :=
  holds_reverse edge28

-- Trace event 29: ['scan', 7, ['rel', 1], 1, 10, 2, 11].
private theorem edge29 : Holds firstSubgroup PresentedGroup.of representative ⟨10, [(true, true)], 11⟩ := by
  have hpre : Holds firstSubgroup PresentedGroup.of representative ⟨7, [(true, true)], 10⟩ :=
    edge09
  have hsuf : Holds firstSubgroup PresentedGroup.of representative ⟨11, [(true, true)], 7⟩ :=
    edge10Inv
  exact scanFacts hpre hsuf (holds_relator 7 (relatorLetters 1) (presentation_relator 1))

private theorem edge29Inv : Holds firstSubgroup PresentedGroup.of representative ⟨11, [(true, false)], 10⟩ :=
  holds_reverse edge29

-- Trace event 30: ['scan', 8, ['rel', 0], 1, 12, 1, 8].
private theorem edge30 : Holds firstSubgroup PresentedGroup.of representative ⟨12, [(false, true)], 8⟩ := by
  have hpre : Holds firstSubgroup PresentedGroup.of representative ⟨8, [(false, true)], 12⟩ :=
    edge11
  have hsuf : Holds firstSubgroup PresentedGroup.of representative ⟨8, [], 8⟩ :=
    (holds_refl 8)
  exact scanFacts hpre hsuf (holds_relator 8 (relatorLetters 0) (presentation_relator 0))

private theorem edge30Inv : Holds firstSubgroup PresentedGroup.of representative ⟨8, [(false, false)], 12⟩ :=
  holds_reverse edge30

-- Trace event 31: ['scan', 9, ['rel', 0], 1, 13, 1, 9].
private theorem edge31 : Holds firstSubgroup PresentedGroup.of representative ⟨13, [(false, true)], 9⟩ := by
  have hpre : Holds firstSubgroup PresentedGroup.of representative ⟨9, [(false, true)], 13⟩ :=
    edge12
  have hsuf : Holds firstSubgroup PresentedGroup.of representative ⟨9, [], 9⟩ :=
    (holds_refl 9)
  exact scanFacts hpre hsuf (holds_relator 9 (relatorLetters 0) (presentation_relator 0))

private theorem edge31Inv : Holds firstSubgroup PresentedGroup.of representative ⟨9, [(false, false)], 13⟩ :=
  holds_reverse edge31

-- Trace event 32: ['scan', 10, ['rel', 0], 1, 14, 1, 10].
private theorem edge32 : Holds firstSubgroup PresentedGroup.of representative ⟨14, [(false, true)], 10⟩ := by
  have hpre : Holds firstSubgroup PresentedGroup.of representative ⟨10, [(false, true)], 14⟩ :=
    edge13
  have hsuf : Holds firstSubgroup PresentedGroup.of representative ⟨10, [], 10⟩ :=
    (holds_refl 10)
  exact scanFacts hpre hsuf (holds_relator 10 (relatorLetters 0) (presentation_relator 0))

private theorem edge32Inv : Holds firstSubgroup PresentedGroup.of representative ⟨10, [(false, false)], 14⟩ :=
  holds_reverse edge32

-- Trace event 33: ['scan', 11, ['rel', 0], 1, 15, 1, 11].
private theorem edge33 : Holds firstSubgroup PresentedGroup.of representative ⟨15, [(false, true)], 11⟩ := by
  have hpre : Holds firstSubgroup PresentedGroup.of representative ⟨11, [(false, true)], 15⟩ :=
    edge14
  have hsuf : Holds firstSubgroup PresentedGroup.of representative ⟨11, [], 11⟩ :=
    (holds_refl 11)
  exact scanFacts hpre hsuf (holds_relator 11 (relatorLetters 0) (presentation_relator 0))

private theorem edge33Inv : Holds firstSubgroup PresentedGroup.of representative ⟨11, [(false, false)], 15⟩ :=
  holds_reverse edge33

-- Trace event 34: ['scan', 14, ['rel', 1], 1, 16, 2, 17].
private theorem edge34 : Holds firstSubgroup PresentedGroup.of representative ⟨16, [(true, true)], 17⟩ := by
  have hpre : Holds firstSubgroup PresentedGroup.of representative ⟨14, [(true, true)], 16⟩ :=
    edge15
  have hsuf : Holds firstSubgroup PresentedGroup.of representative ⟨17, [(true, true)], 14⟩ :=
    edge16Inv
  exact scanFacts hpre hsuf (holds_relator 14 (relatorLetters 1) (presentation_relator 1))

private theorem edge34Inv : Holds firstSubgroup PresentedGroup.of representative ⟨17, [(true, false)], 16⟩ :=
  holds_reverse edge34

-- Trace event 35: ['scan', 16, ['rel', 0], 1, 18, 1, 16].
private theorem edge35 : Holds firstSubgroup PresentedGroup.of representative ⟨18, [(false, true)], 16⟩ := by
  have hpre : Holds firstSubgroup PresentedGroup.of representative ⟨16, [(false, true)], 18⟩ :=
    edge17
  have hsuf : Holds firstSubgroup PresentedGroup.of representative ⟨16, [], 16⟩ :=
    (holds_refl 16)
  exact scanFacts hpre hsuf (holds_relator 16 (relatorLetters 0) (presentation_relator 0))

private theorem edge35Inv : Holds firstSubgroup PresentedGroup.of representative ⟨16, [(false, false)], 18⟩ :=
  holds_reverse edge35

-- Trace event 36: ['scan', 17, ['rel', 0], 1, 19, 1, 17].
private theorem edge36 : Holds firstSubgroup PresentedGroup.of representative ⟨19, [(false, true)], 17⟩ := by
  have hpre : Holds firstSubgroup PresentedGroup.of representative ⟨17, [(false, true)], 19⟩ :=
    edge18
  have hsuf : Holds firstSubgroup PresentedGroup.of representative ⟨17, [], 17⟩ :=
    (holds_refl 17)
  exact scanFacts hpre hsuf (holds_relator 17 (relatorLetters 0) (presentation_relator 0))

private theorem edge36Inv : Holds firstSubgroup PresentedGroup.of representative ⟨17, [(false, false)], 19⟩ :=
  holds_reverse edge36

-- Trace event 37: ['scan', 18, ['rel', 1], 1, 20, 2, 21].
private theorem edge37 : Holds firstSubgroup PresentedGroup.of representative ⟨20, [(true, true)], 21⟩ := by
  have hpre : Holds firstSubgroup PresentedGroup.of representative ⟨18, [(true, true)], 20⟩ :=
    edge19
  have hsuf : Holds firstSubgroup PresentedGroup.of representative ⟨21, [(true, true)], 18⟩ :=
    edge20Inv
  exact scanFacts hpre hsuf (holds_relator 18 (relatorLetters 1) (presentation_relator 1))

private theorem edge37Inv : Holds firstSubgroup PresentedGroup.of representative ⟨21, [(true, false)], 20⟩ :=
  holds_reverse edge37

-- Trace event 38: ['scan', 19, ['rel', 1], 1, 22, 2, 23].
private theorem edge38 : Holds firstSubgroup PresentedGroup.of representative ⟨22, [(true, true)], 23⟩ := by
  have hpre : Holds firstSubgroup PresentedGroup.of representative ⟨19, [(true, true)], 22⟩ :=
    edge21
  have hsuf : Holds firstSubgroup PresentedGroup.of representative ⟨23, [(true, true)], 19⟩ :=
    edge22Inv
  exact scanFacts hpre hsuf (holds_relator 19 (relatorLetters 1) (presentation_relator 1))

private theorem edge38Inv : Holds firstSubgroup PresentedGroup.of representative ⟨23, [(true, false)], 22⟩ :=
  holds_reverse edge38

-- Trace event 39: ['scan', 0, ['sub', 0], 1, 1, 2, 0].
private theorem edge39 : Holds firstSubgroup PresentedGroup.of representative ⟨1, [(true, true)], 0⟩ := by
  have hpre : Holds firstSubgroup PresentedGroup.of representative ⟨0, [(false, true)], 1⟩ :=
    edge00
  have hsuf : Holds firstSubgroup PresentedGroup.of representative ⟨0, [], 0⟩ :=
    (holds_refl 0)
  exact scanFacts hpre hsuf (show Holds firstSubgroup PresentedGroup.of representative
      ⟨0, subgroupWord 0, 0⟩ from
        ⟨⟨subgroupGenerator 0, subgroupGenerator_mem 0⟩,
          by change 1 * subgroupGenerator 0 = subgroupGenerator 0 * 1; simp⟩)

private theorem edge39Inv : Holds firstSubgroup PresentedGroup.of representative ⟨0, [(true, false)], 1⟩ :=
  holds_reverse edge39

-- Trace event 40: ['scan', 0, ['rel', 1], 1, 2, 2, 1].
private theorem edge40 : Holds firstSubgroup PresentedGroup.of representative ⟨2, [(true, true)], 1⟩ := by
  have hpre : Holds firstSubgroup PresentedGroup.of representative ⟨0, [(true, true)], 2⟩ :=
    edge01
  have hsuf : Holds firstSubgroup PresentedGroup.of representative ⟨1, [(true, true)], 0⟩ :=
    edge39
  exact scanFacts hpre hsuf (holds_relator 0 (relatorLetters 1) (presentation_relator 1))

private theorem edge40Inv : Holds firstSubgroup PresentedGroup.of representative ⟨1, [(true, false)], 2⟩ :=
  holds_reverse edge40

-- Trace event 41: ['scan', 0, ['sub', 1], 6, 15, 2, 13].
private theorem edge41 : Holds firstSubgroup PresentedGroup.of representative ⟨15, [(true, true)], 13⟩ := by
  have hpre : Holds firstSubgroup PresentedGroup.of representative ⟨0, [(true, true), (false, true), (true,
    false), (false, true), (true, false), (false, true)], 15⟩ :=
    (appendFacts (appendFacts edge01 (appendFacts edge02 edge04)) (appendFacts edge06 (appendFacts edge10
      edge14)))
  have hsuf : Holds firstSubgroup PresentedGroup.of representative ⟨13, [(false, true), (true, true), (false,
    true), (false, true), (false, true), (true, true), (true, true), (false, true), (true, true), (false,
    true), (false, true), (true, true), (false, true), (false, true)], 0⟩ :=
    (appendFacts (appendFacts (appendFacts edge31 (appendFacts edge08Inv edge26)) (appendFacts (appendFacts
      edge05 edge26) (appendFacts edge25 edge04Inv))) (appendFacts (appendFacts edge24 (appendFacts edge40
      edge23)) (appendFacts (appendFacts edge00 edge39) (appendFacts edge00 edge23))))
  exact scanFacts hpre hsuf (show Holds firstSubgroup PresentedGroup.of representative
      ⟨0, subgroupWord 1, 0⟩ from
        ⟨⟨subgroupGenerator 1, subgroupGenerator_mem 1⟩,
          by change 1 * subgroupGenerator 1 = subgroupGenerator 1 * 1; simp⟩)

private theorem edge41Inv : Holds firstSubgroup PresentedGroup.of representative ⟨13, [(true, false)], 15⟩ :=
  holds_reverse edge41

-- Trace event 42: ['scan', 0, ['sub', 2], 22, 13, 2, 12].
private theorem edge42 : Holds firstSubgroup PresentedGroup.of representative ⟨13, [(true, true)], 12⟩ := by
  have hpre : Holds firstSubgroup PresentedGroup.of representative ⟨0, [(true, false), (false, true), (true,
    true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false,
    true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true,
    true), (false, true), (true, true), (false, true), (true, false), (false, true)], 13⟩ :=
    (appendFacts (appendFacts (appendFacts (appendFacts edge39Inv edge23) (appendFacts edge01 (appendFacts
      edge02 edge04))) (appendFacts (appendFacts edge06 (appendFacts edge10 edge14)) (appendFacts edge41
      (appendFacts edge31 edge08Inv)))) (appendFacts (appendFacts (appendFacts edge26 edge03Inv) (appendFacts
      edge24 (appendFacts edge40 edge23))) (appendFacts (appendFacts edge01 (appendFacts edge02 edge03))
      (appendFacts edge05 (appendFacts edge08 edge12)))))
  have hsuf : Holds firstSubgroup PresentedGroup.of representative ⟨12, [(false, true), (true, true), (true,
    true), (false, true), (true, true), (true, true), (false, true), (true, true), (false, true), (false,
    true), (true, true), (false, true), (true, true), (false, true), (true, true)], 0⟩ :=
    (appendFacts (appendFacts (appendFacts edge30 (appendFacts edge28 edge08Inv)) (appendFacts (appendFacts
      edge26 edge25) (appendFacts edge04Inv edge24))) (appendFacts (appendFacts (appendFacts edge40 edge23)
      (appendFacts edge00 edge39)) (appendFacts (appendFacts edge00 edge39) (appendFacts edge00 edge39))))
  exact scanFacts hpre hsuf (show Holds firstSubgroup PresentedGroup.of representative
      ⟨0, subgroupWord 2, 0⟩ from
        ⟨⟨subgroupGenerator 2, subgroupGenerator_mem 2⟩,
          by change 1 * subgroupGenerator 2 = subgroupGenerator 2 * 1; simp⟩)

private theorem edge42Inv : Holds firstSubgroup PresentedGroup.of representative ⟨12, [(true, false)], 13⟩ :=
  holds_reverse edge42

-- Trace event 43: ['scan', 0, ['rel', 5], 49, 12, 2, 15].
private theorem edge43 : Holds firstSubgroup PresentedGroup.of representative ⟨12, [(true, true)], 15⟩ := by
  have hpre : Holds firstSubgroup PresentedGroup.of representative ⟨0, [(false, true), (true, true), (false,
    true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true,
    true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false,
    true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true,
    true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false,
    true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true,
    false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false,
    true), (true, true), (false, true), (true, false), (false, true)], 12⟩ :=
    (appendFacts (appendFacts (appendFacts (appendFacts (appendFacts edge00 (appendFacts edge39 edge00))
      (appendFacts edge40Inv (appendFacts edge02 edge03))) (appendFacts (appendFacts edge05 (appendFacts
      edge08 edge12)) (appendFacts edge42 (appendFacts edge30 edge28)))) (appendFacts (appendFacts
      (appendFacts edge12 (appendFacts edge42 edge30)) (appendFacts edge28 (appendFacts edge12 edge42)))
      (appendFacts (appendFacts edge30 (appendFacts edge07Inv edge26)) (appendFacts edge03Inv (appendFacts
      edge24 edge40))))) (appendFacts (appendFacts (appendFacts (appendFacts edge23 (appendFacts edge01
      edge02)) (appendFacts edge03 (appendFacts edge05 edge07))) (appendFacts (appendFacts edge11 (appendFacts
      edge42Inv edge31)) (appendFacts edge08Inv (appendFacts edge26 edge03Inv)))) (appendFacts (appendFacts
      (appendFacts edge24 (appendFacts edge01Inv edge00)) (appendFacts edge40Inv (appendFacts edge02 edge04)))
      (appendFacts (appendFacts edge06 (appendFacts edge10 edge14)) (appendFacts (appendFacts edge41 edge31)
      (appendFacts edge28Inv edge11))))))
  have hsuf : Holds firstSubgroup PresentedGroup.of representative ⟨15, [(false, true), (true, true), (false,
    true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true,
    true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false,
    true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true,
    false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false,
    true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true,
    false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false,
    true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true,
    true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false,
    true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true,
    false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false,
    true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true,
    true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false,
    true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true,
    false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false,
    true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true,
    true)], 0⟩ :=
    (appendFacts (appendFacts (appendFacts (appendFacts (appendFacts (appendFacts edge33 (appendFacts
      edge10Inv edge27)) (appendFacts edge04Inv (appendFacts edge24 edge40))) (appendFacts (appendFacts edge23
      (appendFacts edge39Inv edge23)) (appendFacts (appendFacts edge01 edge02) (appendFacts edge03 edge05))))
      (appendFacts (appendFacts (appendFacts edge08 (appendFacts edge12 edge41Inv)) (appendFacts (appendFacts
      edge33 edge10Inv) (appendFacts edge27 edge04Inv))) (appendFacts (appendFacts edge24 (appendFacts edge40
      edge23)) (appendFacts (appendFacts edge39Inv edge23) (appendFacts edge39Inv edge23))))) (appendFacts
      (appendFacts (appendFacts (appendFacts edge01 (appendFacts edge02 edge03)) (appendFacts edge05
      (appendFacts edge08 edge12))) (appendFacts (appendFacts edge41Inv (appendFacts edge33 edge10Inv))
      (appendFacts (appendFacts edge27 edge25Inv) (appendFacts edge05 edge08)))) (appendFacts (appendFacts
      (appendFacts edge12 (appendFacts edge41Inv edge33)) (appendFacts (appendFacts edge10Inv edge27)
      (appendFacts edge04Inv edge24))) (appendFacts (appendFacts edge40 (appendFacts edge23 edge39Inv))
      (appendFacts (appendFacts edge23 edge01) (appendFacts edge02 edge03)))))) (appendFacts (appendFacts
      (appendFacts (appendFacts (appendFacts edge05 (appendFacts edge07 edge11)) (appendFacts edge42Inv
      (appendFacts edge31 edge08Inv))) (appendFacts (appendFacts edge26 (appendFacts edge03Inv edge24))
      (appendFacts (appendFacts edge01Inv edge00) (appendFacts edge40Inv edge02)))) (appendFacts (appendFacts
      (appendFacts edge03 (appendFacts edge05 edge08)) (appendFacts (appendFacts edge12 edge41Inv)
      (appendFacts edge33 edge10Inv))) (appendFacts (appendFacts edge27 (appendFacts edge04Inv edge24))
      (appendFacts (appendFacts edge40 edge23) (appendFacts edge01 edge02))))) (appendFacts (appendFacts
      (appendFacts (appendFacts edge03 (appendFacts edge05 edge07)) (appendFacts edge11 (appendFacts edge42Inv
      edge31))) (appendFacts (appendFacts edge08Inv (appendFacts edge26 edge03Inv)) (appendFacts (appendFacts
      edge24 edge01Inv) (appendFacts edge00 edge40Inv)))) (appendFacts (appendFacts (appendFacts edge02
      (appendFacts edge03 edge05)) (appendFacts (appendFacts edge08 edge12) (appendFacts edge41Inv edge33)))
      (appendFacts (appendFacts edge10Inv (appendFacts edge27 edge04Inv)) (appendFacts (appendFacts edge24
      edge01Inv) (appendFacts edge00 edge39)))))))
  exact scanFacts hpre hsuf (holds_relator 0 (relatorLetters 5) (presentation_relator 5))

private theorem edge43Inv : Holds firstSubgroup PresentedGroup.of representative ⟨15, [(true, false)], 12⟩ :=
  holds_reverse edge43

-- Trace event 44: ['scan', 0, ['sub', 5], 17, 23, -1, 21].
private theorem edge44 : Holds firstSubgroup PresentedGroup.of representative ⟨23, [(false, false)], 21⟩ := by
  have hpre : Holds firstSubgroup PresentedGroup.of representative ⟨0, [(true, true), (false, true), (true,
    true), (false, true), (true, true), (false, false), (true, false), (false, false), (true, false), (false,
    false), (true, true), (false, false), (true, false), (false, false), (true, false), (false, false), (true,
    false)], 23⟩ :=
    (appendFacts (appendFacts (appendFacts (appendFacts edge01 edge02) (appendFacts edge03 edge05))
      (appendFacts (appendFacts edge07 edge30Inv) (appendFacts edge42Inv edge12Inv))) (appendFacts
      (appendFacts (appendFacts edge28Inv edge30Inv) (appendFacts edge43 edge14Inv)) (appendFacts (appendFacts
      edge29Inv edge32Inv) (appendFacts edge16 (appendFacts edge36Inv edge22)))))
  have hsuf : Holds firstSubgroup PresentedGroup.of representative ⟨21, [(true, true), (false, false), (true,
    false), (false, false), (true, false), (false, false), (true, true), (false, false), (true, false), (true,
    false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false,
    true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true,
    false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false,
    true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true,
    true), (false, true), (true, false), (false, true), (false, true), (false, true), (true, true), (false,
    true), (true, true), (true, true), (false, true), (true, true), (true, true), (false, true), (true, true),
    (false, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true)], 0⟩
    :=
    (appendFacts (appendFacts (appendFacts (appendFacts (appendFacts edge20Inv (appendFacts edge17Inv
      edge15Inv)) (appendFacts (appendFacts edge13Inv edge09Inv) (appendFacts edge06Inv edge04Inv)))
      (appendFacts (appendFacts edge02Inv (appendFacts edge01Inv edge39Inv)) (appendFacts (appendFacts edge23
      edge39Inv) (appendFacts edge23 edge39Inv)))) (appendFacts (appendFacts (appendFacts edge23 (appendFacts
      edge39Inv edge23)) (appendFacts (appendFacts edge39Inv edge23) (appendFacts edge39Inv edge23)))
      (appendFacts (appendFacts (appendFacts edge01 edge02) (appendFacts edge04 edge06)) (appendFacts
      (appendFacts edge10 edge14) (appendFacts edge41 edge31))))) (appendFacts (appendFacts (appendFacts
      (appendFacts edge08Inv (appendFacts edge26 edge03Inv)) (appendFacts (appendFacts edge24 edge40)
      (appendFacts edge23 edge01))) (appendFacts (appendFacts (appendFacts edge02 edge03) (appendFacts edge05
      edge08)) (appendFacts (appendFacts edge12 edge31) (appendFacts edge12 edge42)))) (appendFacts
      (appendFacts (appendFacts edge30 (appendFacts edge28 edge08Inv)) (appendFacts (appendFacts edge26
      edge25) (appendFacts edge04Inv edge24))) (appendFacts (appendFacts (appendFacts edge40 edge23)
      (appendFacts edge00 edge39)) (appendFacts (appendFacts edge00 edge39) (appendFacts edge00 edge39))))))
  exact scanFacts hpre hsuf (show Holds firstSubgroup PresentedGroup.of representative
      ⟨0, subgroupWord 5, 0⟩ from
        ⟨⟨subgroupGenerator 5, subgroupGenerator_mem 5⟩,
          by change 1 * subgroupGenerator 5 = subgroupGenerator 5 * 1; simp⟩)

private theorem edge44Inv : Holds firstSubgroup PresentedGroup.of representative ⟨21, [(false, true)], 23⟩ :=
  holds_reverse edge44

-- Trace event 45: ['scan', 0, ['rel', 36], 97, 23, 1, 21].
private theorem edge45 : Holds firstSubgroup PresentedGroup.of representative ⟨23, [(false, true)], 21⟩ := by
  have hpre : Holds firstSubgroup PresentedGroup.of representative ⟨0, [(true, true), (false, true), (true,
    true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false,
    true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true,
    true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false,
    true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true,
    true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false,
    true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true,
    true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false,
    true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true,
    true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false,
    true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true,
    false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false,
    true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true,
    false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false,
    true), (true, false), (false, true), (true, false)], 23⟩ :=
    (appendFacts (appendFacts (appendFacts (appendFacts (appendFacts (appendFacts edge01 (appendFacts edge02
      edge03)) (appendFacts edge05 (appendFacts edge07 edge11))) (appendFacts (appendFacts edge42Inv
      (appendFacts edge31 edge08Inv)) (appendFacts edge26 (appendFacts edge03Inv edge24)))) (appendFacts
      (appendFacts (appendFacts edge01Inv (appendFacts edge00 edge40Inv)) (appendFacts edge02 (appendFacts
      edge03 edge05))) (appendFacts (appendFacts edge08 (appendFacts edge12 edge41Inv)) (appendFacts edge33
      (appendFacts edge10Inv edge27))))) (appendFacts (appendFacts (appendFacts (appendFacts edge04Inv
      (appendFacts edge24 edge01Inv)) (appendFacts edge00 (appendFacts edge39 edge00))) (appendFacts
      (appendFacts edge39 (appendFacts edge00 edge39)) (appendFacts edge00 (appendFacts edge39 edge00))))
      (appendFacts (appendFacts (appendFacts edge39 (appendFacts edge00 edge40Inv)) (appendFacts edge02
      (appendFacts edge04 edge06))) (appendFacts (appendFacts edge09 (appendFacts edge13 edge15)) (appendFacts
      edge17 (appendFacts edge20 edge44Inv)))))) (appendFacts (appendFacts (appendFacts (appendFacts
      (appendFacts edge22Inv (appendFacts edge36 edge16Inv)) (appendFacts edge32 (appendFacts edge29 edge14)))
      (appendFacts (appendFacts edge43Inv (appendFacts edge30 edge28)) (appendFacts edge12 (appendFacts edge42
      edge30)))) (appendFacts (appendFacts (appendFacts edge07Inv (appendFacts edge26 edge03Inv)) (appendFacts
      edge24 (appendFacts edge01Inv edge00))) (appendFacts (appendFacts edge40Inv (appendFacts edge02 edge03))
      (appendFacts edge05 (appendFacts edge07 edge11))))) (appendFacts (appendFacts (appendFacts (appendFacts
      edge42Inv (appendFacts edge31 edge08Inv)) (appendFacts edge26 (appendFacts edge03Inv edge24)))
      (appendFacts (appendFacts edge40 (appendFacts edge23 edge01)) (appendFacts edge02 (appendFacts edge03
      edge05)))) (appendFacts (appendFacts (appendFacts edge07 (appendFacts edge11 edge42Inv)) (appendFacts
      edge31 (appendFacts edge28Inv edge11))) (appendFacts (appendFacts edge43 (appendFacts edge33 edge29Inv))
      (appendFacts (appendFacts edge13 edge16) (appendFacts edge18 edge22)))))))
  have hsuf : Holds firstSubgroup PresentedGroup.of representative ⟨21, [(true, true), (false, true), (true,
    false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false,
    true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true,
    false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false,
    true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true,
    false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false,
    true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true,
    false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false,
    true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true,
    false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false,
    true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true,
    false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false,
    true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true,
    false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false,
    true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true,
    false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false,
    true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true,
    false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false,
    true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true,
    false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false,
    true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true,
    true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false,
    true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true,
    true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false,
    true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true,
    true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false,
    true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true,
    true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false,
    true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true,
    true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false,
    true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true,
    true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false,
    true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true,
    true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false,
    true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true,
    true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false,
    true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true,
    false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false,
    true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true,
    true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false,
    true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true,
    false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false,
    true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true,
    false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false,
    true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true,
    true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false,
    true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true,
    false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false,
    true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true,
    true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false,
    true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true,
    true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false,
    true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true,
    false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false,
    true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true,
    false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false,
    true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true,
    true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false,
    true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true,
    false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false,
    true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true,
    false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false,
    true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true,
    false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false,
    true), (true, true), (false, true)], 0⟩ :=
    (appendFacts (appendFacts (appendFacts (appendFacts (appendFacts (appendFacts (appendFacts (appendFacts
      edge20Inv (appendFacts edge35 edge15Inv)) (appendFacts edge32 (appendFacts edge09Inv edge27)))
      (appendFacts (appendFacts edge04Inv (appendFacts edge24 edge40)) (appendFacts (appendFacts edge23
      edge39Inv) (appendFacts edge23 edge39Inv)))) (appendFacts (appendFacts (appendFacts edge23 (appendFacts
      edge39Inv edge23)) (appendFacts (appendFacts edge39Inv edge23) (appendFacts edge39Inv edge23)))
      (appendFacts (appendFacts edge01 (appendFacts edge02 edge04)) (appendFacts (appendFacts edge06 edge10)
      (appendFacts edge14 edge41))))) (appendFacts (appendFacts (appendFacts (appendFacts edge31 (appendFacts
      edge08Inv edge26)) (appendFacts (appendFacts edge03Inv edge24) (appendFacts edge40 edge23)))
      (appendFacts (appendFacts edge01 (appendFacts edge02 edge03)) (appendFacts (appendFacts edge05 edge08)
      (appendFacts edge12 edge42)))) (appendFacts (appendFacts (appendFacts edge30 (appendFacts edge07Inv
      edge26)) (appendFacts (appendFacts edge03Inv edge24) (appendFacts edge01Inv edge00))) (appendFacts
      (appendFacts edge40Inv (appendFacts edge02 edge04)) (appendFacts (appendFacts edge06 edge10)
      (appendFacts edge14 edge41)))))) (appendFacts (appendFacts (appendFacts (appendFacts (appendFacts edge31
      (appendFacts edge08Inv edge26)) (appendFacts (appendFacts edge03Inv edge24) (appendFacts edge40
      edge23))) (appendFacts (appendFacts edge01 (appendFacts edge02 edge03)) (appendFacts (appendFacts edge05
      edge08) (appendFacts edge12 edge42)))) (appendFacts (appendFacts (appendFacts edge30 (appendFacts
      edge07Inv edge26)) (appendFacts (appendFacts edge03Inv edge24) (appendFacts edge01Inv edge00)))
      (appendFacts (appendFacts edge39 (appendFacts edge00 edge39)) (appendFacts (appendFacts edge00 edge39)
      (appendFacts edge00 edge40Inv))))) (appendFacts (appendFacts (appendFacts (appendFacts edge02
      (appendFacts edge03 edge05)) (appendFacts (appendFacts edge08 edge12) (appendFacts edge42 edge30)))
      (appendFacts (appendFacts edge28 (appendFacts edge12 edge42)) (appendFacts (appendFacts edge30 edge28)
      (appendFacts edge12 edge42)))) (appendFacts (appendFacts (appendFacts edge30 (appendFacts edge07Inv
      edge26)) (appendFacts (appendFacts edge03Inv edge24) (appendFacts edge40 edge23))) (appendFacts
      (appendFacts edge01 (appendFacts edge02 edge03)) (appendFacts (appendFacts edge05 edge07) (appendFacts
      edge11 edge42Inv))))))) (appendFacts (appendFacts (appendFacts (appendFacts (appendFacts (appendFacts
      edge31 (appendFacts edge08Inv edge26)) (appendFacts (appendFacts edge03Inv edge24) (appendFacts
      edge01Inv edge00))) (appendFacts (appendFacts edge39 (appendFacts edge00 edge40Inv)) (appendFacts
      (appendFacts edge02 edge04) (appendFacts edge06 edge09)))) (appendFacts (appendFacts (appendFacts edge13
      (appendFacts edge15 edge17)) (appendFacts (appendFacts edge20 edge44Inv) (appendFacts edge22Inv
      edge36))) (appendFacts (appendFacts edge34Inv (appendFacts edge17 edge20)) (appendFacts (appendFacts
      edge44Inv edge22Inv) (appendFacts edge36 edge16Inv))))) (appendFacts (appendFacts (appendFacts
      (appendFacts edge32 (appendFacts edge09Inv edge27)) (appendFacts (appendFacts edge04Inv edge24)
      (appendFacts edge01Inv edge00))) (appendFacts (appendFacts edge40Inv (appendFacts edge02 edge03))
      (appendFacts (appendFacts edge05 edge08) (appendFacts edge12 edge41Inv)))) (appendFacts (appendFacts
      (appendFacts edge33 (appendFacts edge10Inv edge27)) (appendFacts (appendFacts edge04Inv edge24)
      (appendFacts edge01Inv edge00))) (appendFacts (appendFacts edge40Inv (appendFacts edge02 edge03))
      (appendFacts (appendFacts edge05 edge08) (appendFacts edge12 edge42)))))) (appendFacts (appendFacts
      (appendFacts (appendFacts (appendFacts edge30 (appendFacts edge07Inv edge26)) (appendFacts (appendFacts
      edge25 edge06) (appendFacts edge10 edge14))) (appendFacts (appendFacts edge41 (appendFacts edge31
      edge08Inv)) (appendFacts (appendFacts edge26 edge03Inv) (appendFacts edge24 edge01Inv)))) (appendFacts
      (appendFacts (appendFacts edge00 (appendFacts edge40Inv edge02)) (appendFacts (appendFacts edge03
      edge05) (appendFacts edge08 edge12))) (appendFacts (appendFacts edge41Inv (appendFacts edge33
      edge10Inv)) (appendFacts (appendFacts edge27 edge04Inv) (appendFacts edge24 edge01Inv))))) (appendFacts
      (appendFacts (appendFacts (appendFacts edge00 (appendFacts edge39 edge00)) (appendFacts (appendFacts
      edge39 edge00) (appendFacts edge39 edge00))) (appendFacts (appendFacts edge39 (appendFacts edge00
      edge39)) (appendFacts (appendFacts edge00 edge40Inv) (appendFacts edge02 edge04)))) (appendFacts
      (appendFacts (appendFacts edge06 (appendFacts edge09 edge13)) (appendFacts (appendFacts edge15 edge17)
      (appendFacts edge20 edge44Inv))) (appendFacts (appendFacts edge22Inv (appendFacts edge36 edge16Inv))
      (appendFacts (appendFacts edge32 edge29) (appendFacts edge14 edge43Inv)))))))) (appendFacts (appendFacts
      (appendFacts (appendFacts (appendFacts (appendFacts (appendFacts edge30 (appendFacts edge28 edge12))
      (appendFacts edge42 (appendFacts edge30 edge07Inv))) (appendFacts (appendFacts edge26 (appendFacts
      edge03Inv edge24)) (appendFacts (appendFacts edge40 edge23) (appendFacts edge39Inv edge23))))
      (appendFacts (appendFacts (appendFacts edge01 (appendFacts edge02 edge03)) (appendFacts (appendFacts
      edge05 edge07) (appendFacts edge11 edge42Inv))) (appendFacts (appendFacts edge31 (appendFacts edge08Inv
      edge26)) (appendFacts (appendFacts edge03Inv edge24) (appendFacts edge01Inv edge00))))) (appendFacts
      (appendFacts (appendFacts (appendFacts edge40Inv (appendFacts edge02 edge03)) (appendFacts (appendFacts
      edge05 edge08) (appendFacts edge12 edge41Inv))) (appendFacts (appendFacts edge33 (appendFacts edge10Inv
      edge27)) (appendFacts (appendFacts edge04Inv edge24) (appendFacts edge01Inv edge00)))) (appendFacts
      (appendFacts (appendFacts edge39 (appendFacts edge00 edge39)) (appendFacts (appendFacts edge00 edge39)
      (appendFacts edge00 edge39))) (appendFacts (appendFacts edge00 (appendFacts edge39 edge00)) (appendFacts
      (appendFacts edge40Inv edge02) (appendFacts edge04 edge06)))))) (appendFacts (appendFacts (appendFacts
      (appendFacts (appendFacts edge09 (appendFacts edge13 edge15)) (appendFacts (appendFacts edge17 edge20)
      (appendFacts edge44Inv edge22Inv))) (appendFacts (appendFacts edge36 (appendFacts edge16Inv edge32))
      (appendFacts (appendFacts edge29 edge14) (appendFacts edge43Inv edge30)))) (appendFacts (appendFacts
      (appendFacts edge28 (appendFacts edge12 edge42)) (appendFacts (appendFacts edge30 edge07Inv)
      (appendFacts edge26 edge25))) (appendFacts (appendFacts edge06 (appendFacts edge10 edge14)) (appendFacts
      (appendFacts edge41 edge31) (appendFacts edge08Inv edge26))))) (appendFacts (appendFacts (appendFacts
      (appendFacts edge03Inv (appendFacts edge24 edge40)) (appendFacts (appendFacts edge23 edge01)
      (appendFacts edge02 edge03))) (appendFacts (appendFacts edge05 (appendFacts edge08 edge12)) (appendFacts
      (appendFacts edge42 edge30) (appendFacts edge07Inv edge26)))) (appendFacts (appendFacts (appendFacts
      edge03Inv (appendFacts edge24 edge01Inv)) (appendFacts (appendFacts edge00 edge40Inv) (appendFacts
      edge02 edge04))) (appendFacts (appendFacts edge06 (appendFacts edge10 edge14)) (appendFacts (appendFacts
      edge41 edge31) (appendFacts edge08Inv edge26))))))) (appendFacts (appendFacts (appendFacts (appendFacts
      (appendFacts (appendFacts edge03Inv (appendFacts edge24 edge40)) (appendFacts (appendFacts edge23
      edge01) (appendFacts edge02 edge03))) (appendFacts (appendFacts edge05 (appendFacts edge08 edge12))
      (appendFacts (appendFacts edge42 edge30) (appendFacts edge07Inv edge26)))) (appendFacts (appendFacts
      (appendFacts edge03Inv (appendFacts edge24 edge01Inv)) (appendFacts (appendFacts edge00 edge39)
      (appendFacts edge00 edge40Inv))) (appendFacts (appendFacts edge02 (appendFacts edge03 edge05))
      (appendFacts (appendFacts edge08 edge12) (appendFacts edge42 edge30))))) (appendFacts (appendFacts
      (appendFacts (appendFacts edge07Inv (appendFacts edge26 edge03Inv)) (appendFacts (appendFacts edge24
      edge01Inv) (appendFacts edge00 edge40Inv))) (appendFacts (appendFacts edge02 (appendFacts edge03
      edge05)) (appendFacts (appendFacts edge07 edge11) (appendFacts edge42Inv edge31)))) (appendFacts
      (appendFacts (appendFacts edge28Inv (appendFacts edge11 edge42Inv)) (appendFacts (appendFacts edge31
      edge28Inv) (appendFacts edge11 edge42Inv))) (appendFacts (appendFacts edge31 (appendFacts edge08Inv
      edge26)) (appendFacts (appendFacts edge25 edge06) (appendFacts edge09 edge13)))))) (appendFacts
      (appendFacts (appendFacts (appendFacts (appendFacts edge15 (appendFacts edge17 edge20)) (appendFacts
      (appendFacts edge44Inv edge22Inv) (appendFacts edge36 edge34Inv))) (appendFacts (appendFacts edge17
      (appendFacts edge20 edge44Inv)) (appendFacts (appendFacts edge22Inv edge36) (appendFacts edge16Inv
      edge32)))) (appendFacts (appendFacts (appendFacts edge09Inv (appendFacts edge27 edge04Inv)) (appendFacts
      (appendFacts edge24 edge01Inv) (appendFacts edge00 edge40Inv))) (appendFacts (appendFacts edge02
      (appendFacts edge03 edge05)) (appendFacts (appendFacts edge08 edge12) (appendFacts edge41Inv edge33)))))
      (appendFacts (appendFacts (appendFacts (appendFacts edge10Inv (appendFacts edge27 edge04Inv))
      (appendFacts (appendFacts edge24 edge01Inv) (appendFacts edge00 edge40Inv))) (appendFacts (appendFacts
      edge02 (appendFacts edge03 edge05)) (appendFacts (appendFacts edge08 edge12) (appendFacts edge42
      edge30)))) (appendFacts (appendFacts (appendFacts edge07Inv (appendFacts edge26 edge25)) (appendFacts
      (appendFacts edge06 edge10) (appendFacts edge14 edge43Inv))) (appendFacts (appendFacts edge30
      (appendFacts edge07Inv edge26)) (appendFacts (appendFacts edge03Inv edge24) (appendFacts edge40
      edge23)))))))))
  exact scanFacts hpre hsuf (holds_relator 0 (relatorLetters 36) (presentation_relator 36))

private theorem edge45Inv : Holds firstSubgroup PresentedGroup.of representative ⟨21, [(false, false)], 23⟩ :=
  holds_reverse edge45

-- Trace event 46: ['scan', 2, ['rel', 44], 657, 22, 1, 20].
private theorem edge46 : Holds firstSubgroup PresentedGroup.of representative ⟨22, [(false, true)], 20⟩ := by
  have hpre : Holds firstSubgroup PresentedGroup.of representative ⟨2, [(true, true), (false, true), (true,
    false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false,
    true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true,
    false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false,
    true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true,
    true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false,
    true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true,
    false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false,
    true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true,
    true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false,
    true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true,
    false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false,
    true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true,
    false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false,
    true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true,
    false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false,
    true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true,
    false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false,
    true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true,
    false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false,
    true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true,
    true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false,
    true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true,
    true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false,
    true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true,
    false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false,
    true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true,
    false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false,
    true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true,
    true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false,
    true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true,
    true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false,
    true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true,
    true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false,
    true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true,
    false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false,
    true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true,
    true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false,
    true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true,
    true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false,
    true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true,
    true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false,
    true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true,
    false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false,
    true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true,
    false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false,
    true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true,
    false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false,
    true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true,
    false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false,
    true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true,
    false), (false, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false,
    true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true,
    true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false,
    true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true,
    true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false,
    true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true,
    true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false,
    true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true,
    true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false,
    true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true,
    true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false,
    true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true,
    true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false,
    true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true,
    true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false,
    true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true,
    true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false,
    true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true,
    true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false,
    true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true,
    true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false,
    true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true,
    true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false,
    true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true,
    true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false), (false,
    true), (true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true,
    true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false,
    true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true,
    true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false,
    true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true,
    false), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true), (false,
    true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true,
    true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false,
    true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (true,
    true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (false,
    true), (true, false), (false, true), (true, true), (false, true), (true, true), (false, true), (true,
    false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false,
    true), (true, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true,
    true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false,
    true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true,
    false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, false), (false,
    true), (true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true,
    true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false,
    true), (true, false), (false, true), (true, true)], 22⟩ :=
    (appendFacts (appendFacts (appendFacts (appendFacts (appendFacts (appendFacts (appendFacts (appendFacts
      (appendFacts edge40 edge23) (appendFacts edge39Inv (appendFacts edge23 edge39Inv))) (appendFacts
      (appendFacts edge23 edge01) (appendFacts edge02 (appendFacts edge03 edge05)))) (appendFacts (appendFacts
      (appendFacts edge07 edge11) (appendFacts edge42Inv (appendFacts edge31 edge08Inv))) (appendFacts
      (appendFacts edge26 edge03Inv) (appendFacts edge24 (appendFacts edge01Inv edge00))))) (appendFacts
      (appendFacts (appendFacts (appendFacts edge40Inv edge02) (appendFacts edge03 (appendFacts edge05
      edge08))) (appendFacts (appendFacts edge12 edge41Inv) (appendFacts edge33 (appendFacts edge10Inv
      edge27)))) (appendFacts (appendFacts (appendFacts edge04Inv edge24) (appendFacts edge01Inv (appendFacts
      edge00 edge39))) (appendFacts (appendFacts edge00 (appendFacts edge39 edge00)) (appendFacts edge39
      (appendFacts edge00 edge39)))))) (appendFacts (appendFacts (appendFacts (appendFacts (appendFacts edge00
      edge39) (appendFacts edge00 (appendFacts edge40Inv edge02))) (appendFacts (appendFacts edge04 edge06)
      (appendFacts edge09 (appendFacts edge13 edge15)))) (appendFacts (appendFacts (appendFacts edge17 edge20)
      (appendFacts edge44Inv (appendFacts edge22Inv edge36))) (appendFacts (appendFacts edge16Inv edge32)
      (appendFacts edge29 (appendFacts edge14 edge43Inv))))) (appendFacts (appendFacts (appendFacts
      (appendFacts edge30 edge28) (appendFacts edge12 (appendFacts edge42 edge30))) (appendFacts (appendFacts
      edge07Inv edge26) (appendFacts edge03Inv (appendFacts edge24 edge01Inv)))) (appendFacts (appendFacts
      (appendFacts edge00 edge40Inv) (appendFacts edge02 (appendFacts edge03 edge05))) (appendFacts
      (appendFacts edge08 (appendFacts edge12 edge42)) (appendFacts edge30 (appendFacts edge07Inv
      edge26))))))) (appendFacts (appendFacts (appendFacts (appendFacts (appendFacts (appendFacts edge03Inv
      edge24) (appendFacts edge40 (appendFacts edge23 edge39Inv))) (appendFacts (appendFacts edge23 edge39Inv)
      (appendFacts edge23 (appendFacts edge01 edge02)))) (appendFacts (appendFacts (appendFacts edge03 edge05)
      (appendFacts edge07 (appendFacts edge11 edge43))) (appendFacts (appendFacts edge33 edge10Inv)
      (appendFacts edge27 (appendFacts edge25Inv edge05))))) (appendFacts (appendFacts (appendFacts
      (appendFacts edge07 edge11) (appendFacts edge42Inv (appendFacts edge31 edge08Inv))) (appendFacts
      (appendFacts edge26 edge03Inv) (appendFacts edge24 (appendFacts edge40 edge23)))) (appendFacts
      (appendFacts (appendFacts edge01 edge02) (appendFacts edge04 (appendFacts edge06 edge10))) (appendFacts
      (appendFacts edge14 (appendFacts edge41 edge31)) (appendFacts edge08Inv (appendFacts edge26
      edge03Inv)))))) (appendFacts (appendFacts (appendFacts (appendFacts (appendFacts edge24 edge40)
      (appendFacts edge23 (appendFacts edge01 edge02))) (appendFacts (appendFacts edge04 edge06) (appendFacts
      edge09 (appendFacts edge13 edge16)))) (appendFacts (appendFacts (appendFacts edge18 edge22) (appendFacts
      edge45 (appendFacts edge20Inv edge35))) (appendFacts (appendFacts edge34 edge18) (appendFacts edge22
      (appendFacts edge45 edge20Inv))))) (appendFacts (appendFacts (appendFacts (appendFacts edge35 edge15Inv)
      (appendFacts edge32 (appendFacts edge09Inv edge27))) (appendFacts (appendFacts edge04Inv edge24)
      (appendFacts edge40 (appendFacts edge23 edge39Inv)))) (appendFacts (appendFacts (appendFacts edge23
      edge01) (appendFacts edge02 (appendFacts edge03 edge05))) (appendFacts (appendFacts edge07 (appendFacts
      edge11 edge42Inv)) (appendFacts edge31 (appendFacts edge28Inv edge11)))))))) (appendFacts (appendFacts
      (appendFacts (appendFacts (appendFacts (appendFacts (appendFacts edge43 edge33) (appendFacts edge29Inv
      (appendFacts edge13 edge16))) (appendFacts (appendFacts edge18 edge22) (appendFacts edge45 (appendFacts
      edge20Inv edge35)))) (appendFacts (appendFacts (appendFacts edge15Inv edge32) (appendFacts edge09Inv
      (appendFacts edge27 edge04Inv))) (appendFacts (appendFacts edge24 edge40) (appendFacts edge23
      (appendFacts edge39Inv edge23))))) (appendFacts (appendFacts (appendFacts (appendFacts edge39Inv edge23)
      (appendFacts edge39Inv (appendFacts edge23 edge39Inv))) (appendFacts (appendFacts edge23 edge39Inv)
      (appendFacts edge23 (appendFacts edge01 edge02)))) (appendFacts (appendFacts (appendFacts edge04 edge06)
      (appendFacts edge10 (appendFacts edge14 edge41))) (appendFacts (appendFacts edge31 (appendFacts
      edge08Inv edge26)) (appendFacts edge03Inv (appendFacts edge24 edge40)))))) (appendFacts (appendFacts
      (appendFacts (appendFacts (appendFacts edge23 edge01) (appendFacts edge02 (appendFacts edge03 edge05)))
      (appendFacts (appendFacts edge08 edge12) (appendFacts edge42 (appendFacts edge30 edge07Inv))))
      (appendFacts (appendFacts (appendFacts edge26 edge03Inv) (appendFacts edge24 (appendFacts edge01Inv
      edge00))) (appendFacts (appendFacts edge40Inv edge02) (appendFacts edge04 (appendFacts edge06
      edge10))))) (appendFacts (appendFacts (appendFacts (appendFacts edge14 edge41) (appendFacts edge31
      (appendFacts edge08Inv edge26))) (appendFacts (appendFacts edge03Inv edge24) (appendFacts edge40
      (appendFacts edge23 edge01)))) (appendFacts (appendFacts (appendFacts edge02 edge03) (appendFacts edge05
      (appendFacts edge08 edge12))) (appendFacts (appendFacts edge41Inv (appendFacts edge33 edge10Inv))
      (appendFacts edge27 (appendFacts edge25Inv edge05))))))) (appendFacts (appendFacts (appendFacts
      (appendFacts (appendFacts (appendFacts edge07 edge11) (appendFacts edge42Inv (appendFacts edge31
      edge08Inv))) (appendFacts (appendFacts edge26 edge03Inv) (appendFacts edge24 (appendFacts edge40
      edge23)))) (appendFacts (appendFacts (appendFacts edge01 edge02) (appendFacts edge04 (appendFacts edge06
      edge10))) (appendFacts (appendFacts edge14 edge41) (appendFacts edge31 (appendFacts edge08Inv
      edge26))))) (appendFacts (appendFacts (appendFacts (appendFacts edge03Inv edge24) (appendFacts edge40
      (appendFacts edge23 edge01))) (appendFacts (appendFacts edge02 edge04) (appendFacts edge06 (appendFacts
      edge09 edge13)))) (appendFacts (appendFacts (appendFacts edge16 edge18) (appendFacts edge22 (appendFacts
      edge45 edge20Inv))) (appendFacts (appendFacts edge35 (appendFacts edge34 edge18)) (appendFacts edge22
      (appendFacts edge45 edge20Inv)))))) (appendFacts (appendFacts (appendFacts (appendFacts (appendFacts
      edge35 edge15Inv) (appendFacts edge32 (appendFacts edge09Inv edge27))) (appendFacts (appendFacts
      edge04Inv edge24) (appendFacts edge40 (appendFacts edge23 edge39Inv)))) (appendFacts (appendFacts
      (appendFacts edge23 edge01) (appendFacts edge02 (appendFacts edge03 edge05))) (appendFacts (appendFacts
      edge08 edge12) (appendFacts edge42 (appendFacts edge30 edge07Inv))))) (appendFacts (appendFacts
      (appendFacts (appendFacts edge26 edge03Inv) (appendFacts edge24 (appendFacts edge01Inv edge00)))
      (appendFacts (appendFacts edge40Inv edge02) (appendFacts edge03 (appendFacts edge05 edge07))))
      (appendFacts (appendFacts (appendFacts edge11 edge42Inv) (appendFacts edge31 (appendFacts edge28Inv
      edge11))) (appendFacts (appendFacts edge42Inv (appendFacts edge31 edge28Inv)) (appendFacts edge11
      (appendFacts edge42Inv edge31))))))))) (appendFacts (appendFacts (appendFacts (appendFacts (appendFacts
      (appendFacts (appendFacts (appendFacts edge08Inv edge26) (appendFacts edge03Inv (appendFacts edge24
      edge40))) (appendFacts (appendFacts edge23 edge01) (appendFacts edge02 (appendFacts edge04 edge06))))
      (appendFacts (appendFacts (appendFacts edge10 edge14) (appendFacts edge41 (appendFacts edge31
      edge28Inv))) (appendFacts (appendFacts edge11 edge43) (appendFacts edge33 (appendFacts edge10Inv
      edge27))))) (appendFacts (appendFacts (appendFacts (appendFacts edge04Inv edge24) (appendFacts edge40
      (appendFacts edge23 edge39Inv))) (appendFacts (appendFacts edge23 edge01) (appendFacts edge02
      (appendFacts edge03 edge05)))) (appendFacts (appendFacts (appendFacts edge08 edge12) (appendFacts
      edge41Inv (appendFacts edge33 edge10Inv))) (appendFacts (appendFacts edge27 (appendFacts edge04Inv
      edge24)) (appendFacts edge40 (appendFacts edge23 edge39Inv)))))) (appendFacts (appendFacts (appendFacts
      (appendFacts (appendFacts edge23 edge39Inv) (appendFacts edge23 (appendFacts edge01 edge02)))
      (appendFacts (appendFacts edge03 edge05) (appendFacts edge08 (appendFacts edge12 edge41Inv))))
      (appendFacts (appendFacts (appendFacts edge33 edge10Inv) (appendFacts edge27 (appendFacts edge25Inv
      edge05))) (appendFacts (appendFacts edge08 edge12) (appendFacts edge41Inv (appendFacts edge33
      edge10Inv))))) (appendFacts (appendFacts (appendFacts (appendFacts edge27 edge04Inv) (appendFacts edge24
      (appendFacts edge01Inv edge00))) (appendFacts (appendFacts edge39 edge00) (appendFacts edge40Inv
      (appendFacts edge02 edge03)))) (appendFacts (appendFacts (appendFacts edge05 edge08) (appendFacts edge12
      (appendFacts edge42 edge30))) (appendFacts (appendFacts edge28 (appendFacts edge12 edge42)) (appendFacts
      edge30 (appendFacts edge28 edge12))))))) (appendFacts (appendFacts (appendFacts (appendFacts
      (appendFacts (appendFacts edge42 edge30) (appendFacts edge07Inv (appendFacts edge26 edge03Inv)))
      (appendFacts (appendFacts edge24 edge40) (appendFacts edge23 (appendFacts edge01 edge02)))) (appendFacts
      (appendFacts (appendFacts edge03 edge05) (appendFacts edge07 (appendFacts edge11 edge42Inv)))
      (appendFacts (appendFacts edge31 edge08Inv) (appendFacts edge26 (appendFacts edge03Inv edge24)))))
      (appendFacts (appendFacts (appendFacts (appendFacts edge40 edge23) (appendFacts edge39Inv (appendFacts
      edge23 edge01))) (appendFacts (appendFacts edge02 edge03) (appendFacts edge05 (appendFacts edge07
      edge11)))) (appendFacts (appendFacts (appendFacts edge42Inv edge31) (appendFacts edge08Inv (appendFacts
      edge26 edge03Inv))) (appendFacts (appendFacts edge24 (appendFacts edge01Inv edge00)) (appendFacts
      edge40Inv (appendFacts edge02 edge03)))))) (appendFacts (appendFacts (appendFacts (appendFacts
      (appendFacts edge05 edge08) (appendFacts edge12 (appendFacts edge41Inv edge33))) (appendFacts
      (appendFacts edge10Inv edge27) (appendFacts edge04Inv (appendFacts edge24 edge40)))) (appendFacts
      (appendFacts (appendFacts edge23 edge01) (appendFacts edge02 (appendFacts edge03 edge05))) (appendFacts
      (appendFacts edge07 edge11) (appendFacts edge42Inv (appendFacts edge31 edge08Inv))))) (appendFacts
      (appendFacts (appendFacts (appendFacts edge26 edge03Inv) (appendFacts edge24 (appendFacts edge01Inv
      edge00))) (appendFacts (appendFacts edge40Inv edge02) (appendFacts edge03 (appendFacts edge05 edge08))))
      (appendFacts (appendFacts (appendFacts edge12 edge41Inv) (appendFacts edge33 (appendFacts edge10Inv
      edge27))) (appendFacts (appendFacts edge04Inv (appendFacts edge24 edge01Inv)) (appendFacts edge00
      (appendFacts edge39 edge00)))))))) (appendFacts (appendFacts (appendFacts (appendFacts (appendFacts
      (appendFacts (appendFacts edge39 edge00) (appendFacts edge39 (appendFacts edge00 edge39))) (appendFacts
      (appendFacts edge00 edge39) (appendFacts edge00 (appendFacts edge40Inv edge02)))) (appendFacts
      (appendFacts (appendFacts edge04 edge06) (appendFacts edge09 (appendFacts edge13 edge15))) (appendFacts
      (appendFacts edge17 edge20) (appendFacts edge44Inv (appendFacts edge22Inv edge36))))) (appendFacts
      (appendFacts (appendFacts (appendFacts edge16Inv edge32) (appendFacts edge29 (appendFacts edge14
      edge43Inv))) (appendFacts (appendFacts edge30 edge28) (appendFacts edge12 (appendFacts edge42 edge30))))
      (appendFacts (appendFacts (appendFacts edge07Inv edge26) (appendFacts edge03Inv (appendFacts edge24
      edge01Inv))) (appendFacts (appendFacts edge00 (appendFacts edge40Inv edge02)) (appendFacts edge03
      (appendFacts edge05 edge08)))))) (appendFacts (appendFacts (appendFacts (appendFacts (appendFacts edge12
      edge42) (appendFacts edge30 (appendFacts edge28 edge12))) (appendFacts (appendFacts edge41Inv edge33)
      (appendFacts edge10Inv (appendFacts edge27 edge04Inv)))) (appendFacts (appendFacts (appendFacts edge24
      edge01Inv) (appendFacts edge00 (appendFacts edge40Inv edge02))) (appendFacts (appendFacts edge03 edge05)
      (appendFacts edge08 (appendFacts edge12 edge42))))) (appendFacts (appendFacts (appendFacts (appendFacts
      edge30 edge28) (appendFacts edge12 (appendFacts edge42 edge30))) (appendFacts (appendFacts edge28
      edge12) (appendFacts edge42 (appendFacts edge30 edge07Inv)))) (appendFacts (appendFacts (appendFacts
      edge26 edge03Inv) (appendFacts edge24 (appendFacts edge40 edge23))) (appendFacts (appendFacts edge01
      (appendFacts edge02 edge03)) (appendFacts edge05 (appendFacts edge07 edge11))))))) (appendFacts
      (appendFacts (appendFacts (appendFacts (appendFacts (appendFacts edge42Inv edge31) (appendFacts
      edge08Inv (appendFacts edge26 edge03Inv))) (appendFacts (appendFacts edge24 edge01Inv) (appendFacts
      edge00 (appendFacts edge39 edge00)))) (appendFacts (appendFacts (appendFacts edge40Inv edge02)
      (appendFacts edge04 (appendFacts edge06 edge09))) (appendFacts (appendFacts edge13 edge15) (appendFacts
      edge17 (appendFacts edge20 edge44Inv))))) (appendFacts (appendFacts (appendFacts (appendFacts edge22Inv
      edge36) (appendFacts edge34Inv (appendFacts edge17 edge20))) (appendFacts (appendFacts edge44Inv
      edge22Inv) (appendFacts edge36 (appendFacts edge16Inv edge32)))) (appendFacts (appendFacts (appendFacts
      edge09Inv edge27) (appendFacts edge04Inv (appendFacts edge24 edge01Inv))) (appendFacts (appendFacts
      edge00 (appendFacts edge40Inv edge02)) (appendFacts edge03 (appendFacts edge05 edge08)))))) (appendFacts
      (appendFacts (appendFacts (appendFacts (appendFacts edge12 edge41Inv) (appendFacts edge33 (appendFacts
      edge10Inv edge27))) (appendFacts (appendFacts edge04Inv edge24) (appendFacts edge01Inv (appendFacts
      edge00 edge40Inv)))) (appendFacts (appendFacts (appendFacts edge02 edge03) (appendFacts edge05
      (appendFacts edge08 edge12))) (appendFacts (appendFacts edge42 (appendFacts edge30 edge07Inv))
      (appendFacts edge26 (appendFacts edge25 edge06))))) (appendFacts (appendFacts (appendFacts (appendFacts
      edge10 edge14) (appendFacts edge43Inv (appendFacts edge30 edge07Inv))) (appendFacts (appendFacts edge26
      edge03Inv) (appendFacts edge24 (appendFacts edge01Inv edge00)))) (appendFacts (appendFacts (appendFacts
      edge39 edge00) (appendFacts edge40Inv (appendFacts edge02 edge04))) (appendFacts (appendFacts edge06
      (appendFacts edge09 edge13)) (appendFacts edge16 (appendFacts edge18 edge21))))))))))
  have hsuf : Holds firstSubgroup PresentedGroup.of representative ⟨20, [(true, false), (false, true), (true,
    false), (false, true), (true, false), (false, true), (true, true), (false, true)], 2⟩ :=
    (appendFacts (appendFacts (appendFacts edge19Inv edge35) (appendFacts edge15Inv edge32)) (appendFacts
      (appendFacts edge09Inv edge27) (appendFacts edge04Inv edge24)))
  exact scanFacts hpre hsuf (holds_relator 2 (relatorLetters 44) (presentation_relator 44))

private theorem edge46Inv : Holds firstSubgroup PresentedGroup.of representative ⟨20, [(false, false)], 22⟩ :=
  holds_reverse edge46

-- Trace event 47: ['scan', 4, ['rel', 2], 7, 20, 1, 22].
private theorem edge47 : Holds firstSubgroup PresentedGroup.of representative ⟨20, [(false, true)], 22⟩ := by
  have hpre : Holds firstSubgroup PresentedGroup.of representative ⟨4, [(true, true), (false, true), (true,
    true), (false, true), (true, true), (false, true), (true, true)], 20⟩ :=
    (appendFacts (appendFacts edge25 (appendFacts edge06 edge09)) (appendFacts (appendFacts edge13 edge15)
      (appendFacts edge17 edge19)))
  have hsuf : Holds firstSubgroup PresentedGroup.of representative ⟨22, [(true, true), (false, true), (true,
    true), (false, true), (true, true), (false, true), (true, true), (false, true), (true, true), (false,
    true), (true, true), (false, true), (true, true), (false, true), (true, true), (false, true), (true,
    true), (false, true), (true, true), (false, true)], 4⟩ :=
    (appendFacts (appendFacts (appendFacts (appendFacts edge38 edge45) (appendFacts edge20Inv (appendFacts
      edge35 edge34))) (appendFacts (appendFacts edge18 edge21) (appendFacts edge46 (appendFacts edge37
      edge44Inv)))) (appendFacts (appendFacts (appendFacts edge22Inv edge36) (appendFacts edge16Inv
      (appendFacts edge32 edge29))) (appendFacts (appendFacts edge14 edge41) (appendFacts edge31 (appendFacts
      edge08Inv edge26)))))
  exact scanFacts hpre hsuf (holds_relator 4 (relatorLetters 2) (presentation_relator 2))

private theorem edge47Inv : Holds firstSubgroup PresentedGroup.of representative ⟨22, [(false, false)], 20⟩ :=
  holds_reverse edge47

private def destination (i : Fin 24) (a : Bool × Bool) : Fin 24 :=
  (show Vector (Fin 24) 24 from match a with
  | (false, true) => #v[1, 0, 3, 2, 6, 7, 4, 5, 12, 13, 14, 15, 8, 9, 10, 11, 18, 19, 16, 17, 22, 23, 20, 21]
  | (false, false) => #v[1, 0, 3, 2, 6, 7, 4, 5, 12, 13, 14, 15, 8, 9, 10, 11, 18, 19, 16, 17, 22, 23, 20, 21]
  | (true, true) => #v[2, 0, 1, 4, 5, 3, 8, 10, 9, 6, 11, 7, 15, 12, 16, 13, 17, 14, 20, 22, 21, 18, 23, 19]
  | (true, false) => #v[1, 2, 0, 5, 3, 4, 9, 11, 6, 8, 7, 10, 13, 15, 17, 12, 14, 16, 21, 23, 18, 20, 19, 22]
  ).get i

private theorem transitions (i : Fin 24) (a : Bool × Bool) :
    Holds firstSubgroup PresentedGroup.of representative
      ⟨i.val, [a], (destination i a).val⟩ := by
  rcases a with ⟨a, sign⟩
  fin_cases i <;> cases a <;> cases sign
  · exact edge23Inv
  · exact edge00
  · exact edge39Inv
  · exact edge01
  · exact edge00Inv
  · exact edge23
  · exact edge40Inv
  · exact edge39
  · exact edge24Inv
  · exact edge02
  · exact edge01Inv
  · exact edge40
  · exact edge02Inv
  · exact edge24
  · exact edge04
  · exact edge03
  · exact edge26Inv
  · exact edge05
  · exact edge03Inv
  · exact edge25
  · exact edge27Inv
  · exact edge06
  · exact edge25Inv
  · exact edge04Inv
  · exact edge05Inv
  · exact edge26
  · exact edge08
  · exact edge07
  · exact edge06Inv
  · exact edge27
  · exact edge10
  · exact edge09
  · exact edge30Inv
  · exact edge11
  · exact edge07Inv
  · exact edge28
  · exact edge31Inv
  · exact edge12
  · exact edge28Inv
  · exact edge08Inv
  · exact edge32Inv
  · exact edge13
  · exact edge09Inv
  · exact edge29
  · exact edge33Inv
  · exact edge14
  · exact edge29Inv
  · exact edge10Inv
  · exact edge11Inv
  · exact edge30
  · exact edge42Inv
  · exact edge43
  · exact edge12Inv
  · exact edge31
  · exact edge41Inv
  · exact edge42
  · exact edge13Inv
  · exact edge32
  · exact edge16
  · exact edge15
  · exact edge14Inv
  · exact edge33
  · exact edge43Inv
  · exact edge41
  · exact edge35Inv
  · exact edge17
  · exact edge15Inv
  · exact edge34
  · exact edge36Inv
  · exact edge18
  · exact edge34Inv
  · exact edge16Inv
  · exact edge17Inv
  · exact edge35
  · exact edge20
  · exact edge19
  · exact edge18Inv
  · exact edge36
  · exact edge22
  · exact edge21
  · exact edge46Inv
  · exact edge47
  · exact edge19Inv
  · exact edge37
  · exact edge45Inv
  · exact edge44Inv
  · exact edge37Inv
  · exact edge20Inv
  · exact edge47Inv
  · exact edge46
  · exact edge21Inv
  · exact edge38
  · exact edge44
  · exact edge45
  · exact edge38Inv
  · exact edge22Inv

/-- The ten explicit subgroup generators have a cover by 24 right cosets
in the original presentation. -/
public def firstSubgroup_cosetCover :
    Subgroup.GeneratorCosetCover firstSubgroup PresentedGroup.of (Fin 24) :=
  generatorCosetCover Fin.val 0 (eval_nil PresentedGroup.of) destination transitions

end Janko4.Cardinality.QuotientCount.UpperBound.PresentationBound
