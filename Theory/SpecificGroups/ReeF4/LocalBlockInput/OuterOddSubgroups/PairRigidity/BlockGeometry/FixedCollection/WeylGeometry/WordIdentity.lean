module

public import Mathlib.Algebra.Group.Basic
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Tactic.FinCases

/-!
# A B₂ word calculation in characteristic two

The ten letters are the eight signed root elements and the two simple Weyl
lifts. Root involutions, reflection transport, the rank-one and B₂ braid
relations, and the Chevalley exchanges give a five-factor expression for the
longest Weyl lift in terms of the two central root pairs. Every step below is
an equality in an arbitrary group; the concrete Ree matrices discharge the
relations in `SuzukiWord`.

Source: GLS3, 2.3.8 and Table 2.4, `refs/KGroup/GLS3/chapter2.tex`.
-/

@[expose] public section
namespace ReeF4.LocalBlockInput.PairRigidity.FixedCollection.B2WordCalculation

def reflectionIndex : Fin 2 → Fin 8 → Fin 8 :=
  ![![4, 2, 1, 3, 0, 6, 5, 7], ![3, 5, 2, 0, 7, 1, 6, 4]]

def commutingPairs : Fin 16 → Fin 8 × Fin 8 :=
  ![(2, 0), (2, 1), (3, 0), (3, 1), (3, 2), (4, 1), (4, 3), (5, 0), (5, 2), (6, 1), (6, 4), (6, 5), (7, 0), (7, 4), (7, 5), (7, 6)]

def exchangeRoots : Fin 8 → Fin 8 × Fin 8 × Fin 8 × Fin 8 :=
  ![(0, 1, 2, 3), (0, 6, 5, 7), (3, 5, 2, 0), (3, 6, 1, 4), (4, 2, 1, 3), (4, 5, 6, 7), (7, 1, 6, 4), (7, 2, 5, 0)]

/-- Chevalley and rank-one relations imply the central five-factor word. -/
theorem central_word {G : Type*} [Group G] (x : Fin 10 → G)
    (hsq : ∀ i, x i * x i = 1)
    (hconj : ∀ (i : Fin 2) (j : Fin 8),
      x ⟨8 + i.val, by omega⟩ * x (j.castLE (by decide)) =
        x ((reflectionIndex i j).castLE (by decide)) * x ⟨8 + i.val, by omega⟩)
    (hweyl : ∀ i : Fin 2, x (i.castLE (by decide)) * x ⟨i.val + 4, by omega⟩ *
      x (i.castLE (by decide)) = x ⟨8 + i.val, by omega⟩)
    (hrootbraid : x 7 * x 3 * x 7 = x 3 * x 7 * x 3)
    (hbraid : x 9 * x 8 * x 9 * x 8 = x 8 * x 9 * x 8 * x 9)
    (hcomm : ∀ i, let p := commutingPairs i
      x (p.1.castLE (by decide)) * x (p.2.castLE (by decide)) =
        x (p.2.castLE (by decide)) * x (p.1.castLE (by decide)))
    (hswap : ∀ i, let p := exchangeRoots i
      x (p.1.castLE (by decide)) * x (p.2.1.castLE (by decide)) *
        x (p.2.2.1.castLE (by decide)) * x (p.2.2.2.castLE (by decide)) =
      x (p.2.1.castLE (by decide)) * x (p.1.castLE (by decide))) :
    (x 2 * x 3) * (x 6 * x 7) * (x 2 * x 3) * (x 6 * x 7) * (x 2 * x 3) =
      x 8 * x 9 * x 8 * x 9 := by
  have r0 : x 0 * x 0 = (1 : G) := by
    exact hsq 0
  have r1 : x 1 * x 1 = (1 : G) := by
    exact hsq 1
  have r2 : x 2 * x 2 = (1 : G) := by
    exact hsq 2
  have r3 : x 3 * x 3 = (1 : G) := by
    exact hsq 3
  have r4 : x 4 * x 4 = (1 : G) := by
    exact hsq 4
  have r7 : x 7 * x 7 = (1 : G) := by
    exact hsq 7
  have r8 : x 8 * x 8 = (1 : G) := by
    exact hsq 8
  have r9 : x 9 * x 9 = (1 : G) := by
    exact hsq 9
  have r11 : x 8 * x 1 = x 2 * x 8 := by
    exact hconj 0 1
  have r13 : x 8 * x 3 = x 3 * x 8 := by
    exact hconj 0 3
  have r15 : x 8 * x 5 = x 6 * x 8 := by
    exact hconj 0 5
  have r17 : x 8 * x 7 = x 7 * x 8 := by
    exact hconj 0 7
  have r18 : x 9 * x 0 = x 3 * x 9 := by
    exact hconj 1 0
  have r20 : x 9 * x 2 = x 2 * x 9 := by
    exact hconj 1 2
  have r22 : x 9 * x 4 = x 7 * x 9 := by
    exact hconj 1 4
  have r24 : x 9 * x 6 = x 6 * x 9 := by
    exact hconj 1 6
  have r26 : x 0 * x 4 * x 0 = x 8 := by
    exact hweyl 0
  have r27 : x 1 * x 5 * x 1 = x 9 := by
    exact hweyl 1
  have r31 : x 7 * x 3 * x 7 = x 3 * x 7 * x 3 := by
    exact hrootbraid
  have r32 : x 9 * x 8 * x 9 * x 8 = x 8 * x 9 * x 8 * x 9 := by
    exact hbraid
  have r33 : x 2 * x 0 = x 0 * x 2 := by
    exact hcomm 0
  have r34 : x 2 * x 1 = x 1 * x 2 := by
    exact hcomm 1
  have r35 : x 3 * x 0 = x 0 * x 3 := by
    exact hcomm 2
  have r36 : x 3 * x 1 = x 1 * x 3 := by
    exact hcomm 3
  have r38 : x 4 * x 1 = x 1 * x 4 := by
    exact hcomm 5
  have r42 : x 6 * x 1 = x 1 * x 6 := by
    exact hcomm 9
  have r43 : x 6 * x 4 = x 4 * x 6 := by
    exact hcomm 10
  have r44 : x 6 * x 5 = x 5 * x 6 := by
    exact hcomm 11
  have r45 : x 7 * x 0 = x 0 * x 7 := by
    exact hcomm 12
  have r46 : x 7 * x 4 = x 4 * x 7 := by
    exact hcomm 13
  have r48 : x 7 * x 6 = x 6 * x 7 := by
    exact hcomm 15
  have r49 : x 0 * x 1 * x 2 * x 3 = x 1 * x 0 := by
    exact hswap 0
  have r50 : x 0 * x 6 * x 5 * x 7 = x 6 * x 0 := by
    exact hswap 1
  have r52 : x 3 * x 6 * x 1 * x 4 = x 6 * x 3 := by
    exact hswap 3
  have r53 : x 4 * x 2 * x 1 * x 3 = x 2 * x 4 := by
    exact hswap 4
  have r55 : x 7 * x 1 * x 6 * x 4 = x 1 * x 7 := by
    exact hswap 6
  have r59 : x 3 * x 7 * x 3 * x 9 = x 9 * x 8 := by
    have ha : x 9 * x 0 * x 4 * x 0 = x 3 * x 7 * x 3 * x 9 := by
      have step0 : x 9 * x 0 * x 4 * x 0 = x 3 * x 9 * x 4 * x 0 := by
        simpa only [mul_assoc, one_mul, mul_one] using
          congrArg (fun z => ((1 : G)) * z * (x 4 * x 0)) r18
      have step1 : x 3 * x 9 * x 4 * x 0 = x 3 * x 7 * x 9 * x 0 := by
        simpa only [mul_assoc, one_mul, mul_one] using
          congrArg (fun z => (x 3) * z * (x 0)) r22
      have step2 : x 3 * x 7 * x 9 * x 0 = x 3 * x 7 * x 3 * x 9 := by
        simpa only [mul_assoc, one_mul, mul_one] using
          congrArg (fun z => (x 3 * x 7) * z * ((1 : G))) r18
      exact ((step0).trans step1).trans step2
    have hb : x 9 * x 0 * x 4 * x 0 = x 9 * x 8 := by
      have step0 : x 9 * x 0 * x 4 * x 0 = x 9 * x 8 := by
        simpa only [mul_assoc, one_mul, mul_one] using
          congrArg (fun z => (x 9) * z * ((1 : G))) r26
      exact step0
    exact ha.symm.trans hb
  have r61 : x 5 * x 1 = x 1 * x 9 := by
    have ha : x 1 * x 1 * x 5 * x 1 = x 5 * x 1 := by
      have step0 : x 1 * x 1 * x 5 * x 1 = x 5 * x 1 := by
        simpa only [mul_assoc, one_mul, mul_one] using
          congrArg (fun z => ((1 : G)) * z * (x 5 * x 1)) r1
      exact step0
    have hb : x 1 * x 1 * x 5 * x 1 = x 1 * x 9 := by
      have step0 : x 1 * x 1 * x 5 * x 1 = x 1 * x 9 := by
        simpa only [mul_assoc, one_mul, mul_one] using
          congrArg (fun z => (x 1) * z * ((1 : G))) r27
      exact step0
    exact ha.symm.trans hb
  have r62 : x 2 * x 6 * x 2 * x 8 = x 8 * x 9 := by
    have ha : x 8 * x 1 * x 5 * x 1 = x 2 * x 6 * x 2 * x 8 := by
      have step0 : x 8 * x 1 * x 5 * x 1 = x 2 * x 8 * x 5 * x 1 := by
        simpa only [mul_assoc, one_mul, mul_one] using
          congrArg (fun z => ((1 : G)) * z * (x 5 * x 1)) r11
      have step1 : x 2 * x 8 * x 5 * x 1 = x 2 * x 6 * x 8 * x 1 := by
        simpa only [mul_assoc, one_mul, mul_one] using
          congrArg (fun z => (x 2) * z * (x 1)) r15
      have step2 : x 2 * x 6 * x 8 * x 1 = x 2 * x 6 * x 2 * x 8 := by
        simpa only [mul_assoc, one_mul, mul_one] using
          congrArg (fun z => (x 2 * x 6) * z * ((1 : G))) r11
      exact ((step0).trans step1).trans step2
    have hb : x 8 * x 1 * x 5 * x 1 = x 8 * x 9 := by
      have step0 : x 8 * x 1 * x 5 * x 1 = x 8 * x 9 := by
        simpa only [mul_assoc, one_mul, mul_one] using
          congrArg (fun z => (x 8) * z * ((1 : G))) r27
      exact step0
    exact ha.symm.trans hb
  have r78 : x 7 * x 1 * x 6 = x 6 * x 7 * x 1 := by
    have ha : x 7 * x 6 * x 1 = x 7 * x 1 * x 6 := by
      have step0 : x 7 * x 6 * x 1 = x 7 * x 1 * x 6 := by
        simpa only [mul_assoc, one_mul, mul_one] using
          congrArg (fun z => (x 7) * z * ((1 : G))) r42
      exact step0
    have hb : x 7 * x 6 * x 1 = x 6 * x 7 * x 1 := by
      have step0 : x 7 * x 6 * x 1 = x 6 * x 7 * x 1 := by
        simpa only [mul_assoc, one_mul, mul_one] using
          congrArg (fun z => ((1 : G)) * z * (x 1)) r48
      exact step0
    exact ha.symm.trans hb
  have r79 : x 1 * x 2 * x 3 = x 0 * x 1 * x 0 := by
    have ha : x 0 * x 0 * x 1 * x 2 * x 3 = x 1 * x 2 * x 3 := by
      have step0 : x 0 * x 0 * x 1 * x 2 * x 3 = x 1 * x 2 * x 3 := by
        simpa only [mul_assoc, one_mul, mul_one] using
          congrArg (fun z => ((1 : G)) * z * (x 1 * x 2 * x 3)) r0
      exact step0
    have hb : x 0 * x 0 * x 1 * x 2 * x 3 = x 0 * x 1 * x 0 := by
      have step0 : x 0 * x 0 * x 1 * x 2 * x 3 = x 0 * x 1 * x 0 := by
        simpa only [mul_assoc, one_mul, mul_one] using
          congrArg (fun z => (x 0) * z * ((1 : G))) r49
      exact step0
    exact ha.symm.trans hb
  have r80 : x 1 * x 0 * x 3 = x 0 * x 1 * x 2 := by
    have ha : x 0 * x 1 * x 2 * x 3 * x 3 = x 1 * x 0 * x 3 := by
      have step0 : x 0 * x 1 * x 2 * x 3 * x 3 = x 1 * x 0 * x 3 := by
        simpa only [mul_assoc, one_mul, mul_one] using
          congrArg (fun z => ((1 : G)) * z * (x 3)) r49
      exact step0
    have hb : x 0 * x 1 * x 2 * x 3 * x 3 = x 0 * x 1 * x 2 := by
      have step0 : x 0 * x 1 * x 2 * x 3 * x 3 = x 0 * x 1 * x 2 := by
        simpa only [mul_assoc, one_mul, mul_one] using
          congrArg (fun z => (x 0 * x 1 * x 2) * z * ((1 : G))) r3
      exact step0
    exact ha.symm.trans hb
  have r83 : x 1 * x 0 * x 2 = x 0 * x 1 * x 3 := by
    have ha : x 2 * x 0 * x 1 * x 2 * x 3 = x 1 * x 0 * x 2 := by
      have step0 : x 2 * x 0 * x 1 * x 2 * x 3 = x 2 * x 1 * x 0 := by
        simpa only [mul_assoc, one_mul, mul_one] using
          congrArg (fun z => (x 2) * z * ((1 : G))) r49
      have step1 : x 2 * x 1 * x 0 = x 1 * x 2 * x 0 := by
        simpa only [mul_assoc, one_mul, mul_one] using
          congrArg (fun z => ((1 : G)) * z * (x 0)) r34
      have step2 : x 1 * x 2 * x 0 = x 1 * x 0 * x 2 := by
        simpa only [mul_assoc, one_mul, mul_one] using
          congrArg (fun z => (x 1) * z * ((1 : G))) r33
      exact ((step0).trans step1).trans step2
    have hb : x 2 * x 0 * x 1 * x 2 * x 3 = x 0 * x 1 * x 3 := by
      have step0 : x 2 * x 0 * x 1 * x 2 * x 3 = x 0 * x 2 * x 1 * x 2 * x 3 := by
        simpa only [mul_assoc, one_mul, mul_one] using
          congrArg (fun z => ((1 : G)) * z * (x 1 * x 2 * x 3)) r33
      have step1 : x 0 * x 2 * x 1 * x 2 * x 3 = x 0 * x 1 * x 2 * x 2 * x 3 := by
        simpa only [mul_assoc, one_mul, mul_one] using
          congrArg (fun z => (x 0) * z * (x 2 * x 3)) r34
      have step2 : x 0 * x 1 * x 2 * x 2 * x 3 = x 0 * x 1 * x 3 := by
        simpa only [mul_assoc, one_mul, mul_one] using
          congrArg (fun z => (x 0 * x 1) * z * (x 3)) r2
      exact ((step0).trans step1).trans step2
    exact ha.symm.trans hb
  have r84 : x 1 * x 0 * x 1 = x 0 * x 2 * x 3 := by
    have ha : x 0 * x 1 * x 2 * x 3 * x 1 = x 1 * x 0 * x 1 := by
      have step0 : x 0 * x 1 * x 2 * x 3 * x 1 = x 1 * x 0 * x 1 := by
        simpa only [mul_assoc, one_mul, mul_one] using
          congrArg (fun z => ((1 : G)) * z * (x 1)) r49
      exact step0
    have hb : x 0 * x 1 * x 2 * x 3 * x 1 = x 0 * x 2 * x 3 := by
      have step0 : x 0 * x 1 * x 2 * x 3 * x 1 = x 0 * x 1 * x 2 * x 1 * x 3 := by
        simpa only [mul_assoc, one_mul, mul_one] using
          congrArg (fun z => (x 0 * x 1 * x 2) * z * ((1 : G))) r36
      have step1 : x 0 * x 1 * x 2 * x 1 * x 3 = x 0 * x 1 * x 1 * x 2 * x 3 := by
        simpa only [mul_assoc, one_mul, mul_one] using
          congrArg (fun z => (x 0 * x 1) * z * (x 3)) r34
      have step2 : x 0 * x 1 * x 1 * x 2 * x 3 = x 0 * x 2 * x 3 := by
        simpa only [mul_assoc, one_mul, mul_one] using
          congrArg (fun z => (x 0) * z * (x 2 * x 3)) r1
      exact ((step0).trans step1).trans step2
    exact ha.symm.trans hb
  have r86 : x 6 * x 0 * x 7 = x 0 * x 5 * x 6 := by
    have ha : x 0 * x 6 * x 5 * x 7 * x 7 = x 6 * x 0 * x 7 := by
      have step0 : x 0 * x 6 * x 5 * x 7 * x 7 = x 6 * x 0 * x 7 := by
        simpa only [mul_assoc, one_mul, mul_one] using
          congrArg (fun z => ((1 : G)) * z * (x 7)) r50
      exact step0
    have hb : x 0 * x 6 * x 5 * x 7 * x 7 = x 0 * x 5 * x 6 := by
      have step0 : x 0 * x 6 * x 5 * x 7 * x 7 = x 0 * x 6 * x 5 := by
        simpa only [mul_assoc, one_mul, mul_one] using
          congrArg (fun z => (x 0 * x 6 * x 5) * z * ((1 : G))) r7
      have step1 : x 0 * x 6 * x 5 = x 0 * x 5 * x 6 := by
        simpa only [mul_assoc, one_mul, mul_one] using
          congrArg (fun z => (x 0) * z * ((1 : G))) r44
      exact (step0).trans step1
    exact ha.symm.trans hb
  have r102 : x 3 * x 4 * x 6 = x 1 * x 6 * x 3 := by
    have ha : x 3 * x 6 * x 1 * x 4 * x 1 = x 3 * x 4 * x 6 := by
      have step0 : x 3 * x 6 * x 1 * x 4 * x 1 = x 3 * x 6 * x 1 * x 1 * x 4 := by
        simpa only [mul_assoc, one_mul, mul_one] using
          congrArg (fun z => (x 3 * x 6 * x 1) * z * ((1 : G))) r38
      have step1 : x 3 * x 6 * x 1 * x 1 * x 4 = x 3 * x 6 * x 4 := by
        simpa only [mul_assoc, one_mul, mul_one] using
          congrArg (fun z => (x 3 * x 6) * z * (x 4)) r1
      have step2 : x 3 * x 6 * x 4 = x 3 * x 4 * x 6 := by
        simpa only [mul_assoc, one_mul, mul_one] using
          congrArg (fun z => (x 3) * z * ((1 : G))) r43
      exact ((step0).trans step1).trans step2
    have hb : x 3 * x 6 * x 1 * x 4 * x 1 = x 1 * x 6 * x 3 := by
      have step0 : x 3 * x 6 * x 1 * x 4 * x 1 = x 6 * x 3 * x 1 := by
        simpa only [mul_assoc, one_mul, mul_one] using
          congrArg (fun z => ((1 : G)) * z * (x 1)) r52
      have step1 : x 6 * x 3 * x 1 = x 6 * x 1 * x 3 := by
        simpa only [mul_assoc, one_mul, mul_one] using
          congrArg (fun z => (x 6) * z * ((1 : G))) r36
      have step2 : x 6 * x 1 * x 3 = x 1 * x 6 * x 3 := by
        simpa only [mul_assoc, one_mul, mul_one] using
          congrArg (fun z => ((1 : G)) * z * (x 3)) r42
      exact ((step0).trans step1).trans step2
    exact ha.symm.trans hb
  have r104 : x 4 * x 2 * x 4 = x 0 * x 1 * x 0 := by
    have ha : x 4 * x 4 * x 2 * x 1 * x 3 = x 4 * x 2 * x 4 := by
      have step0 : x 4 * x 4 * x 2 * x 1 * x 3 = x 4 * x 2 * x 4 := by
        simpa only [mul_assoc, one_mul, mul_one] using
          congrArg (fun z => (x 4) * z * ((1 : G))) r53
      exact step0
    have hb : x 4 * x 4 * x 2 * x 1 * x 3 = x 0 * x 1 * x 0 := by
      have step0 : x 4 * x 4 * x 2 * x 1 * x 3 = x 2 * x 1 * x 3 := by
        simpa only [mul_assoc, one_mul, mul_one] using
          congrArg (fun z => ((1 : G)) * z * (x 2 * x 1 * x 3)) r4
      have step1 : x 2 * x 1 * x 3 = x 1 * x 2 * x 3 := by
        simpa only [mul_assoc, one_mul, mul_one] using
          congrArg (fun z => ((1 : G)) * z * (x 3)) r34
      have step2 : x 1 * x 2 * x 3 = x 0 * x 1 * x 0 := by
        simpa only [mul_assoc, one_mul, mul_one] using
          congrArg (fun z => ((1 : G)) * z * ((1 : G))) r79
      exact ((step0).trans step1).trans step2
    exact ha.symm.trans hb
  have r123 : x 7 * x 1 * x 3 * x 7 = x 3 * x 6 * x 7 * x 3 := by
    have ha : x 7 * x 3 * x 7 * x 1 * x 6 * x 4 = x 7 * x 1 * x 3 * x 7 := by
      have step0 : x 7 * x 3 * x 7 * x 1 * x 6 * x 4 = x 7 * x 3 * x 1 * x 7 := by
        simpa only [mul_assoc, one_mul, mul_one] using
          congrArg (fun z => (x 7 * x 3) * z * ((1 : G))) r55
      have step1 : x 7 * x 3 * x 1 * x 7 = x 7 * x 1 * x 3 * x 7 := by
        simpa only [mul_assoc, one_mul, mul_one] using
          congrArg (fun z => (x 7) * z * (x 7)) r36
      exact (step0).trans step1
    have hb : x 7 * x 3 * x 7 * x 1 * x 6 * x 4 = x 3 * x 6 * x 7 * x 3 := by
      have step0 : x 7 * x 3 * x 7 * x 1 * x 6 * x 4 = x 3 * x 7 * x 3 * x 1 * x 6 * x 4 := by
        simpa only [mul_assoc, one_mul, mul_one] using
          congrArg (fun z => ((1 : G)) * z * (x 1 * x 6 * x 4)) r31
      have step1 : x 3 * x 7 * x 3 * x 1 * x 6 * x 4 = x 3 * x 7 * x 1 * x 3 * x 6 * x 4 := by
        simpa only [mul_assoc, one_mul, mul_one] using
          congrArg (fun z => (x 3 * x 7) * z * (x 6 * x 4)) r36
      have step2 : x 3 * x 7 * x 1 * x 3 * x 6 * x 4 = x 3 * x 7 * x 1 * x 3 * x 4 * x 6 := by
        simpa only [mul_assoc, one_mul, mul_one] using
          congrArg (fun z => (x 3 * x 7 * x 1 * x 3) * z * ((1 : G))) r43
      have step3 : x 3 * x 7 * x 1 * x 3 * x 4 * x 6 = x 3 * x 7 * x 1 * x 1 * x 6 * x 3 := by
        simpa only [mul_assoc, one_mul, mul_one] using
          congrArg (fun z => (x 3 * x 7 * x 1) * z * ((1 : G))) r102
      have step4 : x 3 * x 7 * x 1 * x 1 * x 6 * x 3 = x 3 * x 7 * x 6 * x 3 := by
        simpa only [mul_assoc, one_mul, mul_one] using
          congrArg (fun z => (x 3 * x 7) * z * (x 6 * x 3)) r1
      have step5 : x 3 * x 7 * x 6 * x 3 = x 3 * x 6 * x 7 * x 3 := by
        simpa only [mul_assoc, one_mul, mul_one] using
          congrArg (fun z => (x 3) * z * (x 3)) r48
      exact (((((step0).trans step1).trans step2).trans step3).trans step4).trans step5
    exact ha.symm.trans hb
  have r124 : x 4 * x 6 * x 7 = x 1 * x 7 * x 1 := by
    have ha : x 7 * x 1 * x 6 * x 4 * x 1 = x 4 * x 6 * x 7 := by
      have step0 : x 7 * x 1 * x 6 * x 4 * x 1 = x 7 * x 1 * x 6 * x 1 * x 4 := by
        simpa only [mul_assoc, one_mul, mul_one] using
          congrArg (fun z => (x 7 * x 1 * x 6) * z * ((1 : G))) r38
      have step1 : x 7 * x 1 * x 6 * x 1 * x 4 = x 7 * x 1 * x 1 * x 6 * x 4 := by
        simpa only [mul_assoc, one_mul, mul_one] using
          congrArg (fun z => (x 7 * x 1) * z * (x 4)) r42
      have step2 : x 7 * x 1 * x 1 * x 6 * x 4 = x 7 * x 6 * x 4 := by
        simpa only [mul_assoc, one_mul, mul_one] using
          congrArg (fun z => (x 7) * z * (x 6 * x 4)) r1
      have step3 : x 7 * x 6 * x 4 = x 7 * x 4 * x 6 := by
        simpa only [mul_assoc, one_mul, mul_one] using
          congrArg (fun z => (x 7) * z * ((1 : G))) r43
      have step4 : x 7 * x 4 * x 6 = x 4 * x 7 * x 6 := by
        simpa only [mul_assoc, one_mul, mul_one] using
          congrArg (fun z => ((1 : G)) * z * (x 6)) r46
      have step5 : x 4 * x 7 * x 6 = x 4 * x 6 * x 7 := by
        simpa only [mul_assoc, one_mul, mul_one] using
          congrArg (fun z => (x 4) * z * ((1 : G))) r48
      exact (((((step0).trans step1).trans step2).trans step3).trans step4).trans step5
    have hb : x 7 * x 1 * x 6 * x 4 * x 1 = x 1 * x 7 * x 1 := by
      have step0 : x 7 * x 1 * x 6 * x 4 * x 1 = x 1 * x 7 * x 1 := by
        simpa only [mul_assoc, one_mul, mul_one] using
          congrArg (fun z => ((1 : G)) * z * (x 1)) r55
      exact step0
    exact ha.symm.trans hb
  have r144 : x 9 * x 8 * x 9 = x 3 * x 7 * x 3 := by
    have ha : x 3 * x 7 * x 3 * x 9 * x 9 = x 9 * x 8 * x 9 := by
      have step0 : x 3 * x 7 * x 3 * x 9 * x 9 = x 9 * x 8 * x 9 := by
        simpa only [mul_assoc, one_mul, mul_one] using
          congrArg (fun z => ((1 : G)) * z * (x 9)) r59
      exact step0
    have hb : x 3 * x 7 * x 3 * x 9 * x 9 = x 3 * x 7 * x 3 := by
      have step0 : x 3 * x 7 * x 3 * x 9 * x 9 = x 3 * x 7 * x 3 := by
        simpa only [mul_assoc, one_mul, mul_one] using
          congrArg (fun z => (x 3 * x 7 * x 3) * z * ((1 : G))) r9
      exact step0
    exact ha.symm.trans hb
  have r159 : x 8 * x 9 * x 8 = x 2 * x 6 * x 2 := by
    have ha : x 2 * x 6 * x 2 * x 8 * x 8 = x 8 * x 9 * x 8 := by
      have step0 : x 2 * x 6 * x 2 * x 8 * x 8 = x 8 * x 9 * x 8 := by
        simpa only [mul_assoc, one_mul, mul_one] using
          congrArg (fun z => ((1 : G)) * z * (x 8)) r62
      exact step0
    have hb : x 2 * x 6 * x 2 * x 8 * x 8 = x 2 * x 6 * x 2 := by
      have step0 : x 2 * x 6 * x 2 * x 8 * x 8 = x 2 * x 6 * x 2 := by
        simpa only [mul_assoc, one_mul, mul_one] using
          congrArg (fun z => (x 2 * x 6 * x 2) * z * ((1 : G))) r8
      exact step0
    exact ha.symm.trans hb
  have r341 : x 6 * x 7 * x 2 * x 3 = x 1 * x 7 * x 2 * x 4 := by
    have ha : x 7 * x 1 * x 6 * x 4 * x 2 * x 4 = x 6 * x 7 * x 2 * x 3 := by
      have step0 : x 7 * x 1 * x 6 * x 4 * x 2 * x 4 = x 7 * x 1 * x 6 * x 0 * x 1 * x 0 := by
        simpa only [mul_assoc, one_mul, mul_one] using
          congrArg (fun z => (x 7 * x 1 * x 6) * z * ((1 : G))) r104
      have step1 : x 7 * x 1 * x 6 * x 0 * x 1 * x 0 = x 6 * x 7 * x 1 * x 0 * x 1 * x 0 := by
        simpa only [mul_assoc, one_mul, mul_one] using
          congrArg (fun z => ((1 : G)) * z * (x 0 * x 1 * x 0)) r78
      have step2 : x 6 * x 7 * x 1 * x 0 * x 1 * x 0 = x 6 * x 7 * x 0 * x 2 * x 3 * x 0 := by
        simpa only [mul_assoc, one_mul, mul_one] using
          congrArg (fun z => (x 6 * x 7) * z * (x 0)) r84
      have step3 : x 6 * x 7 * x 0 * x 2 * x 3 * x 0 = x 6 * x 7 * x 0 * x 2 * x 0 * x 3 := by
        simpa only [mul_assoc, one_mul, mul_one] using
          congrArg (fun z => (x 6 * x 7 * x 0 * x 2) * z * ((1 : G))) r35
      have step4 : x 6 * x 7 * x 0 * x 2 * x 0 * x 3 = x 6 * x 7 * x 0 * x 0 * x 2 * x 3 := by
        simpa only [mul_assoc, one_mul, mul_one] using
          congrArg (fun z => (x 6 * x 7 * x 0) * z * (x 3)) r33
      have step5 : x 6 * x 7 * x 0 * x 0 * x 2 * x 3 = x 6 * x 7 * x 2 * x 3 := by
        simpa only [mul_assoc, one_mul, mul_one] using
          congrArg (fun z => (x 6 * x 7) * z * (x 2 * x 3)) r0
      exact (((((step0).trans step1).trans step2).trans step3).trans step4).trans step5
    have hb : x 7 * x 1 * x 6 * x 4 * x 2 * x 4 = x 1 * x 7 * x 2 * x 4 := by
      have step0 : x 7 * x 1 * x 6 * x 4 * x 2 * x 4 = x 1 * x 7 * x 2 * x 4 := by
        simpa only [mul_assoc, one_mul, mul_one] using
          congrArg (fun z => ((1 : G)) * z * (x 2 * x 4)) r55
      exact step0
    exact ha.symm.trans hb
  have r634 : x 3 * x 7 * x 3 * x 8 = x 2 * x 6 * x 2 * x 9 := by
    have ha : x 9 * x 8 * x 9 * x 8 = x 3 * x 7 * x 3 * x 8 := by
      have step0 : x 9 * x 8 * x 9 * x 8 = x 8 * x 9 * x 8 * x 9 := by
        simpa only [mul_assoc, one_mul, mul_one] using
          congrArg (fun z => ((1 : G)) * z * ((1 : G))) r32
      have step1 : x 8 * x 9 * x 8 * x 9 = x 8 * x 3 * x 7 * x 3 := by
        simpa only [mul_assoc, one_mul, mul_one] using
          congrArg (fun z => (x 8) * z * ((1 : G))) r144
      have step2 : x 8 * x 3 * x 7 * x 3 = x 3 * x 8 * x 7 * x 3 := by
        simpa only [mul_assoc, one_mul, mul_one] using
          congrArg (fun z => ((1 : G)) * z * (x 7 * x 3)) r13
      have step3 : x 3 * x 8 * x 7 * x 3 = x 3 * x 7 * x 8 * x 3 := by
        simpa only [mul_assoc, one_mul, mul_one] using
          congrArg (fun z => (x 3) * z * (x 3)) r17
      have step4 : x 3 * x 7 * x 8 * x 3 = x 3 * x 7 * x 3 * x 8 := by
        simpa only [mul_assoc, one_mul, mul_one] using
          congrArg (fun z => (x 3 * x 7) * z * ((1 : G))) r13
      exact ((((step0).trans step1).trans step2).trans step3).trans step4
    have hb : x 9 * x 8 * x 9 * x 8 = x 2 * x 6 * x 2 * x 9 := by
      have step0 : x 9 * x 8 * x 9 * x 8 = x 9 * x 2 * x 6 * x 2 := by
        simpa only [mul_assoc, one_mul, mul_one] using
          congrArg (fun z => (x 9) * z * ((1 : G))) r159
      have step1 : x 9 * x 2 * x 6 * x 2 = x 2 * x 9 * x 6 * x 2 := by
        simpa only [mul_assoc, one_mul, mul_one] using
          congrArg (fun z => ((1 : G)) * z * (x 6 * x 2)) r20
      have step2 : x 2 * x 9 * x 6 * x 2 = x 2 * x 6 * x 9 * x 2 := by
        simpa only [mul_assoc, one_mul, mul_one] using
          congrArg (fun z => (x 2) * z * (x 2)) r24
      have step3 : x 2 * x 6 * x 9 * x 2 = x 2 * x 6 * x 2 * x 9 := by
        simpa only [mul_assoc, one_mul, mul_one] using
          congrArg (fun z => (x 2 * x 6) * z * ((1 : G))) r20
      exact (((step0).trans step1).trans step2).trans step3
    exact ha.symm.trans hb
  have ha : x 2 * x 3 * x 6 * x 7 * x 2 * x 3 * x 6 * x 7 * x 2 * x 3 = x 2 * x 6 * x 2 * x 9 := by
    have step0 : x 2 * x 3 * x 6 * x 7 * x 2 * x 3 * x 6 * x 7 * x 2 * x 3 = x 2 * x 3 * x 1 * x 7 * x 2 * x 4 * x 6 * x 7 * x 2 * x 3 := by
      simpa only [mul_assoc, one_mul, mul_one] using
        congrArg (fun z => (x 2 * x 3) * z * (x 6 * x 7 * x 2 * x 3)) r341
    have step1 : x 2 * x 3 * x 1 * x 7 * x 2 * x 4 * x 6 * x 7 * x 2 * x 3 = x 2 * x 1 * x 3 * x 7 * x 2 * x 4 * x 6 * x 7 * x 2 * x 3 := by
      simpa only [mul_assoc, one_mul, mul_one] using
        congrArg (fun z => (x 2) * z * (x 7 * x 2 * x 4 * x 6 * x 7 * x 2 * x 3)) r36
    have step2 : x 2 * x 1 * x 3 * x 7 * x 2 * x 4 * x 6 * x 7 * x 2 * x 3 = x 1 * x 2 * x 3 * x 7 * x 2 * x 4 * x 6 * x 7 * x 2 * x 3 := by
      simpa only [mul_assoc, one_mul, mul_one] using
        congrArg (fun z => ((1 : G)) * z * (x 3 * x 7 * x 2 * x 4 * x 6 * x 7 * x 2 * x 3)) r34
    have step3 : x 1 * x 2 * x 3 * x 7 * x 2 * x 4 * x 6 * x 7 * x 2 * x 3 = x 0 * x 1 * x 0 * x 7 * x 2 * x 4 * x 6 * x 7 * x 2 * x 3 := by
      simpa only [mul_assoc, one_mul, mul_one] using
        congrArg (fun z => ((1 : G)) * z * (x 7 * x 2 * x 4 * x 6 * x 7 * x 2 * x 3)) r79
    have step4 : x 0 * x 1 * x 0 * x 7 * x 2 * x 4 * x 6 * x 7 * x 2 * x 3 = x 0 * x 1 * x 0 * x 7 * x 2 * x 1 * x 7 * x 1 * x 2 * x 3 := by
      simpa only [mul_assoc, one_mul, mul_one] using
        congrArg (fun z => (x 0 * x 1 * x 0 * x 7 * x 2) * z * (x 2 * x 3)) r124
    have step5 : x 0 * x 1 * x 0 * x 7 * x 2 * x 1 * x 7 * x 1 * x 2 * x 3 = x 0 * x 1 * x 0 * x 7 * x 1 * x 2 * x 7 * x 1 * x 2 * x 3 := by
      simpa only [mul_assoc, one_mul, mul_one] using
        congrArg (fun z => (x 0 * x 1 * x 0 * x 7) * z * (x 7 * x 1 * x 2 * x 3)) r34
    have step6 : x 0 * x 1 * x 0 * x 7 * x 1 * x 2 * x 7 * x 1 * x 2 * x 3 = x 0 * x 1 * x 0 * x 7 * x 1 * x 2 * x 7 * x 0 * x 1 * x 0 := by
      simpa only [mul_assoc, one_mul, mul_one] using
        congrArg (fun z => (x 0 * x 1 * x 0 * x 7 * x 1 * x 2 * x 7) * z * ((1 : G))) r79
    have step7 : x 0 * x 1 * x 0 * x 7 * x 1 * x 2 * x 7 * x 0 * x 1 * x 0 = x 0 * x 1 * x 0 * x 7 * x 1 * x 2 * x 0 * x 7 * x 1 * x 0 := by
      simpa only [mul_assoc, one_mul, mul_one] using
        congrArg (fun z => (x 0 * x 1 * x 0 * x 7 * x 1 * x 2) * z * (x 1 * x 0)) r45
    have step8 : x 0 * x 1 * x 0 * x 7 * x 1 * x 2 * x 0 * x 7 * x 1 * x 0 = x 0 * x 1 * x 0 * x 7 * x 1 * x 0 * x 2 * x 7 * x 1 * x 0 := by
      simpa only [mul_assoc, one_mul, mul_one] using
        congrArg (fun z => (x 0 * x 1 * x 0 * x 7 * x 1) * z * (x 7 * x 1 * x 0)) r33
    have step9 : x 0 * x 1 * x 0 * x 7 * x 1 * x 0 * x 2 * x 7 * x 1 * x 0 = x 0 * x 1 * x 0 * x 7 * x 0 * x 1 * x 3 * x 7 * x 1 * x 0 := by
      simpa only [mul_assoc, one_mul, mul_one] using
        congrArg (fun z => (x 0 * x 1 * x 0 * x 7) * z * (x 7 * x 1 * x 0)) r83
    have step10 : x 0 * x 1 * x 0 * x 7 * x 0 * x 1 * x 3 * x 7 * x 1 * x 0 = x 0 * x 1 * x 0 * x 0 * x 7 * x 1 * x 3 * x 7 * x 1 * x 0 := by
      simpa only [mul_assoc, one_mul, mul_one] using
        congrArg (fun z => (x 0 * x 1 * x 0) * z * (x 1 * x 3 * x 7 * x 1 * x 0)) r45
    have step11 : x 0 * x 1 * x 0 * x 0 * x 7 * x 1 * x 3 * x 7 * x 1 * x 0 = x 0 * x 1 * x 7 * x 1 * x 3 * x 7 * x 1 * x 0 := by
      simpa only [mul_assoc, one_mul, mul_one] using
        congrArg (fun z => (x 0 * x 1) * z * (x 7 * x 1 * x 3 * x 7 * x 1 * x 0)) r0
    have step12 : x 0 * x 1 * x 7 * x 1 * x 3 * x 7 * x 1 * x 0 = x 0 * x 1 * x 3 * x 6 * x 7 * x 3 * x 1 * x 0 := by
      simpa only [mul_assoc, one_mul, mul_one] using
        congrArg (fun z => (x 0 * x 1) * z * (x 1 * x 0)) r123
    have step13 : x 0 * x 1 * x 3 * x 6 * x 7 * x 3 * x 1 * x 0 = x 0 * x 1 * x 3 * x 6 * x 7 * x 1 * x 3 * x 0 := by
      simpa only [mul_assoc, one_mul, mul_one] using
        congrArg (fun z => (x 0 * x 1 * x 3 * x 6 * x 7) * z * (x 0)) r36
    have step14 : x 0 * x 1 * x 3 * x 6 * x 7 * x 1 * x 3 * x 0 = x 0 * x 1 * x 3 * x 6 * x 7 * x 1 * x 0 * x 3 := by
      simpa only [mul_assoc, one_mul, mul_one] using
        congrArg (fun z => (x 0 * x 1 * x 3 * x 6 * x 7 * x 1) * z * ((1 : G))) r35
    have step15 : x 0 * x 1 * x 3 * x 6 * x 7 * x 1 * x 0 * x 3 = x 0 * x 1 * x 3 * x 6 * x 7 * x 0 * x 1 * x 2 := by
      simpa only [mul_assoc, one_mul, mul_one] using
        congrArg (fun z => (x 0 * x 1 * x 3 * x 6 * x 7) * z * ((1 : G))) r80
    have step16 : x 0 * x 1 * x 3 * x 6 * x 7 * x 0 * x 1 * x 2 = x 0 * x 1 * x 3 * x 6 * x 0 * x 7 * x 1 * x 2 := by
      simpa only [mul_assoc, one_mul, mul_one] using
        congrArg (fun z => (x 0 * x 1 * x 3 * x 6) * z * (x 1 * x 2)) r45
    have step17 : x 0 * x 1 * x 3 * x 6 * x 0 * x 7 * x 1 * x 2 = x 0 * x 1 * x 3 * x 0 * x 5 * x 6 * x 1 * x 2 := by
      simpa only [mul_assoc, one_mul, mul_one] using
        congrArg (fun z => (x 0 * x 1 * x 3) * z * (x 1 * x 2)) r86
    have step18 : x 0 * x 1 * x 3 * x 0 * x 5 * x 6 * x 1 * x 2 = x 0 * x 1 * x 0 * x 3 * x 5 * x 6 * x 1 * x 2 := by
      simpa only [mul_assoc, one_mul, mul_one] using
        congrArg (fun z => (x 0 * x 1) * z * (x 5 * x 6 * x 1 * x 2)) r35
    have step19 : x 0 * x 1 * x 0 * x 3 * x 5 * x 6 * x 1 * x 2 = x 0 * x 1 * x 0 * x 3 * x 5 * x 1 * x 6 * x 2 := by
      simpa only [mul_assoc, one_mul, mul_one] using
        congrArg (fun z => (x 0 * x 1 * x 0 * x 3 * x 5) * z * (x 2)) r42
    have step20 : x 0 * x 1 * x 0 * x 3 * x 5 * x 1 * x 6 * x 2 = x 0 * x 1 * x 0 * x 3 * x 1 * x 9 * x 6 * x 2 := by
      simpa only [mul_assoc, one_mul, mul_one] using
        congrArg (fun z => (x 0 * x 1 * x 0 * x 3) * z * (x 6 * x 2)) r61
    have step21 : x 0 * x 1 * x 0 * x 3 * x 1 * x 9 * x 6 * x 2 = x 0 * x 1 * x 0 * x 3 * x 1 * x 6 * x 9 * x 2 := by
      simpa only [mul_assoc, one_mul, mul_one] using
        congrArg (fun z => (x 0 * x 1 * x 0 * x 3 * x 1) * z * (x 2)) r24
    have step22 : x 0 * x 1 * x 0 * x 3 * x 1 * x 6 * x 9 * x 2 = x 0 * x 1 * x 0 * x 3 * x 1 * x 6 * x 2 * x 9 := by
      simpa only [mul_assoc, one_mul, mul_one] using
        congrArg (fun z => (x 0 * x 1 * x 0 * x 3 * x 1 * x 6) * z * ((1 : G))) r20
    have step23 : x 0 * x 1 * x 0 * x 3 * x 1 * x 6 * x 2 * x 9 = x 0 * x 1 * x 0 * x 1 * x 3 * x 6 * x 2 * x 9 := by
      simpa only [mul_assoc, one_mul, mul_one] using
        congrArg (fun z => (x 0 * x 1 * x 0) * z * (x 6 * x 2 * x 9)) r36
    have step24 : x 0 * x 1 * x 0 * x 1 * x 3 * x 6 * x 2 * x 9 = x 0 * x 0 * x 2 * x 3 * x 3 * x 6 * x 2 * x 9 := by
      simpa only [mul_assoc, one_mul, mul_one] using
        congrArg (fun z => (x 0) * z * (x 3 * x 6 * x 2 * x 9)) r84
    have step25 : x 0 * x 0 * x 2 * x 3 * x 3 * x 6 * x 2 * x 9 = x 2 * x 3 * x 3 * x 6 * x 2 * x 9 := by
      simpa only [mul_assoc, one_mul, mul_one] using
        congrArg (fun z => ((1 : G)) * z * (x 2 * x 3 * x 3 * x 6 * x 2 * x 9)) r0
    have step26 : x 2 * x 3 * x 3 * x 6 * x 2 * x 9 = x 2 * x 6 * x 2 * x 9 := by
      simpa only [mul_assoc, one_mul, mul_one] using
        congrArg (fun z => (x 2) * z * (x 6 * x 2 * x 9)) r3
    exact ((((((((((((((((((((((((((step0).trans step1).trans step2).trans step3).trans step4).trans step5).trans step6).trans step7).trans step8).trans step9).trans step10).trans step11).trans step12).trans step13).trans step14).trans step15).trans step16).trans step17).trans step18).trans step19).trans step20).trans step21).trans step22).trans step23).trans step24).trans step25).trans step26
  have hb : x 8 * x 9 * x 8 * x 9 = x 2 * x 6 * x 2 * x 9 := by
    have step0 : x 8 * x 9 * x 8 * x 9 = x 8 * x 3 * x 7 * x 3 := by
      simpa only [mul_assoc, one_mul, mul_one] using
        congrArg (fun z => (x 8) * z * ((1 : G))) r144
    have step1 : x 8 * x 3 * x 7 * x 3 = x 3 * x 8 * x 7 * x 3 := by
      simpa only [mul_assoc, one_mul, mul_one] using
        congrArg (fun z => ((1 : G)) * z * (x 7 * x 3)) r13
    have step2 : x 3 * x 8 * x 7 * x 3 = x 3 * x 7 * x 8 * x 3 := by
      simpa only [mul_assoc, one_mul, mul_one] using
        congrArg (fun z => (x 3) * z * (x 3)) r17
    have step3 : x 3 * x 7 * x 8 * x 3 = x 3 * x 7 * x 3 * x 8 := by
      simpa only [mul_assoc, one_mul, mul_one] using
        congrArg (fun z => (x 3 * x 7) * z * ((1 : G))) r13
    have step4 : x 3 * x 7 * x 3 * x 8 = x 2 * x 6 * x 2 * x 9 := by
      simpa only [mul_assoc, one_mul, mul_one] using
        congrArg (fun z => ((1 : G)) * z * ((1 : G))) r634
    exact ((((step0).trans step1).trans step2).trans step3).trans step4
  simpa only [mul_assoc] using ha.trans hb.symm

end ReeF4.LocalBlockInput.PairRigidity.FixedCollection.B2WordCalculation
