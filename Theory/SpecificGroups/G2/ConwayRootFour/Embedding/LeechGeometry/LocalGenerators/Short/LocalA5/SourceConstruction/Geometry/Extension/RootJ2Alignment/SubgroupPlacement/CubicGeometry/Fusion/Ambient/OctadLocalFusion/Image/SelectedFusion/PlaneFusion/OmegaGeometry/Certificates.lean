/-
Copyright (c) 2026 Gerald Höhn and the ATLAS contributors. All rights reserved.
Covered by the ATLAS Research and Attribution License 1.0 (LICENSES/ATLAS.txt).
The Siegel coordinates and trace method are reused from the attributed
BinaryEightObstruction.Simplicity.Geometry.Coordinates and Certificates modules.
The anisotropic orbit words and pair checker are new.
-/
module

public import Theory.SpecificGroups.ClassicalOrthogonal.SplitOdd.BinaryEightObstruction.Simplicity.Geometry.Coordinates

/-!
# Siegel transport of anisotropic pairs in binary split eight-space

The first trace family transports `e₀+f₀` to every nonsingular vector. The
second fixes this vector and transports `e₀+e₁+f₁` to every nonsingular
partner with polar value one. Its extra generator swaps `e₀,f₀` and `e₁,f₁`
simultaneously and is a word of six actual Siegel generators.

All 256 possible vectors are checked through the existing decoder. Explicit
intermediate vectors make the kernel check each root only once per step.
The consumer `OmegaGeometry` uses these ordered-pair transports on the moved
planes of cubics. Source: Aschbacher, *Sporadic Groups* (1994), §25 and §46.
See `source/README.md` for reproduction and representative measurements.
-/

public section
open ClassicalOrthogonal.BinaryEightObstruction.Simplicity
open ClassicalOrthogonal.BinaryEightObstruction.Simplicity.Geometry
namespace ClassicalOrthogonal.BinaryEightObstruction.Simplicity.Geometry.AnisotropicPairs
private abbrev PairTrace := List (Fin 24 × ℕ × ℕ)
private def checkPair : ℕ → ℕ → ℕ → ℕ → PairTrace → Bool
  | x, y, u, v, [] => decide (x = u ∧ y = v)
  | x, y, u, v, (r, xn, yn) :: tail =>
      decide (stepCode r x = xn ∧ stepCode r y = yn) && checkPair xn yn u v tail
private noncomputable def pairElement : PairTrace → E
  | [] => 1
  | (r, _, _) :: tail => pairElement tail * generator r

private theorem pair_action (x y u v : ℕ) (trace : PairTrace)
    (h : checkPair x y u v trace = true) :
    linear (pairElement trace) (decode x) = decode u ∧
      linear (pairElement trace) (decode y) = decode v := by
  induction trace generalizing x y with
  | nil =>
    have he : x = u ∧ y = v := of_decide_eq_true h
    exact ⟨congrArg decode he.1, congrArg decode he.2⟩
  | cons s tail ih =>
    rcases s with ⟨r, xn, yn⟩
    simp only [checkPair, Bool.and_eq_true, decide_eq_true_eq] at h
    have hh := ih xn yn h.2
    constructor
    · change linear (pairElement tail) (linear (generator r) (decode x)) = _
      rw [generator_action, ← decode_step, h.1.1]
      exact hh.1
    · change linear (pairElement tail) (linear (generator r) (decode y)) = _
      rw [generator_action, ← decode_step, h.1.2]
      exact hh.2

private def allPathsTable : Fin 16 → Fin 16 → Trace := ![
  ![[],
    [],
    [],
    [],
    [],
    [],
    [],
    [],
    [],
    [],
    [],
    [],
    [],
    [],
    [],
    []],
  ![[],
    [],
    [],
    [(0, 19)],
    [],
    [(1, 21)],
    [],
    [(0, 19), (1, 23)],
    [],
    [(2, 25)],
    [],
    [(0, 19), (2, 27)],
    [],
    [(1, 21), (2, 29)],
    [],
    [(0, 19), (1, 23), (2, 31)]],
  ![[],
    [],
    [(0, 19), (3, 50), (8, 34)],
    [(0, 19), (18, 35)],
    [],
    [],
    [(0, 19), (1, 23), (3, 54), (8, 38)],
    [(0, 19), (1, 23), (18, 39)],
    [],
    [],
    [(0, 19), (2, 27), (3, 58), (8, 42)],
    [(0, 19), (2, 27), (18, 43)],
    [],
    [],
    [(0, 19), (1, 23), (2, 31), (3, 62), (8, 46)],
    [(0, 19), (1, 23), (2, 31), (18, 47)]],
  ![[],
    [(3, 49)],
    [(0, 19), (3, 50)],
    [],
    [],
    [(1, 21), (3, 53)],
    [(0, 19), (1, 23), (3, 54)],
    [],
    [],
    [(2, 25), (3, 57)],
    [(0, 19), (2, 27), (3, 58)],
    [],
    [],
    [(1, 21), (2, 29), (3, 61)],
    [(0, 19), (1, 23), (2, 31), (3, 62)],
    []],
  ![[],
    [],
    [],
    [],
    [(1, 21), (4, 84), (12, 68)],
    [(1, 21), (19, 69)],
    [(0, 19), (1, 23), (4, 86), (12, 70)],
    [(0, 19), (1, 23), (19, 71)],
    [],
    [],
    [],
    [],
    [(1, 21), (2, 29), (4, 92), (12, 76)],
    [(1, 21), (2, 29), (19, 77)],
    [(0, 19), (1, 23), (2, 31), (4, 94), (12, 78)],
    [(0, 19), (1, 23), (2, 31), (19, 79)]],
  ![[],
    [(4, 81)],
    [],
    [(0, 19), (4, 83)],
    [(1, 21), (4, 84)],
    [],
    [(0, 19), (1, 23), (4, 86)],
    [],
    [],
    [(2, 25), (4, 89)],
    [],
    [(0, 19), (2, 27), (4, 91)],
    [(1, 21), (2, 29), (4, 92)],
    [],
    [(0, 19), (1, 23), (2, 31), (4, 94)],
    []],
  ![[],
    [],
    [(0, 19), (3, 50), (4, 114), (8, 98)],
    [(0, 19), (4, 83), (18, 99)],
    [(1, 21), (3, 53), (4, 116), (8, 100)],
    [(1, 21), (3, 53), (19, 101)],
    [],
    [],
    [],
    [],
    [(0, 19), (2, 27), (3, 58), (4, 122), (8, 106)],
    [(0, 19), (2, 27), (4, 91), (18, 107)],
    [(1, 21), (2, 29), (3, 61), (4, 124), (8, 108)],
    [(1, 21), (2, 29), (3, 61), (19, 109)],
    [],
    []],
  ![[],
    [(3, 49), (4, 113)],
    [(0, 19), (3, 50), (4, 114)],
    [],
    [(1, 21), (3, 53), (4, 116)],
    [],
    [],
    [(0, 19), (1, 23), (21, 119)],
    [],
    [(2, 25), (3, 57), (4, 121)],
    [(0, 19), (2, 27), (3, 58), (4, 122)],
    [],
    [(1, 21), (2, 29), (3, 61), (4, 124)],
    [],
    [],
    [(0, 19), (1, 23), (2, 31), (21, 127)]],
  ![[],
    [],
    [],
    [],
    [],
    [],
    [],
    [],
    [(2, 25), (5, 152), (15, 136)],
    [(2, 25), (20, 137)],
    [(0, 19), (2, 27), (5, 154), (15, 138)],
    [(0, 19), (2, 27), (20, 139)],
    [(1, 21), (2, 29), (5, 156), (15, 140)],
    [(1, 21), (2, 29), (20, 141)],
    [(0, 19), (1, 23), (2, 31), (5, 158), (15, 142)],
    [(0, 19), (1, 23), (2, 31), (20, 143)]],
  ![[],
    [(5, 145)],
    [],
    [(0, 19), (5, 147)],
    [],
    [(1, 21), (5, 149)],
    [],
    [(0, 19), (1, 23), (5, 151)],
    [(2, 25), (5, 152)],
    [],
    [(0, 19), (2, 27), (5, 154)],
    [],
    [(1, 21), (2, 29), (5, 156)],
    [],
    [(0, 19), (1, 23), (2, 31), (5, 158)],
    []],
  ![[],
    [],
    [(0, 19), (3, 50), (5, 178), (8, 162)],
    [(0, 19), (5, 147), (18, 163)],
    [],
    [],
    [(0, 19), (1, 23), (3, 54), (5, 182), (8, 166)],
    [(0, 19), (1, 23), (5, 151), (18, 167)],
    [(2, 25), (3, 57), (5, 184), (8, 168)],
    [(2, 25), (3, 57), (20, 169)],
    [],
    [],
    [(1, 21), (2, 29), (3, 61), (5, 188), (8, 172)],
    [(1, 21), (2, 29), (3, 61), (20, 173)],
    [],
    []],
  ![[],
    [(3, 49), (5, 177)],
    [(0, 19), (3, 50), (5, 178)],
    [],
    [],
    [(1, 21), (3, 53), (5, 181)],
    [(0, 19), (1, 23), (3, 54), (5, 182)],
    [],
    [(2, 25), (3, 57), (5, 184)],
    [],
    [],
    [(0, 19), (2, 27), (22, 187)],
    [(1, 21), (2, 29), (3, 61), (5, 188)],
    [],
    [],
    [(0, 19), (1, 23), (2, 31), (22, 191)]],
  ![[],
    [],
    [],
    [],
    [(1, 21), (4, 84), (5, 212), (12, 196)],
    [(1, 21), (5, 149), (19, 197)],
    [(0, 19), (1, 23), (4, 86), (5, 214), (12, 198)],
    [(0, 19), (1, 23), (5, 151), (19, 199)],
    [(2, 25), (4, 89), (5, 216), (12, 200)],
    [(2, 25), (4, 89), (20, 201)],
    [(0, 19), (2, 27), (4, 91), (5, 218), (12, 202)],
    [(0, 19), (2, 27), (4, 91), (20, 203)],
    [],
    [],
    [],
    []],
  ![[],
    [(4, 81), (5, 209)],
    [],
    [(0, 19), (4, 83), (5, 211)],
    [(1, 21), (4, 84), (5, 212)],
    [],
    [(0, 19), (1, 23), (4, 86), (5, 214)],
    [],
    [(2, 25), (4, 89), (5, 216)],
    [],
    [(0, 19), (2, 27), (4, 91), (5, 218)],
    [],
    [],
    [(1, 21), (2, 29), (23, 221)],
    [],
    [(0, 19), (1, 23), (2, 31), (23, 223)]],
  ![[],
    [],
    [(0, 19), (3, 50), (4, 114), (5, 242), (8, 226)],
    [(0, 19), (4, 83), (5, 211), (18, 227)],
    [(1, 21), (3, 53), (4, 116), (5, 244), (8, 228)],
    [(1, 21), (3, 53), (5, 181), (19, 229)],
    [],
    [],
    [(2, 25), (3, 57), (4, 121), (5, 248), (8, 232)],
    [(2, 25), (3, 57), (4, 121), (20, 233)],
    [],
    [],
    [],
    [],
    [(0, 19), (1, 23), (2, 31), (3, 62), (8, 46), (23, 238)],
    [(0, 19), (1, 23), (2, 31), (18, 47), (23, 239)]],
  ![[],
    [(3, 49), (4, 113), (5, 241)],
    [(0, 19), (3, 50), (4, 114), (5, 242)],
    [],
    [(1, 21), (3, 53), (4, 116), (5, 244)],
    [],
    [],
    [(0, 19), (1, 23), (5, 151), (21, 247)],
    [(2, 25), (3, 57), (4, 121), (5, 248)],
    [],
    [],
    [(0, 19), (2, 27), (4, 91), (22, 251)],
    [],
    [(1, 21), (2, 29), (3, 61), (23, 253)],
    [(0, 19), (1, 23), (2, 31), (3, 62), (23, 254)],
    []]]

private def allPaths (n : Byte) : Trace :=
  allPathsTable (Fin.ofNat 16 (n.val / 16)) (Fin.ofNat 16 n.val)

private def partnerPathsTable : Fin 16 → Fin 16 → PairTrace := ![
  ![[],
    [],
    [],
    [],
    [],
    [],
    [],
    [],
    [],
    [],
    [],
    [],
    [],
    [],
    [],
    []],
  ![[],
    [],
    [],
    [],
    [],
    [],
    [],
    [],
    [],
    [],
    [],
    [],
    [],
    [],
    [],
    []],
  ![[],
    [],
    [],
    [],
    [],
    [],
    [],
    [(6, 17, 39)],
    [],
    [],
    [],
    [(7, 17, 43)],
    [],
    [],
    [],
    [(6, 17, 39), (7, 17, 47)]],
  ![[],
    [],
    [(0, 19, 34), (18, 35, 50), (0, 34, 49), (3, 35, 17), (8, 49, 19), (3, 17, 50)],
    [],
    [],
    [],
    [(6, 17, 39), (0, 19, 38), (18, 35, 54), (0, 34, 53), (3, 35, 21), (8, 49, 23), (3, 17, 54)],
    [],
    [],
    [],
    [(7, 17, 43), (0, 19, 42), (18, 35, 58), (0, 34, 57), (3, 35, 25), (8, 49, 27), (3, 17, 58)],
    [],
    [],
    [],
    [(6, 17, 39), (7, 17, 47), (0, 19, 46), (18, 35, 62), (0, 34, 61), (3, 35, 29), (8, 49, 31), (3, 17, 62)],
    []],
  ![[],
    [],
    [],
    [],
    [],
    [(6, 17, 39), (9, 17, 101), (13, 17, 69)],
    [],
    [(6, 17, 39), (21, 17, 71)],
    [],
    [],
    [],
    [],
    [],
    [(6, 17, 39), (7, 17, 47), (9, 17, 109), (13, 17, 77)],
    [],
    [(6, 17, 39), (7, 17, 47), (21, 17, 79)]],
  ![[],
    [],
    [],
    [],
    [(6, 17, 39), (9, 17, 101), (13, 17, 69), (0, 19, 69), (18, 35, 101), (0, 34, 100), (3, 35, 100), (8, 49, 116), (3, 17, 84)],
    [],
    [(6, 17, 39), (9, 17, 101), (0, 19, 100), (18, 35, 100), (0, 34, 101), (3, 35, 101), (8, 49, 119), (3, 17, 86)],
    [],
    [],
    [],
    [],
    [],
    [(6, 17, 39), (7, 17, 47), (9, 17, 109), (13, 17, 77), (0, 19, 77), (18, 35, 109), (0, 34, 108), (3, 35, 108), (8, 49, 124), (3, 17, 92)],
    [],
    [(6, 17, 39), (7, 17, 47), (9, 17, 109), (0, 19, 108), (18, 35, 108), (0, 34, 109), (3, 35, 109), (8, 49, 127), (3, 17, 94)],
    []],
  ![[],
    [],
    [],
    [(9, 17, 99)],
    [],
    [(6, 17, 39), (9, 17, 101)],
    [],
    [],
    [],
    [],
    [],
    [(7, 17, 43), (9, 17, 107)],
    [],
    [(6, 17, 39), (7, 17, 47), (9, 17, 109)],
    [],
    []],
  ![[],
    [],
    [(9, 17, 99), (0, 19, 98), (18, 35, 114), (0, 34, 113), (3, 35, 81), (8, 49, 83), (3, 17, 114)],
    [],
    [(6, 17, 39), (21, 17, 71), (0, 19, 71), (18, 35, 119), (0, 34, 116), (3, 35, 84), (8, 49, 84), (3, 17, 116)],
    [],
    [],
    [],
    [],
    [],
    [(7, 17, 43), (9, 17, 107), (0, 19, 106), (18, 35, 122), (0, 34, 121), (3, 35, 89), (8, 49, 91), (3, 17, 122)],
    [],
    [(6, 17, 39), (7, 17, 47), (21, 17, 79), (0, 19, 79), (18, 35, 127), (0, 34, 124), (3, 35, 92), (8, 49, 92), (3, 17, 124)],
    [],
    [],
    []],
  ![[],
    [],
    [],
    [],
    [],
    [],
    [],
    [],
    [],
    [(7, 17, 43), (10, 17, 169), (16, 17, 137)],
    [],
    [(7, 17, 43), (22, 17, 139)],
    [],
    [(6, 17, 39), (7, 17, 47), (10, 17, 173), (16, 17, 141)],
    [],
    [(6, 17, 39), (7, 17, 47), (22, 17, 143)]],
  ![[],
    [],
    [],
    [],
    [],
    [],
    [],
    [],
    [(7, 17, 43), (10, 17, 169), (16, 17, 137), (0, 19, 137), (18, 35, 169), (0, 34, 168), (3, 35, 168), (8, 49, 184), (3, 17, 152)],
    [],
    [(7, 17, 43), (10, 17, 169), (0, 19, 168), (18, 35, 168), (0, 34, 169), (3, 35, 169), (8, 49, 187), (3, 17, 154)],
    [],
    [(6, 17, 39), (7, 17, 47), (10, 17, 173), (16, 17, 141), (0, 19, 141), (18, 35, 173), (0, 34, 172), (3, 35, 172), (8, 49, 188), (3, 17, 156)],
    [],
    [(6, 17, 39), (7, 17, 47), (10, 17, 173), (0, 19, 172), (18, 35, 172), (0, 34, 173), (3, 35, 173), (8, 49, 191), (3, 17, 158)],
    []],
  ![[],
    [],
    [],
    [(10, 17, 163)],
    [],
    [],
    [],
    [(6, 17, 39), (10, 17, 167)],
    [],
    [(7, 17, 43), (10, 17, 169)],
    [],
    [],
    [],
    [(6, 17, 39), (7, 17, 47), (10, 17, 173)],
    [],
    []],
  ![[],
    [],
    [(10, 17, 163), (0, 19, 162), (18, 35, 178), (0, 34, 177), (3, 35, 145), (8, 49, 147), (3, 17, 178)],
    [],
    [],
    [],
    [(6, 17, 39), (10, 17, 167), (0, 19, 166), (18, 35, 182), (0, 34, 181), (3, 35, 149), (8, 49, 151), (3, 17, 182)],
    [],
    [(7, 17, 43), (22, 17, 139), (0, 19, 139), (18, 35, 187), (0, 34, 184), (3, 35, 152), (8, 49, 152), (3, 17, 184)],
    [],
    [],
    [],
    [(6, 17, 39), (7, 17, 47), (22, 17, 143), (0, 19, 143), (18, 35, 191), (0, 34, 188), (3, 35, 156), (8, 49, 156), (3, 17, 188)],
    [],
    [],
    []],
  ![[],
    [],
    [],
    [],
    [],
    [(6, 17, 39), (9, 17, 101), (10, 17, 229), (13, 17, 197)],
    [],
    [(6, 17, 39), (10, 17, 167), (21, 17, 199)],
    [],
    [(7, 17, 43), (9, 17, 107), (10, 17, 233), (13, 17, 201)],
    [],
    [(7, 17, 43), (9, 17, 107), (22, 17, 203)],
    [],
    [],
    [],
    []],
  ![[],
    [],
    [],
    [],
    [(6, 17, 39), (9, 17, 101), (10, 17, 229), (13, 17, 197), (0, 19, 197), (18, 35, 229), (0, 34, 228), (3, 35, 228), (8, 49, 244), (3, 17, 212)],
    [],
    [(6, 17, 39), (9, 17, 101), (10, 17, 229), (0, 19, 228), (18, 35, 228), (0, 34, 229), (3, 35, 229), (8, 49, 247), (3, 17, 214)],
    [],
    [(7, 17, 43), (9, 17, 107), (10, 17, 233), (13, 17, 201), (0, 19, 201), (18, 35, 233), (0, 34, 232), (3, 35, 232), (8, 49, 248), (3, 17, 216)],
    [],
    [(7, 17, 43), (9, 17, 107), (10, 17, 233), (0, 19, 232), (18, 35, 232), (0, 34, 233), (3, 35, 233), (8, 49, 251), (3, 17, 218)],
    [],
    [],
    [],
    [],
    []],
  ![[],
    [],
    [],
    [(9, 17, 99), (10, 17, 227)],
    [],
    [(6, 17, 39), (9, 17, 101), (10, 17, 229)],
    [],
    [],
    [],
    [(7, 17, 43), (9, 17, 107), (10, 17, 233)],
    [],
    [],
    [],
    [],
    [],
    [(6, 17, 39), (7, 17, 47), (23, 17, 239)]],
  ![[],
    [],
    [(9, 17, 99), (10, 17, 227), (0, 19, 226), (18, 35, 242), (0, 34, 241), (3, 35, 209), (8, 49, 211), (3, 17, 242)],
    [],
    [(6, 17, 39), (10, 17, 167), (21, 17, 199), (0, 19, 199), (18, 35, 247), (0, 34, 244), (3, 35, 212), (8, 49, 212), (3, 17, 244)],
    [],
    [],
    [],
    [(7, 17, 43), (9, 17, 107), (22, 17, 203), (0, 19, 203), (18, 35, 251), (0, 34, 248), (3, 35, 216), (8, 49, 216), (3, 17, 248)],
    [],
    [],
    [],
    [],
    [],
    [(6, 17, 39), (7, 17, 47), (23, 17, 239), (0, 19, 238), (18, 35, 254), (0, 34, 253), (3, 35, 221), (8, 49, 223), (3, 17, 254)],
    []]]

private def partnerPaths (n : Byte) : PairTrace :=
  partnerPathsTable (Fin.ofNat 16 (n.val / 16)) (Fin.ofNat 16 n.val)

private theorem allPaths_checked : ∀ n : Byte,
    fastQ (decode n.val) = 1 → checkPath 17 n.val (allPaths n) = true := by
  decide +kernel

private theorem partnerPaths_checked : ∀ n : Byte,
    fastQ (decode n.val) = 1 → decode n.val (.inl 0) + decode n.val (.inr 0) = 1 →
    checkPair 17 35 17 n.val (partnerPaths n) = true := by
  decide +kernel

/-- Every vector of quadratic value one is reached by actual Siegel roots. -/
theorem nonsingular_transport (v : V) (hq : Q v = 1) :
    ∃ g : E, linear g (decode 17) = v := by
  have hc := allPaths_checked (encode v)
    (by rw [decode_encode, fastQ_eq]; exact hq)
  refine ⟨pathElement (allPaths (encode v)), ?_⟩
  have h := path_action 17 (encode v).val (allPaths (encode v)) hc
  rwa [decode_encode] at h

private theorem polar_base (v : V) :
    Q.polarBilin (decode 17) v = v (.inl 0) + v (.inr 0) := by
  have hd : decode 17 = ClassicalOrthogonal.e 0 + ClassicalOrthogonal.f 0 := by decide +kernel
  rw [hd, Quadratic.polar_swap, map_add, ClassicalOrthogonal.polarD_e,
    ClassicalOrthogonal.polarD_f, add_comm]

/-- The nonsingular-vector stabilizer is transitive on anisotropic partners. -/
theorem partner_transport (v : V) (hq : Q v = 1)
    (hp : Q.polarBilin (decode 17) v = 1) :
    ∃ g : E, linear g (decode 17) = decode 17 ∧ linear g (decode 35) = v := by
  have hc := partnerPaths_checked (encode v)
    (by rw [decode_encode, fastQ_eq]; exact hq)
    (by rw [decode_encode]; rwa [polar_base] at hp)
  refine ⟨pairElement (partnerPaths (encode v)), ?_, ?_⟩
  · exact (pair_action 17 35 17 (encode v).val (partnerPaths (encode v)) hc).1
  · simpa only [decode_encode] using
      (pair_action 17 35 17 (encode v).val (partnerPaths (encode v)) hc).2

/-- A fixed anisotropic ordered pair can be carried to any such pair inside Omega. -/
theorem pair_from_base (u v : V) (hu : Q u = 1) (hv : Q v = 1)
    (hp : Q.polarBilin u v = 1) :
    ∃ g : E, linear g (decode 17) = u ∧ linear g (decode 35) = v := by
  obtain ⟨g, hg⟩ := nonsingular_transport u hu
  have hq : Q (linear g⁻¹ v) = 1 := (linear_preserves g⁻¹ v).trans hv
  have hpol : Q.polarBilin (decode 17) (linear g⁻¹ v) = 1 := by
    have hh := linear_polar g (decode 17) (linear g⁻¹ v)
    change Q.polarBilin (linear g (decode 17)) ((linear g) ((linear g).symm v)) = _ at hh
    rw [hg, LinearEquiv.apply_symm_apply, hp] at hh
    exact hh.symm
  obtain ⟨k, hk, hkv⟩ := partner_transport (linear g⁻¹ v) hq hpol
  refine ⟨g * k, ?_, ?_⟩
  · change linear g (linear k (decode 17)) = u
    rw [hk, hg]
  · change linear g (linear k (decode 35)) = v
    rw [hkv]
    exact (linear g).apply_symm_apply v

/-- Ordered anisotropic pairs are conjugate under the actual elementary subgroup. -/
theorem pair_transport (u v x y : V) (hu : Q u = 1) (hv : Q v = 1)
    (huv : Q.polarBilin u v = 1) (hx : Q x = 1) (hy : Q y = 1)
    (hxy : Q.polarBilin x y = 1) :
    ∃ g : E, linear g u = x ∧ linear g v = y := by
  obtain ⟨g, hgu, hgv⟩ := pair_from_base u v hu hv huv
  obtain ⟨k, hkx, hky⟩ := pair_from_base x y hx hy hxy
  refine ⟨k * g⁻¹, ?_, ?_⟩
  · change linear k ((linear g).symm u) = x
    rw [← hgu, LinearEquiv.symm_apply_apply, hkx]
  · change linear k ((linear g).symm v) = y
    rw [← hgv, LinearEquiv.symm_apply_apply, hky]

end ClassicalOrthogonal.BinaryEightObstruction.Simplicity.Geometry.AnisotropicPairs
