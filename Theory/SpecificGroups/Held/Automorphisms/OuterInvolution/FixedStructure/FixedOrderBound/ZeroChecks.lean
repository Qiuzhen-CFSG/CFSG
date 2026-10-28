module

public import Theory.SpecificGroups.Held.Automorphisms.OuterInvolution.FixedStructure.FixedOrderBound.Data
public import Mathlib.Tactic.FinCases

/-!
# Bounded checks for the first centralizer orbit

The 630-point invariant sample distinguishes the 756 possible images of zero.
Each block checks sixteen vertices, sequentially, so the size of a single
kernel calculation stays bounded. The final block wraps modulo 2058.

Source: GLS3 Table 5.3p; the unchanged ATLAS Held graph.
-/

namespace Held.OuterInvolution.FixedStructure.FixedOrderBound
open Held.NormalizerGraph Held.NormalizerGraph.CardBound
open Held.LocalPairs.PairCoverage.IntervalNormalizer.Inner.Ambient.Max4.GraphBound

set_option Elab.async false

set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
private theorem zeroBlock0 : ∀ r : Fin 16,
    cell0_0 (vertex (0 * 16 + r.val)).val =
      if weight0 (vertex (0 * 16 + r.val)).val = 0 ∧
        neighborCount sample0_0 (vertex (0 * 16 + r.val)) = 140 then 1 else 0 := by
  simp only [neighborCount, adj_iff_fast]
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
private theorem zeroBlock1 : ∀ r : Fin 16,
    cell0_0 (vertex (1 * 16 + r.val)).val =
      if weight0 (vertex (1 * 16 + r.val)).val = 0 ∧
        neighborCount sample0_0 (vertex (1 * 16 + r.val)) = 140 then 1 else 0 := by
  simp only [neighborCount, adj_iff_fast]
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
private theorem zeroBlock2 : ∀ r : Fin 16,
    cell0_0 (vertex (2 * 16 + r.val)).val =
      if weight0 (vertex (2 * 16 + r.val)).val = 0 ∧
        neighborCount sample0_0 (vertex (2 * 16 + r.val)) = 140 then 1 else 0 := by
  simp only [neighborCount, adj_iff_fast]
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
private theorem zeroBlock3 : ∀ r : Fin 16,
    cell0_0 (vertex (3 * 16 + r.val)).val =
      if weight0 (vertex (3 * 16 + r.val)).val = 0 ∧
        neighborCount sample0_0 (vertex (3 * 16 + r.val)) = 140 then 1 else 0 := by
  simp only [neighborCount, adj_iff_fast]
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
private theorem zeroBlock4 : ∀ r : Fin 16,
    cell0_0 (vertex (4 * 16 + r.val)).val =
      if weight0 (vertex (4 * 16 + r.val)).val = 0 ∧
        neighborCount sample0_0 (vertex (4 * 16 + r.val)) = 140 then 1 else 0 := by
  simp only [neighborCount, adj_iff_fast]
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
private theorem zeroBlock5 : ∀ r : Fin 16,
    cell0_0 (vertex (5 * 16 + r.val)).val =
      if weight0 (vertex (5 * 16 + r.val)).val = 0 ∧
        neighborCount sample0_0 (vertex (5 * 16 + r.val)) = 140 then 1 else 0 := by
  simp only [neighborCount, adj_iff_fast]
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
private theorem zeroBlock6 : ∀ r : Fin 16,
    cell0_0 (vertex (6 * 16 + r.val)).val =
      if weight0 (vertex (6 * 16 + r.val)).val = 0 ∧
        neighborCount sample0_0 (vertex (6 * 16 + r.val)) = 140 then 1 else 0 := by
  simp only [neighborCount, adj_iff_fast]
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
private theorem zeroBlock7 : ∀ r : Fin 16,
    cell0_0 (vertex (7 * 16 + r.val)).val =
      if weight0 (vertex (7 * 16 + r.val)).val = 0 ∧
        neighborCount sample0_0 (vertex (7 * 16 + r.val)) = 140 then 1 else 0 := by
  simp only [neighborCount, adj_iff_fast]
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
private theorem zeroBlock8 : ∀ r : Fin 16,
    cell0_0 (vertex (8 * 16 + r.val)).val =
      if weight0 (vertex (8 * 16 + r.val)).val = 0 ∧
        neighborCount sample0_0 (vertex (8 * 16 + r.val)) = 140 then 1 else 0 := by
  simp only [neighborCount, adj_iff_fast]
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
private theorem zeroBlock9 : ∀ r : Fin 16,
    cell0_0 (vertex (9 * 16 + r.val)).val =
      if weight0 (vertex (9 * 16 + r.val)).val = 0 ∧
        neighborCount sample0_0 (vertex (9 * 16 + r.val)) = 140 then 1 else 0 := by
  simp only [neighborCount, adj_iff_fast]
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
private theorem zeroBlock10 : ∀ r : Fin 16,
    cell0_0 (vertex (10 * 16 + r.val)).val =
      if weight0 (vertex (10 * 16 + r.val)).val = 0 ∧
        neighborCount sample0_0 (vertex (10 * 16 + r.val)) = 140 then 1 else 0 := by
  simp only [neighborCount, adj_iff_fast]
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
private theorem zeroBlock11 : ∀ r : Fin 16,
    cell0_0 (vertex (11 * 16 + r.val)).val =
      if weight0 (vertex (11 * 16 + r.val)).val = 0 ∧
        neighborCount sample0_0 (vertex (11 * 16 + r.val)) = 140 then 1 else 0 := by
  simp only [neighborCount, adj_iff_fast]
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
private theorem zeroBlock12 : ∀ r : Fin 16,
    cell0_0 (vertex (12 * 16 + r.val)).val =
      if weight0 (vertex (12 * 16 + r.val)).val = 0 ∧
        neighborCount sample0_0 (vertex (12 * 16 + r.val)) = 140 then 1 else 0 := by
  simp only [neighborCount, adj_iff_fast]
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
private theorem zeroBlock13 : ∀ r : Fin 16,
    cell0_0 (vertex (13 * 16 + r.val)).val =
      if weight0 (vertex (13 * 16 + r.val)).val = 0 ∧
        neighborCount sample0_0 (vertex (13 * 16 + r.val)) = 140 then 1 else 0 := by
  simp only [neighborCount, adj_iff_fast]
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
private theorem zeroBlock14 : ∀ r : Fin 16,
    cell0_0 (vertex (14 * 16 + r.val)).val =
      if weight0 (vertex (14 * 16 + r.val)).val = 0 ∧
        neighborCount sample0_0 (vertex (14 * 16 + r.val)) = 140 then 1 else 0 := by
  simp only [neighborCount, adj_iff_fast]
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
private theorem zeroBlock15 : ∀ r : Fin 16,
    cell0_0 (vertex (15 * 16 + r.val)).val =
      if weight0 (vertex (15 * 16 + r.val)).val = 0 ∧
        neighborCount sample0_0 (vertex (15 * 16 + r.val)) = 140 then 1 else 0 := by
  simp only [neighborCount, adj_iff_fast]
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
private theorem zeroBlock16 : ∀ r : Fin 16,
    cell0_0 (vertex (16 * 16 + r.val)).val =
      if weight0 (vertex (16 * 16 + r.val)).val = 0 ∧
        neighborCount sample0_0 (vertex (16 * 16 + r.val)) = 140 then 1 else 0 := by
  simp only [neighborCount, adj_iff_fast]
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
private theorem zeroBlock17 : ∀ r : Fin 16,
    cell0_0 (vertex (17 * 16 + r.val)).val =
      if weight0 (vertex (17 * 16 + r.val)).val = 0 ∧
        neighborCount sample0_0 (vertex (17 * 16 + r.val)) = 140 then 1 else 0 := by
  simp only [neighborCount, adj_iff_fast]
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
private theorem zeroBlock18 : ∀ r : Fin 16,
    cell0_0 (vertex (18 * 16 + r.val)).val =
      if weight0 (vertex (18 * 16 + r.val)).val = 0 ∧
        neighborCount sample0_0 (vertex (18 * 16 + r.val)) = 140 then 1 else 0 := by
  simp only [neighborCount, adj_iff_fast]
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
private theorem zeroBlock19 : ∀ r : Fin 16,
    cell0_0 (vertex (19 * 16 + r.val)).val =
      if weight0 (vertex (19 * 16 + r.val)).val = 0 ∧
        neighborCount sample0_0 (vertex (19 * 16 + r.val)) = 140 then 1 else 0 := by
  simp only [neighborCount, adj_iff_fast]
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
private theorem zeroBlock20 : ∀ r : Fin 16,
    cell0_0 (vertex (20 * 16 + r.val)).val =
      if weight0 (vertex (20 * 16 + r.val)).val = 0 ∧
        neighborCount sample0_0 (vertex (20 * 16 + r.val)) = 140 then 1 else 0 := by
  simp only [neighborCount, adj_iff_fast]
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
private theorem zeroBlock21 : ∀ r : Fin 16,
    cell0_0 (vertex (21 * 16 + r.val)).val =
      if weight0 (vertex (21 * 16 + r.val)).val = 0 ∧
        neighborCount sample0_0 (vertex (21 * 16 + r.val)) = 140 then 1 else 0 := by
  simp only [neighborCount, adj_iff_fast]
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
private theorem zeroBlock22 : ∀ r : Fin 16,
    cell0_0 (vertex (22 * 16 + r.val)).val =
      if weight0 (vertex (22 * 16 + r.val)).val = 0 ∧
        neighborCount sample0_0 (vertex (22 * 16 + r.val)) = 140 then 1 else 0 := by
  simp only [neighborCount, adj_iff_fast]
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
private theorem zeroBlock23 : ∀ r : Fin 16,
    cell0_0 (vertex (23 * 16 + r.val)).val =
      if weight0 (vertex (23 * 16 + r.val)).val = 0 ∧
        neighborCount sample0_0 (vertex (23 * 16 + r.val)) = 140 then 1 else 0 := by
  simp only [neighborCount, adj_iff_fast]
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
private theorem zeroBlock24 : ∀ r : Fin 16,
    cell0_0 (vertex (24 * 16 + r.val)).val =
      if weight0 (vertex (24 * 16 + r.val)).val = 0 ∧
        neighborCount sample0_0 (vertex (24 * 16 + r.val)) = 140 then 1 else 0 := by
  simp only [neighborCount, adj_iff_fast]
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
private theorem zeroBlock25 : ∀ r : Fin 16,
    cell0_0 (vertex (25 * 16 + r.val)).val =
      if weight0 (vertex (25 * 16 + r.val)).val = 0 ∧
        neighborCount sample0_0 (vertex (25 * 16 + r.val)) = 140 then 1 else 0 := by
  simp only [neighborCount, adj_iff_fast]
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
private theorem zeroBlock26 : ∀ r : Fin 16,
    cell0_0 (vertex (26 * 16 + r.val)).val =
      if weight0 (vertex (26 * 16 + r.val)).val = 0 ∧
        neighborCount sample0_0 (vertex (26 * 16 + r.val)) = 140 then 1 else 0 := by
  simp only [neighborCount, adj_iff_fast]
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
private theorem zeroBlock27 : ∀ r : Fin 16,
    cell0_0 (vertex (27 * 16 + r.val)).val =
      if weight0 (vertex (27 * 16 + r.val)).val = 0 ∧
        neighborCount sample0_0 (vertex (27 * 16 + r.val)) = 140 then 1 else 0 := by
  simp only [neighborCount, adj_iff_fast]
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
private theorem zeroBlock28 : ∀ r : Fin 16,
    cell0_0 (vertex (28 * 16 + r.val)).val =
      if weight0 (vertex (28 * 16 + r.val)).val = 0 ∧
        neighborCount sample0_0 (vertex (28 * 16 + r.val)) = 140 then 1 else 0 := by
  simp only [neighborCount, adj_iff_fast]
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
private theorem zeroBlock29 : ∀ r : Fin 16,
    cell0_0 (vertex (29 * 16 + r.val)).val =
      if weight0 (vertex (29 * 16 + r.val)).val = 0 ∧
        neighborCount sample0_0 (vertex (29 * 16 + r.val)) = 140 then 1 else 0 := by
  simp only [neighborCount, adj_iff_fast]
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
private theorem zeroBlock30 : ∀ r : Fin 16,
    cell0_0 (vertex (30 * 16 + r.val)).val =
      if weight0 (vertex (30 * 16 + r.val)).val = 0 ∧
        neighborCount sample0_0 (vertex (30 * 16 + r.val)) = 140 then 1 else 0 := by
  simp only [neighborCount, adj_iff_fast]
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
private theorem zeroBlock31 : ∀ r : Fin 16,
    cell0_0 (vertex (31 * 16 + r.val)).val =
      if weight0 (vertex (31 * 16 + r.val)).val = 0 ∧
        neighborCount sample0_0 (vertex (31 * 16 + r.val)) = 140 then 1 else 0 := by
  simp only [neighborCount, adj_iff_fast]
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
private theorem zeroBlock32 : ∀ r : Fin 16,
    cell0_0 (vertex (32 * 16 + r.val)).val =
      if weight0 (vertex (32 * 16 + r.val)).val = 0 ∧
        neighborCount sample0_0 (vertex (32 * 16 + r.val)) = 140 then 1 else 0 := by
  simp only [neighborCount, adj_iff_fast]
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
private theorem zeroBlock33 : ∀ r : Fin 16,
    cell0_0 (vertex (33 * 16 + r.val)).val =
      if weight0 (vertex (33 * 16 + r.val)).val = 0 ∧
        neighborCount sample0_0 (vertex (33 * 16 + r.val)) = 140 then 1 else 0 := by
  simp only [neighborCount, adj_iff_fast]
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
private theorem zeroBlock34 : ∀ r : Fin 16,
    cell0_0 (vertex (34 * 16 + r.val)).val =
      if weight0 (vertex (34 * 16 + r.val)).val = 0 ∧
        neighborCount sample0_0 (vertex (34 * 16 + r.val)) = 140 then 1 else 0 := by
  simp only [neighborCount, adj_iff_fast]
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
private theorem zeroBlock35 : ∀ r : Fin 16,
    cell0_0 (vertex (35 * 16 + r.val)).val =
      if weight0 (vertex (35 * 16 + r.val)).val = 0 ∧
        neighborCount sample0_0 (vertex (35 * 16 + r.val)) = 140 then 1 else 0 := by
  simp only [neighborCount, adj_iff_fast]
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
private theorem zeroBlock36 : ∀ r : Fin 16,
    cell0_0 (vertex (36 * 16 + r.val)).val =
      if weight0 (vertex (36 * 16 + r.val)).val = 0 ∧
        neighborCount sample0_0 (vertex (36 * 16 + r.val)) = 140 then 1 else 0 := by
  simp only [neighborCount, adj_iff_fast]
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
private theorem zeroBlock37 : ∀ r : Fin 16,
    cell0_0 (vertex (37 * 16 + r.val)).val =
      if weight0 (vertex (37 * 16 + r.val)).val = 0 ∧
        neighborCount sample0_0 (vertex (37 * 16 + r.val)) = 140 then 1 else 0 := by
  simp only [neighborCount, adj_iff_fast]
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
private theorem zeroBlock38 : ∀ r : Fin 16,
    cell0_0 (vertex (38 * 16 + r.val)).val =
      if weight0 (vertex (38 * 16 + r.val)).val = 0 ∧
        neighborCount sample0_0 (vertex (38 * 16 + r.val)) = 140 then 1 else 0 := by
  simp only [neighborCount, adj_iff_fast]
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
private theorem zeroBlock39 : ∀ r : Fin 16,
    cell0_0 (vertex (39 * 16 + r.val)).val =
      if weight0 (vertex (39 * 16 + r.val)).val = 0 ∧
        neighborCount sample0_0 (vertex (39 * 16 + r.val)) = 140 then 1 else 0 := by
  simp only [neighborCount, adj_iff_fast]
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
private theorem zeroBlock40 : ∀ r : Fin 16,
    cell0_0 (vertex (40 * 16 + r.val)).val =
      if weight0 (vertex (40 * 16 + r.val)).val = 0 ∧
        neighborCount sample0_0 (vertex (40 * 16 + r.val)) = 140 then 1 else 0 := by
  simp only [neighborCount, adj_iff_fast]
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
private theorem zeroBlock41 : ∀ r : Fin 16,
    cell0_0 (vertex (41 * 16 + r.val)).val =
      if weight0 (vertex (41 * 16 + r.val)).val = 0 ∧
        neighborCount sample0_0 (vertex (41 * 16 + r.val)) = 140 then 1 else 0 := by
  simp only [neighborCount, adj_iff_fast]
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
private theorem zeroBlock42 : ∀ r : Fin 16,
    cell0_0 (vertex (42 * 16 + r.val)).val =
      if weight0 (vertex (42 * 16 + r.val)).val = 0 ∧
        neighborCount sample0_0 (vertex (42 * 16 + r.val)) = 140 then 1 else 0 := by
  simp only [neighborCount, adj_iff_fast]
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
private theorem zeroBlock43 : ∀ r : Fin 16,
    cell0_0 (vertex (43 * 16 + r.val)).val =
      if weight0 (vertex (43 * 16 + r.val)).val = 0 ∧
        neighborCount sample0_0 (vertex (43 * 16 + r.val)) = 140 then 1 else 0 := by
  simp only [neighborCount, adj_iff_fast]
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
private theorem zeroBlock44 : ∀ r : Fin 16,
    cell0_0 (vertex (44 * 16 + r.val)).val =
      if weight0 (vertex (44 * 16 + r.val)).val = 0 ∧
        neighborCount sample0_0 (vertex (44 * 16 + r.val)) = 140 then 1 else 0 := by
  simp only [neighborCount, adj_iff_fast]
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
private theorem zeroBlock45 : ∀ r : Fin 16,
    cell0_0 (vertex (45 * 16 + r.val)).val =
      if weight0 (vertex (45 * 16 + r.val)).val = 0 ∧
        neighborCount sample0_0 (vertex (45 * 16 + r.val)) = 140 then 1 else 0 := by
  simp only [neighborCount, adj_iff_fast]
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
private theorem zeroBlock46 : ∀ r : Fin 16,
    cell0_0 (vertex (46 * 16 + r.val)).val =
      if weight0 (vertex (46 * 16 + r.val)).val = 0 ∧
        neighborCount sample0_0 (vertex (46 * 16 + r.val)) = 140 then 1 else 0 := by
  simp only [neighborCount, adj_iff_fast]
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
private theorem zeroBlock47 : ∀ r : Fin 16,
    cell0_0 (vertex (47 * 16 + r.val)).val =
      if weight0 (vertex (47 * 16 + r.val)).val = 0 ∧
        neighborCount sample0_0 (vertex (47 * 16 + r.val)) = 140 then 1 else 0 := by
  simp only [neighborCount, adj_iff_fast]
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
private theorem zeroBlock48 : ∀ r : Fin 16,
    cell0_0 (vertex (48 * 16 + r.val)).val =
      if weight0 (vertex (48 * 16 + r.val)).val = 0 ∧
        neighborCount sample0_0 (vertex (48 * 16 + r.val)) = 140 then 1 else 0 := by
  simp only [neighborCount, adj_iff_fast]
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
private theorem zeroBlock49 : ∀ r : Fin 16,
    cell0_0 (vertex (49 * 16 + r.val)).val =
      if weight0 (vertex (49 * 16 + r.val)).val = 0 ∧
        neighborCount sample0_0 (vertex (49 * 16 + r.val)) = 140 then 1 else 0 := by
  simp only [neighborCount, adj_iff_fast]
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
private theorem zeroBlock50 : ∀ r : Fin 16,
    cell0_0 (vertex (50 * 16 + r.val)).val =
      if weight0 (vertex (50 * 16 + r.val)).val = 0 ∧
        neighborCount sample0_0 (vertex (50 * 16 + r.val)) = 140 then 1 else 0 := by
  simp only [neighborCount, adj_iff_fast]
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
private theorem zeroBlock51 : ∀ r : Fin 16,
    cell0_0 (vertex (51 * 16 + r.val)).val =
      if weight0 (vertex (51 * 16 + r.val)).val = 0 ∧
        neighborCount sample0_0 (vertex (51 * 16 + r.val)) = 140 then 1 else 0 := by
  simp only [neighborCount, adj_iff_fast]
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
private theorem zeroBlock52 : ∀ r : Fin 16,
    cell0_0 (vertex (52 * 16 + r.val)).val =
      if weight0 (vertex (52 * 16 + r.val)).val = 0 ∧
        neighborCount sample0_0 (vertex (52 * 16 + r.val)) = 140 then 1 else 0 := by
  simp only [neighborCount, adj_iff_fast]
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
private theorem zeroBlock53 : ∀ r : Fin 16,
    cell0_0 (vertex (53 * 16 + r.val)).val =
      if weight0 (vertex (53 * 16 + r.val)).val = 0 ∧
        neighborCount sample0_0 (vertex (53 * 16 + r.val)) = 140 then 1 else 0 := by
  simp only [neighborCount, adj_iff_fast]
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
private theorem zeroBlock54 : ∀ r : Fin 16,
    cell0_0 (vertex (54 * 16 + r.val)).val =
      if weight0 (vertex (54 * 16 + r.val)).val = 0 ∧
        neighborCount sample0_0 (vertex (54 * 16 + r.val)) = 140 then 1 else 0 := by
  simp only [neighborCount, adj_iff_fast]
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
private theorem zeroBlock55 : ∀ r : Fin 16,
    cell0_0 (vertex (55 * 16 + r.val)).val =
      if weight0 (vertex (55 * 16 + r.val)).val = 0 ∧
        neighborCount sample0_0 (vertex (55 * 16 + r.val)) = 140 then 1 else 0 := by
  simp only [neighborCount, adj_iff_fast]
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
private theorem zeroBlock56 : ∀ r : Fin 16,
    cell0_0 (vertex (56 * 16 + r.val)).val =
      if weight0 (vertex (56 * 16 + r.val)).val = 0 ∧
        neighborCount sample0_0 (vertex (56 * 16 + r.val)) = 140 then 1 else 0 := by
  simp only [neighborCount, adj_iff_fast]
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
private theorem zeroBlock57 : ∀ r : Fin 16,
    cell0_0 (vertex (57 * 16 + r.val)).val =
      if weight0 (vertex (57 * 16 + r.val)).val = 0 ∧
        neighborCount sample0_0 (vertex (57 * 16 + r.val)) = 140 then 1 else 0 := by
  simp only [neighborCount, adj_iff_fast]
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
private theorem zeroBlock58 : ∀ r : Fin 16,
    cell0_0 (vertex (58 * 16 + r.val)).val =
      if weight0 (vertex (58 * 16 + r.val)).val = 0 ∧
        neighborCount sample0_0 (vertex (58 * 16 + r.val)) = 140 then 1 else 0 := by
  simp only [neighborCount, adj_iff_fast]
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
private theorem zeroBlock59 : ∀ r : Fin 16,
    cell0_0 (vertex (59 * 16 + r.val)).val =
      if weight0 (vertex (59 * 16 + r.val)).val = 0 ∧
        neighborCount sample0_0 (vertex (59 * 16 + r.val)) = 140 then 1 else 0 := by
  simp only [neighborCount, adj_iff_fast]
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
private theorem zeroBlock60 : ∀ r : Fin 16,
    cell0_0 (vertex (60 * 16 + r.val)).val =
      if weight0 (vertex (60 * 16 + r.val)).val = 0 ∧
        neighborCount sample0_0 (vertex (60 * 16 + r.val)) = 140 then 1 else 0 := by
  simp only [neighborCount, adj_iff_fast]
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
private theorem zeroBlock61 : ∀ r : Fin 16,
    cell0_0 (vertex (61 * 16 + r.val)).val =
      if weight0 (vertex (61 * 16 + r.val)).val = 0 ∧
        neighborCount sample0_0 (vertex (61 * 16 + r.val)) = 140 then 1 else 0 := by
  simp only [neighborCount, adj_iff_fast]
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
private theorem zeroBlock62 : ∀ r : Fin 16,
    cell0_0 (vertex (62 * 16 + r.val)).val =
      if weight0 (vertex (62 * 16 + r.val)).val = 0 ∧
        neighborCount sample0_0 (vertex (62 * 16 + r.val)) = 140 then 1 else 0 := by
  simp only [neighborCount, adj_iff_fast]
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
private theorem zeroBlock63 : ∀ r : Fin 16,
    cell0_0 (vertex (63 * 16 + r.val)).val =
      if weight0 (vertex (63 * 16 + r.val)).val = 0 ∧
        neighborCount sample0_0 (vertex (63 * 16 + r.val)) = 140 then 1 else 0 := by
  simp only [neighborCount, adj_iff_fast]
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
private theorem zeroBlock64 : ∀ r : Fin 16,
    cell0_0 (vertex (64 * 16 + r.val)).val =
      if weight0 (vertex (64 * 16 + r.val)).val = 0 ∧
        neighborCount sample0_0 (vertex (64 * 16 + r.val)) = 140 then 1 else 0 := by
  simp only [neighborCount, adj_iff_fast]
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
private theorem zeroBlock65 : ∀ r : Fin 16,
    cell0_0 (vertex (65 * 16 + r.val)).val =
      if weight0 (vertex (65 * 16 + r.val)).val = 0 ∧
        neighborCount sample0_0 (vertex (65 * 16 + r.val)) = 140 then 1 else 0 := by
  simp only [neighborCount, adj_iff_fast]
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
private theorem zeroBlock66 : ∀ r : Fin 16,
    cell0_0 (vertex (66 * 16 + r.val)).val =
      if weight0 (vertex (66 * 16 + r.val)).val = 0 ∧
        neighborCount sample0_0 (vertex (66 * 16 + r.val)) = 140 then 1 else 0 := by
  simp only [neighborCount, adj_iff_fast]
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
private theorem zeroBlock67 : ∀ r : Fin 16,
    cell0_0 (vertex (67 * 16 + r.val)).val =
      if weight0 (vertex (67 * 16 + r.val)).val = 0 ∧
        neighborCount sample0_0 (vertex (67 * 16 + r.val)) = 140 then 1 else 0 := by
  simp only [neighborCount, adj_iff_fast]
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
private theorem zeroBlock68 : ∀ r : Fin 16,
    cell0_0 (vertex (68 * 16 + r.val)).val =
      if weight0 (vertex (68 * 16 + r.val)).val = 0 ∧
        neighborCount sample0_0 (vertex (68 * 16 + r.val)) = 140 then 1 else 0 := by
  simp only [neighborCount, adj_iff_fast]
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
private theorem zeroBlock69 : ∀ r : Fin 16,
    cell0_0 (vertex (69 * 16 + r.val)).val =
      if weight0 (vertex (69 * 16 + r.val)).val = 0 ∧
        neighborCount sample0_0 (vertex (69 * 16 + r.val)) = 140 then 1 else 0 := by
  simp only [neighborCount, adj_iff_fast]
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
private theorem zeroBlock70 : ∀ r : Fin 16,
    cell0_0 (vertex (70 * 16 + r.val)).val =
      if weight0 (vertex (70 * 16 + r.val)).val = 0 ∧
        neighborCount sample0_0 (vertex (70 * 16 + r.val)) = 140 then 1 else 0 := by
  simp only [neighborCount, adj_iff_fast]
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
private theorem zeroBlock71 : ∀ r : Fin 16,
    cell0_0 (vertex (71 * 16 + r.val)).val =
      if weight0 (vertex (71 * 16 + r.val)).val = 0 ∧
        neighborCount sample0_0 (vertex (71 * 16 + r.val)) = 140 then 1 else 0 := by
  simp only [neighborCount, adj_iff_fast]
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
private theorem zeroBlock72 : ∀ r : Fin 16,
    cell0_0 (vertex (72 * 16 + r.val)).val =
      if weight0 (vertex (72 * 16 + r.val)).val = 0 ∧
        neighborCount sample0_0 (vertex (72 * 16 + r.val)) = 140 then 1 else 0 := by
  simp only [neighborCount, adj_iff_fast]
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
private theorem zeroBlock73 : ∀ r : Fin 16,
    cell0_0 (vertex (73 * 16 + r.val)).val =
      if weight0 (vertex (73 * 16 + r.val)).val = 0 ∧
        neighborCount sample0_0 (vertex (73 * 16 + r.val)) = 140 then 1 else 0 := by
  simp only [neighborCount, adj_iff_fast]
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
private theorem zeroBlock74 : ∀ r : Fin 16,
    cell0_0 (vertex (74 * 16 + r.val)).val =
      if weight0 (vertex (74 * 16 + r.val)).val = 0 ∧
        neighborCount sample0_0 (vertex (74 * 16 + r.val)) = 140 then 1 else 0 := by
  simp only [neighborCount, adj_iff_fast]
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
private theorem zeroBlock75 : ∀ r : Fin 16,
    cell0_0 (vertex (75 * 16 + r.val)).val =
      if weight0 (vertex (75 * 16 + r.val)).val = 0 ∧
        neighborCount sample0_0 (vertex (75 * 16 + r.val)) = 140 then 1 else 0 := by
  simp only [neighborCount, adj_iff_fast]
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
private theorem zeroBlock76 : ∀ r : Fin 16,
    cell0_0 (vertex (76 * 16 + r.val)).val =
      if weight0 (vertex (76 * 16 + r.val)).val = 0 ∧
        neighborCount sample0_0 (vertex (76 * 16 + r.val)) = 140 then 1 else 0 := by
  simp only [neighborCount, adj_iff_fast]
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
private theorem zeroBlock77 : ∀ r : Fin 16,
    cell0_0 (vertex (77 * 16 + r.val)).val =
      if weight0 (vertex (77 * 16 + r.val)).val = 0 ∧
        neighborCount sample0_0 (vertex (77 * 16 + r.val)) = 140 then 1 else 0 := by
  simp only [neighborCount, adj_iff_fast]
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
private theorem zeroBlock78 : ∀ r : Fin 16,
    cell0_0 (vertex (78 * 16 + r.val)).val =
      if weight0 (vertex (78 * 16 + r.val)).val = 0 ∧
        neighborCount sample0_0 (vertex (78 * 16 + r.val)) = 140 then 1 else 0 := by
  simp only [neighborCount, adj_iff_fast]
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
private theorem zeroBlock79 : ∀ r : Fin 16,
    cell0_0 (vertex (79 * 16 + r.val)).val =
      if weight0 (vertex (79 * 16 + r.val)).val = 0 ∧
        neighborCount sample0_0 (vertex (79 * 16 + r.val)) = 140 then 1 else 0 := by
  simp only [neighborCount, adj_iff_fast]
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
private theorem zeroBlock80 : ∀ r : Fin 16,
    cell0_0 (vertex (80 * 16 + r.val)).val =
      if weight0 (vertex (80 * 16 + r.val)).val = 0 ∧
        neighborCount sample0_0 (vertex (80 * 16 + r.val)) = 140 then 1 else 0 := by
  simp only [neighborCount, adj_iff_fast]
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
private theorem zeroBlock81 : ∀ r : Fin 16,
    cell0_0 (vertex (81 * 16 + r.val)).val =
      if weight0 (vertex (81 * 16 + r.val)).val = 0 ∧
        neighborCount sample0_0 (vertex (81 * 16 + r.val)) = 140 then 1 else 0 := by
  simp only [neighborCount, adj_iff_fast]
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
private theorem zeroBlock82 : ∀ r : Fin 16,
    cell0_0 (vertex (82 * 16 + r.val)).val =
      if weight0 (vertex (82 * 16 + r.val)).val = 0 ∧
        neighborCount sample0_0 (vertex (82 * 16 + r.val)) = 140 then 1 else 0 := by
  simp only [neighborCount, adj_iff_fast]
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
private theorem zeroBlock83 : ∀ r : Fin 16,
    cell0_0 (vertex (83 * 16 + r.val)).val =
      if weight0 (vertex (83 * 16 + r.val)).val = 0 ∧
        neighborCount sample0_0 (vertex (83 * 16 + r.val)) = 140 then 1 else 0 := by
  simp only [neighborCount, adj_iff_fast]
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
private theorem zeroBlock84 : ∀ r : Fin 16,
    cell0_0 (vertex (84 * 16 + r.val)).val =
      if weight0 (vertex (84 * 16 + r.val)).val = 0 ∧
        neighborCount sample0_0 (vertex (84 * 16 + r.val)) = 140 then 1 else 0 := by
  simp only [neighborCount, adj_iff_fast]
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
private theorem zeroBlock85 : ∀ r : Fin 16,
    cell0_0 (vertex (85 * 16 + r.val)).val =
      if weight0 (vertex (85 * 16 + r.val)).val = 0 ∧
        neighborCount sample0_0 (vertex (85 * 16 + r.val)) = 140 then 1 else 0 := by
  simp only [neighborCount, adj_iff_fast]
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
private theorem zeroBlock86 : ∀ r : Fin 16,
    cell0_0 (vertex (86 * 16 + r.val)).val =
      if weight0 (vertex (86 * 16 + r.val)).val = 0 ∧
        neighborCount sample0_0 (vertex (86 * 16 + r.val)) = 140 then 1 else 0 := by
  simp only [neighborCount, adj_iff_fast]
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
private theorem zeroBlock87 : ∀ r : Fin 16,
    cell0_0 (vertex (87 * 16 + r.val)).val =
      if weight0 (vertex (87 * 16 + r.val)).val = 0 ∧
        neighborCount sample0_0 (vertex (87 * 16 + r.val)) = 140 then 1 else 0 := by
  simp only [neighborCount, adj_iff_fast]
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
private theorem zeroBlock88 : ∀ r : Fin 16,
    cell0_0 (vertex (88 * 16 + r.val)).val =
      if weight0 (vertex (88 * 16 + r.val)).val = 0 ∧
        neighborCount sample0_0 (vertex (88 * 16 + r.val)) = 140 then 1 else 0 := by
  simp only [neighborCount, adj_iff_fast]
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
private theorem zeroBlock89 : ∀ r : Fin 16,
    cell0_0 (vertex (89 * 16 + r.val)).val =
      if weight0 (vertex (89 * 16 + r.val)).val = 0 ∧
        neighborCount sample0_0 (vertex (89 * 16 + r.val)) = 140 then 1 else 0 := by
  simp only [neighborCount, adj_iff_fast]
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
private theorem zeroBlock90 : ∀ r : Fin 16,
    cell0_0 (vertex (90 * 16 + r.val)).val =
      if weight0 (vertex (90 * 16 + r.val)).val = 0 ∧
        neighborCount sample0_0 (vertex (90 * 16 + r.val)) = 140 then 1 else 0 := by
  simp only [neighborCount, adj_iff_fast]
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
private theorem zeroBlock91 : ∀ r : Fin 16,
    cell0_0 (vertex (91 * 16 + r.val)).val =
      if weight0 (vertex (91 * 16 + r.val)).val = 0 ∧
        neighborCount sample0_0 (vertex (91 * 16 + r.val)) = 140 then 1 else 0 := by
  simp only [neighborCount, adj_iff_fast]
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
private theorem zeroBlock92 : ∀ r : Fin 16,
    cell0_0 (vertex (92 * 16 + r.val)).val =
      if weight0 (vertex (92 * 16 + r.val)).val = 0 ∧
        neighborCount sample0_0 (vertex (92 * 16 + r.val)) = 140 then 1 else 0 := by
  simp only [neighborCount, adj_iff_fast]
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
private theorem zeroBlock93 : ∀ r : Fin 16,
    cell0_0 (vertex (93 * 16 + r.val)).val =
      if weight0 (vertex (93 * 16 + r.val)).val = 0 ∧
        neighborCount sample0_0 (vertex (93 * 16 + r.val)) = 140 then 1 else 0 := by
  simp only [neighborCount, adj_iff_fast]
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
private theorem zeroBlock94 : ∀ r : Fin 16,
    cell0_0 (vertex (94 * 16 + r.val)).val =
      if weight0 (vertex (94 * 16 + r.val)).val = 0 ∧
        neighborCount sample0_0 (vertex (94 * 16 + r.val)) = 140 then 1 else 0 := by
  simp only [neighborCount, adj_iff_fast]
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
private theorem zeroBlock95 : ∀ r : Fin 16,
    cell0_0 (vertex (95 * 16 + r.val)).val =
      if weight0 (vertex (95 * 16 + r.val)).val = 0 ∧
        neighborCount sample0_0 (vertex (95 * 16 + r.val)) = 140 then 1 else 0 := by
  simp only [neighborCount, adj_iff_fast]
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
private theorem zeroBlock96 : ∀ r : Fin 16,
    cell0_0 (vertex (96 * 16 + r.val)).val =
      if weight0 (vertex (96 * 16 + r.val)).val = 0 ∧
        neighborCount sample0_0 (vertex (96 * 16 + r.val)) = 140 then 1 else 0 := by
  simp only [neighborCount, adj_iff_fast]
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
private theorem zeroBlock97 : ∀ r : Fin 16,
    cell0_0 (vertex (97 * 16 + r.val)).val =
      if weight0 (vertex (97 * 16 + r.val)).val = 0 ∧
        neighborCount sample0_0 (vertex (97 * 16 + r.val)) = 140 then 1 else 0 := by
  simp only [neighborCount, adj_iff_fast]
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
private theorem zeroBlock98 : ∀ r : Fin 16,
    cell0_0 (vertex (98 * 16 + r.val)).val =
      if weight0 (vertex (98 * 16 + r.val)).val = 0 ∧
        neighborCount sample0_0 (vertex (98 * 16 + r.val)) = 140 then 1 else 0 := by
  simp only [neighborCount, adj_iff_fast]
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
private theorem zeroBlock99 : ∀ r : Fin 16,
    cell0_0 (vertex (99 * 16 + r.val)).val =
      if weight0 (vertex (99 * 16 + r.val)).val = 0 ∧
        neighborCount sample0_0 (vertex (99 * 16 + r.val)) = 140 then 1 else 0 := by
  simp only [neighborCount, adj_iff_fast]
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
private theorem zeroBlock100 : ∀ r : Fin 16,
    cell0_0 (vertex (100 * 16 + r.val)).val =
      if weight0 (vertex (100 * 16 + r.val)).val = 0 ∧
        neighborCount sample0_0 (vertex (100 * 16 + r.val)) = 140 then 1 else 0 := by
  simp only [neighborCount, adj_iff_fast]
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
private theorem zeroBlock101 : ∀ r : Fin 16,
    cell0_0 (vertex (101 * 16 + r.val)).val =
      if weight0 (vertex (101 * 16 + r.val)).val = 0 ∧
        neighborCount sample0_0 (vertex (101 * 16 + r.val)) = 140 then 1 else 0 := by
  simp only [neighborCount, adj_iff_fast]
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
private theorem zeroBlock102 : ∀ r : Fin 16,
    cell0_0 (vertex (102 * 16 + r.val)).val =
      if weight0 (vertex (102 * 16 + r.val)).val = 0 ∧
        neighborCount sample0_0 (vertex (102 * 16 + r.val)) = 140 then 1 else 0 := by
  simp only [neighborCount, adj_iff_fast]
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
private theorem zeroBlock103 : ∀ r : Fin 16,
    cell0_0 (vertex (103 * 16 + r.val)).val =
      if weight0 (vertex (103 * 16 + r.val)).val = 0 ∧
        neighborCount sample0_0 (vertex (103 * 16 + r.val)) = 140 then 1 else 0 := by
  simp only [neighborCount, adj_iff_fast]
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
private theorem zeroBlock104 : ∀ r : Fin 16,
    cell0_0 (vertex (104 * 16 + r.val)).val =
      if weight0 (vertex (104 * 16 + r.val)).val = 0 ∧
        neighborCount sample0_0 (vertex (104 * 16 + r.val)) = 140 then 1 else 0 := by
  simp only [neighborCount, adj_iff_fast]
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
private theorem zeroBlock105 : ∀ r : Fin 16,
    cell0_0 (vertex (105 * 16 + r.val)).val =
      if weight0 (vertex (105 * 16 + r.val)).val = 0 ∧
        neighborCount sample0_0 (vertex (105 * 16 + r.val)) = 140 then 1 else 0 := by
  simp only [neighborCount, adj_iff_fast]
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
private theorem zeroBlock106 : ∀ r : Fin 16,
    cell0_0 (vertex (106 * 16 + r.val)).val =
      if weight0 (vertex (106 * 16 + r.val)).val = 0 ∧
        neighborCount sample0_0 (vertex (106 * 16 + r.val)) = 140 then 1 else 0 := by
  simp only [neighborCount, adj_iff_fast]
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
private theorem zeroBlock107 : ∀ r : Fin 16,
    cell0_0 (vertex (107 * 16 + r.val)).val =
      if weight0 (vertex (107 * 16 + r.val)).val = 0 ∧
        neighborCount sample0_0 (vertex (107 * 16 + r.val)) = 140 then 1 else 0 := by
  simp only [neighborCount, adj_iff_fast]
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
private theorem zeroBlock108 : ∀ r : Fin 16,
    cell0_0 (vertex (108 * 16 + r.val)).val =
      if weight0 (vertex (108 * 16 + r.val)).val = 0 ∧
        neighborCount sample0_0 (vertex (108 * 16 + r.val)) = 140 then 1 else 0 := by
  simp only [neighborCount, adj_iff_fast]
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
private theorem zeroBlock109 : ∀ r : Fin 16,
    cell0_0 (vertex (109 * 16 + r.val)).val =
      if weight0 (vertex (109 * 16 + r.val)).val = 0 ∧
        neighborCount sample0_0 (vertex (109 * 16 + r.val)) = 140 then 1 else 0 := by
  simp only [neighborCount, adj_iff_fast]
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
private theorem zeroBlock110 : ∀ r : Fin 16,
    cell0_0 (vertex (110 * 16 + r.val)).val =
      if weight0 (vertex (110 * 16 + r.val)).val = 0 ∧
        neighborCount sample0_0 (vertex (110 * 16 + r.val)) = 140 then 1 else 0 := by
  simp only [neighborCount, adj_iff_fast]
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
private theorem zeroBlock111 : ∀ r : Fin 16,
    cell0_0 (vertex (111 * 16 + r.val)).val =
      if weight0 (vertex (111 * 16 + r.val)).val = 0 ∧
        neighborCount sample0_0 (vertex (111 * 16 + r.val)) = 140 then 1 else 0 := by
  simp only [neighborCount, adj_iff_fast]
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
private theorem zeroBlock112 : ∀ r : Fin 16,
    cell0_0 (vertex (112 * 16 + r.val)).val =
      if weight0 (vertex (112 * 16 + r.val)).val = 0 ∧
        neighborCount sample0_0 (vertex (112 * 16 + r.val)) = 140 then 1 else 0 := by
  simp only [neighborCount, adj_iff_fast]
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
private theorem zeroBlock113 : ∀ r : Fin 16,
    cell0_0 (vertex (113 * 16 + r.val)).val =
      if weight0 (vertex (113 * 16 + r.val)).val = 0 ∧
        neighborCount sample0_0 (vertex (113 * 16 + r.val)) = 140 then 1 else 0 := by
  simp only [neighborCount, adj_iff_fast]
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
private theorem zeroBlock114 : ∀ r : Fin 16,
    cell0_0 (vertex (114 * 16 + r.val)).val =
      if weight0 (vertex (114 * 16 + r.val)).val = 0 ∧
        neighborCount sample0_0 (vertex (114 * 16 + r.val)) = 140 then 1 else 0 := by
  simp only [neighborCount, adj_iff_fast]
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
private theorem zeroBlock115 : ∀ r : Fin 16,
    cell0_0 (vertex (115 * 16 + r.val)).val =
      if weight0 (vertex (115 * 16 + r.val)).val = 0 ∧
        neighborCount sample0_0 (vertex (115 * 16 + r.val)) = 140 then 1 else 0 := by
  simp only [neighborCount, adj_iff_fast]
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
private theorem zeroBlock116 : ∀ r : Fin 16,
    cell0_0 (vertex (116 * 16 + r.val)).val =
      if weight0 (vertex (116 * 16 + r.val)).val = 0 ∧
        neighborCount sample0_0 (vertex (116 * 16 + r.val)) = 140 then 1 else 0 := by
  simp only [neighborCount, adj_iff_fast]
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
private theorem zeroBlock117 : ∀ r : Fin 16,
    cell0_0 (vertex (117 * 16 + r.val)).val =
      if weight0 (vertex (117 * 16 + r.val)).val = 0 ∧
        neighborCount sample0_0 (vertex (117 * 16 + r.val)) = 140 then 1 else 0 := by
  simp only [neighborCount, adj_iff_fast]
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
private theorem zeroBlock118 : ∀ r : Fin 16,
    cell0_0 (vertex (118 * 16 + r.val)).val =
      if weight0 (vertex (118 * 16 + r.val)).val = 0 ∧
        neighborCount sample0_0 (vertex (118 * 16 + r.val)) = 140 then 1 else 0 := by
  simp only [neighborCount, adj_iff_fast]
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
private theorem zeroBlock119 : ∀ r : Fin 16,
    cell0_0 (vertex (119 * 16 + r.val)).val =
      if weight0 (vertex (119 * 16 + r.val)).val = 0 ∧
        neighborCount sample0_0 (vertex (119 * 16 + r.val)) = 140 then 1 else 0 := by
  simp only [neighborCount, adj_iff_fast]
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
private theorem zeroBlock120 : ∀ r : Fin 16,
    cell0_0 (vertex (120 * 16 + r.val)).val =
      if weight0 (vertex (120 * 16 + r.val)).val = 0 ∧
        neighborCount sample0_0 (vertex (120 * 16 + r.val)) = 140 then 1 else 0 := by
  simp only [neighborCount, adj_iff_fast]
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
private theorem zeroBlock121 : ∀ r : Fin 16,
    cell0_0 (vertex (121 * 16 + r.val)).val =
      if weight0 (vertex (121 * 16 + r.val)).val = 0 ∧
        neighborCount sample0_0 (vertex (121 * 16 + r.val)) = 140 then 1 else 0 := by
  simp only [neighborCount, adj_iff_fast]
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
private theorem zeroBlock122 : ∀ r : Fin 16,
    cell0_0 (vertex (122 * 16 + r.val)).val =
      if weight0 (vertex (122 * 16 + r.val)).val = 0 ∧
        neighborCount sample0_0 (vertex (122 * 16 + r.val)) = 140 then 1 else 0 := by
  simp only [neighborCount, adj_iff_fast]
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
private theorem zeroBlock123 : ∀ r : Fin 16,
    cell0_0 (vertex (123 * 16 + r.val)).val =
      if weight0 (vertex (123 * 16 + r.val)).val = 0 ∧
        neighborCount sample0_0 (vertex (123 * 16 + r.val)) = 140 then 1 else 0 := by
  simp only [neighborCount, adj_iff_fast]
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
private theorem zeroBlock124 : ∀ r : Fin 16,
    cell0_0 (vertex (124 * 16 + r.val)).val =
      if weight0 (vertex (124 * 16 + r.val)).val = 0 ∧
        neighborCount sample0_0 (vertex (124 * 16 + r.val)) = 140 then 1 else 0 := by
  simp only [neighborCount, adj_iff_fast]
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
private theorem zeroBlock125 : ∀ r : Fin 16,
    cell0_0 (vertex (125 * 16 + r.val)).val =
      if weight0 (vertex (125 * 16 + r.val)).val = 0 ∧
        neighborCount sample0_0 (vertex (125 * 16 + r.val)) = 140 then 1 else 0 := by
  simp only [neighborCount, adj_iff_fast]
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
private theorem zeroBlock126 : ∀ r : Fin 16,
    cell0_0 (vertex (126 * 16 + r.val)).val =
      if weight0 (vertex (126 * 16 + r.val)).val = 0 ∧
        neighborCount sample0_0 (vertex (126 * 16 + r.val)) = 140 then 1 else 0 := by
  simp only [neighborCount, adj_iff_fast]
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
private theorem zeroBlock127 : ∀ r : Fin 16,
    cell0_0 (vertex (127 * 16 + r.val)).val =
      if weight0 (vertex (127 * 16 + r.val)).val = 0 ∧
        neighborCount sample0_0 (vertex (127 * 16 + r.val)) = 140 then 1 else 0 := by
  simp only [neighborCount, adj_iff_fast]
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
private theorem zeroBlock128 : ∀ r : Fin 16,
    cell0_0 (vertex (128 * 16 + r.val)).val =
      if weight0 (vertex (128 * 16 + r.val)).val = 0 ∧
        neighborCount sample0_0 (vertex (128 * 16 + r.val)) = 140 then 1 else 0 := by
  simp only [neighborCount, adj_iff_fast]
  decide +kernel

private theorem allBlocks (P : Fin 2058 → Prop)
    (h : ∀ q : Fin 129, ∀ r : Fin 16, P (vertex (q.val * 16 + r.val))) : ∀ x, P x := by
  intro x
  have hx := h ⟨x.val / 16, by omega⟩ ⟨x.val % 16, Nat.mod_lt _ (by decide)⟩
  have he : x.val / 16 * 16 + x.val % 16 = x.val := by omega
  simpa only [he, vertex, Nat.mod_eq_of_lt x.isLt] using hx

public theorem zero_check : ∀ x : Fin 2058,
    cell0_0 x.val = if weight0 x.val = 0 ∧
      neighborCount sample0_0 x = 140 then 1 else 0 := by
  apply allBlocks
  intro q
  fin_cases q
  · exact zeroBlock0
  · exact zeroBlock1
  · exact zeroBlock2
  · exact zeroBlock3
  · exact zeroBlock4
  · exact zeroBlock5
  · exact zeroBlock6
  · exact zeroBlock7
  · exact zeroBlock8
  · exact zeroBlock9
  · exact zeroBlock10
  · exact zeroBlock11
  · exact zeroBlock12
  · exact zeroBlock13
  · exact zeroBlock14
  · exact zeroBlock15
  · exact zeroBlock16
  · exact zeroBlock17
  · exact zeroBlock18
  · exact zeroBlock19
  · exact zeroBlock20
  · exact zeroBlock21
  · exact zeroBlock22
  · exact zeroBlock23
  · exact zeroBlock24
  · exact zeroBlock25
  · exact zeroBlock26
  · exact zeroBlock27
  · exact zeroBlock28
  · exact zeroBlock29
  · exact zeroBlock30
  · exact zeroBlock31
  · exact zeroBlock32
  · exact zeroBlock33
  · exact zeroBlock34
  · exact zeroBlock35
  · exact zeroBlock36
  · exact zeroBlock37
  · exact zeroBlock38
  · exact zeroBlock39
  · exact zeroBlock40
  · exact zeroBlock41
  · exact zeroBlock42
  · exact zeroBlock43
  · exact zeroBlock44
  · exact zeroBlock45
  · exact zeroBlock46
  · exact zeroBlock47
  · exact zeroBlock48
  · exact zeroBlock49
  · exact zeroBlock50
  · exact zeroBlock51
  · exact zeroBlock52
  · exact zeroBlock53
  · exact zeroBlock54
  · exact zeroBlock55
  · exact zeroBlock56
  · exact zeroBlock57
  · exact zeroBlock58
  · exact zeroBlock59
  · exact zeroBlock60
  · exact zeroBlock61
  · exact zeroBlock62
  · exact zeroBlock63
  · exact zeroBlock64
  · exact zeroBlock65
  · exact zeroBlock66
  · exact zeroBlock67
  · exact zeroBlock68
  · exact zeroBlock69
  · exact zeroBlock70
  · exact zeroBlock71
  · exact zeroBlock72
  · exact zeroBlock73
  · exact zeroBlock74
  · exact zeroBlock75
  · exact zeroBlock76
  · exact zeroBlock77
  · exact zeroBlock78
  · exact zeroBlock79
  · exact zeroBlock80
  · exact zeroBlock81
  · exact zeroBlock82
  · exact zeroBlock83
  · exact zeroBlock84
  · exact zeroBlock85
  · exact zeroBlock86
  · exact zeroBlock87
  · exact zeroBlock88
  · exact zeroBlock89
  · exact zeroBlock90
  · exact zeroBlock91
  · exact zeroBlock92
  · exact zeroBlock93
  · exact zeroBlock94
  · exact zeroBlock95
  · exact zeroBlock96
  · exact zeroBlock97
  · exact zeroBlock98
  · exact zeroBlock99
  · exact zeroBlock100
  · exact zeroBlock101
  · exact zeroBlock102
  · exact zeroBlock103
  · exact zeroBlock104
  · exact zeroBlock105
  · exact zeroBlock106
  · exact zeroBlock107
  · exact zeroBlock108
  · exact zeroBlock109
  · exact zeroBlock110
  · exact zeroBlock111
  · exact zeroBlock112
  · exact zeroBlock113
  · exact zeroBlock114
  · exact zeroBlock115
  · exact zeroBlock116
  · exact zeroBlock117
  · exact zeroBlock118
  · exact zeroBlock119
  · exact zeroBlock120
  · exact zeroBlock121
  · exact zeroBlock122
  · exact zeroBlock123
  · exact zeroBlock124
  · exact zeroBlock125
  · exact zeroBlock126
  · exact zeroBlock127
  · exact zeroBlock128

end Held.OuterInvolution.FixedStructure.FixedOrderBound
