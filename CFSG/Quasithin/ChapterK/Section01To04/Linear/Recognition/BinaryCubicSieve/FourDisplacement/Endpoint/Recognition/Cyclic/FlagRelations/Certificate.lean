module

public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Recognition.BinaryCubicSieve.FourDisplacement.Endpoint.Recognition.Cyclic.Spanning

/-!
# Additive generation of the binary incident flags

The table starts with the fifteen flags from `Spanning`, then lists ninety more
flags. For each new flag, `parents` records two earlier flags whose elementary
addition gives it. The kernel checks incidence, the initial fifteen flags,
strict descent of the parent indices, every additive triple, and exhaustion of
all incident point–covector pairs. Strong induction then gives an elimination
principle for the actual `Flag` type.

The vector codes are the four binary digits, starting with the coefficient of
e₀. The tables can be obtained by repeatedly adjoining coordinate sums of pairs
already listed. Their generation is not part of the trusted proof: all table
properties used below are proved by kernel reduction.

Source: Aschbacher–Smith, K.3.2, printed pp.451,454–455;
Guralnick–Malle, Classification of 2F-modules II, author manuscript,
Lemma 4.5 step 2 and Proposition 4.8 step 3A.
-/

set_option backward.isDefEq.respectTransparency false
public noncomputable section
namespace CFSG.Quasithin.ChapterK.Linear.Recognition.BinaryCubicSieve.FourDisplacement.Endpoint.Cyclic

private def vector : Fin 16 → Natural :=
  ![![0, 0, 0, 0], ![1, 0, 0, 0], ![0, 1, 0, 0], ![1, 1, 0, 0], ![0, 0, 1, 0], ![1, 0, 1, 0], ![0,
    1, 1, 0], ![1, 1, 1, 0], ![0, 0, 0, 1], ![1, 0, 0, 1], ![0, 1, 0, 1], ![1, 1, 0, 1], ![0, 0,
    1, 1], ![1, 0, 1, 1], ![0, 1, 1, 1], ![1, 1, 1, 1]]
private def pairs : Fin 105 → Fin 16 × Fin 16 :=
  ![(1, 2), (1, 4), (1, 8), (2, 1), (2, 4), (2, 8), (4, 1), (4, 2), (4, 8), (8, 1), (8, 2), (8,
    4), (9, 9), (10, 10), (12, 12), (1, 6), (1, 10), (5, 2), (9, 2), (1, 12), (3, 4), (9, 4), (3,
    8), (5, 8), (2, 5), (2, 9), (6, 1), (10, 1), (2, 12), (10, 4), (6, 8), (4, 3), (4, 9), (12,
    1), (4, 10), (12, 2), (8, 3), (8, 5), (8, 6), (1, 14), (13, 2), (11, 4), (7, 8), (2, 13), (14,
    1), (4, 11), (8, 7), (9, 11), (9, 13), (11, 9), (13, 9), (11, 10), (10, 11), (10, 14), (14,
    10), (13, 12), (14, 12), (12, 13), (12, 14), (9, 6), (5, 10), (3, 12), (10, 5), (6, 9), (12,
    3), (9, 15), (15, 9), (15, 10), (10, 15), (15, 12), (12, 15), (11, 14), (13, 14), (13, 11),
    (11, 13), (14, 13), (14, 11), (3, 11), (5, 13), (11, 3), (13, 5), (6, 14), (14, 6), (15, 6),
    (5, 15), (3, 15), (3, 3), (5, 5), (15, 5), (6, 15), (6, 6), (15, 3), (7, 14), (13, 7), (11,
    7), (7, 13), (14, 7), (7, 11), (7, 6), (5, 7), (3, 7), (7, 5), (6, 7), (7, 3), (15, 15)]
private def parents : Fin 90 → Fin 105 × Fin 105 :=
  ![(0, 1), (0, 2), (0, 7), (0, 10), (1, 2), (1, 4), (1, 11), (2, 5), (2, 8), (3, 4), (3, 5), (3,
    6), (3, 9), (4, 5), (4, 11), (5, 8), (6, 7), (6, 8), (6, 9), (7, 8), (7, 10), (9, 10), (9,
    11), (10, 11), (0, 19), (0, 35), (1, 29), (2, 30), (3, 28), (3, 33), (6, 34), (9, 38), (12,
    18), (12, 21), (12, 25), (12, 32), (13, 16), (13, 27), (13, 29), (13, 34), (14, 19), (14, 28),
    (14, 33), (14, 35), (15, 38), (16, 34), (19, 28), (24, 37), (25, 32), (31, 36), (12, 59), (12,
    63), (13, 60), (13, 62), (14, 61), (14, 64), (39, 53), (39, 58), (40, 50), (41, 49), (43, 57),
    (44, 54), (47, 52), (48, 57), (49, 51), (50, 55), (53, 58), (54, 56), (15, 82), (17, 78), (20,
    77), (22, 77), (23, 78), (24, 80), (26, 81), (30, 81), (31, 79), (39, 81), (40, 80), (41, 79),
    (43, 78), (44, 82), (45, 77), (59, 82), (60, 78), (61, 77), (62, 80), (63, 81), (64, 79), (65,
    89)]
private theorem incident : ∀ i : Fin 105, let p := pairs i
    vector p.1 ≠ 0 ∧ vector p.2 ≠ 0 ∧ dotProduct (vector p.2) (vector p.1) = 0 := by
  decide +kernel
private def listedFlag (i : Fin 105) : Flag :=
  ⟨(vector (pairs i).1, vector (pairs i).2), incident i⟩
private theorem initial : ∀ i : Fin 15,
    listedFlag ⟨i.val, by omega⟩ = spanningFlag i := by
  decide +kernel
private theorem parents_lt : ∀ i : Fin 90,
    (parents i).1.val < 15 + i.val ∧ (parents i).2.val < 15 + i.val := by
  decide +kernel
private theorem parents_triple : ∀ i : Fin 90,
    AdditiveTriple (listedFlag (parents i).1) (listedFlag (parents i).2)
      (listedFlag ⟨15 + i.val, by omega⟩) := by
  unfold AdditiveTriple
  decide +kernel
private theorem vector_surjective : Function.Surjective vector := by
  decide +kernel
private theorem pairs_complete : ∀ x y : Fin 16,
    vector x ≠ 0 → vector y ≠ 0 → dotProduct (vector y) (vector x) = 0 →
      ∃ i : Fin 105, pairs i = (x, y) := by
  decide +kernel
private theorem listedFlag_surjective : Function.Surjective listedFlag := by
  intro a
  obtain ⟨x, hx⟩ := vector_surjective (point a)
  obtain ⟨y, hy⟩ := vector_surjective (covector a)
  obtain ⟨i, hi⟩ := pairs_complete x y
    (by simpa only [hx, point] using a.property.1)
    (by simpa only [hy, covector] using a.property.2.1)
    (by simpa only [hx, hy, point, covector] using a.property.2.2)
  refine ⟨i, ?_⟩
  apply Flag.ext
  · change vector (pairs i).1 = point a
    simpa only [hi] using hx
  · change vector (pairs i).2 = covector a
    simpa only [hi] using hy

/-- Closure under the elementary triples, starting at the fifteen selected flags,
exhausts the incident geometry. -/
theorem flag_additive_induction (P : Flag → Prop)
    (hb : ∀ i, P (spanningFlag i))
    (ha : ∀ a b c, AdditiveTriple a b c → P a → P b → P c) : ∀ a, P a := by
  have hall (n : ℕ) : ∀ hn : n < 105, P (listedFlag ⟨n, hn⟩) := by
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro hn
      by_cases hsmall : n < 15
      · simpa only [initial ⟨n, hsmall⟩] using hb ⟨n, hsmall⟩
      · let j : Fin 90 := ⟨n - 15, by omega⟩
        have he : 15 + j.val = n := by dsimp [j]; omega
        have hl := parents_lt j
        have hp := ha _ _ _ (parents_triple j)
          (ih _ (by omega) (parents j).1.isLt)
          (ih _ (by omega) (parents j).2.isLt)
        have hi : (⟨15 + j.val, by omega⟩ : Fin 105) = ⟨n, hn⟩ := Fin.ext he
        rwa [hi] at hp
  intro a
  obtain ⟨i, rfl⟩ := listedFlag_surjective a
  exact hall i.val i.isLt


end CFSG.Quasithin.ChapterK.Linear.Recognition.BinaryCubicSieve.FourDisplacement.Endpoint.Cyclic
