module

public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.RadicalOrders.FixedCoordinates.Blocks
public import Theory.SpecificGroups.ReeF4.ExceptionalEndomorphism.WordRelations.Intertwining.Transport.WeylDuality

/-!
# A concrete partition of the three Ree root supports

The 24 positive F₄ roots are listed in four orthogonal long-short pairs,
followed by four B₂ quartets ordered as `r, s, r+s, r+2s`. Positivity is
checked by the height functional, and exhaustiveness by the signed-pair,
unit and half-sign descriptions of the actual Euclidean root set. The
Suzuki radical removes the first quartet; the linear radical removes the
first pair, as verified from their Levi-node coefficient conditions.

The root-coroot pairing identity for `exceptionalRootPermutation` and its
simple-root reversal determine each dual root. All lengths, inner products
and root sums are checked in Euclidean coordinates. This constructs the
geometric `RootBlocks` input without any matrix-relation or counting premise.

`rootBlocks_roots_val` and `RootPartition.table_simpleCoefficient` specify
the layout for consumers that need the individual root words.

Source: the root calculation underlying Aschbacher–Smith F.1.12(I)(5),
printed p.263 (PDF p.274) of `refs/quasithin.pdf`. This partition is a
prerequisite for the radical-order calculation, not that order theorem.
-/

noncomputable section
namespace ReeF4.Parabolics.RadicalCoordinates.FixedCoordinates

namespace RootPartition
open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem

def degree (x : Vec 4) : ℝ := 8 * x 0 + 3 * x 1 + 2 * x 2 + x 3

lemma degree_simple (i : Fin 4) : degree (typeF4SimpleRoot i) = 1 := by
  fin_cases i <;> norm_num [degree, typeF4SimpleRoot, Matrix.cons_val_two, Matrix.cons_val_three]

lemma degree_pos {r : typeF4Roots} (hr : typeF4RootPairing_base.IsPos r) :
    0 < degree r.val := by
  have hs (i : typeF4Roots) (hi : i ∈ typeF4RootPairing_base.support) :
      degree i.val = 1 := by
    obtain ⟨j, hj⟩ := typeF4RootPairing_baseEquiv.surjective ⟨i, hi⟩
    have he : typeF4SimpleRootIndex j = i := congrArg Subtype.val hj
    rw [← he, typeF4SimpleRootIndex_val, degree_simple]
  apply hr.induction_on_add
  · intro i hi
    rw [hs i hi]
    norm_num
  · intro i j k hk hi hj
    change k.val = i.val + j.val at hk
    have hd : degree k.val = degree i.val + degree j.val := by rw [hk]; simp [degree]; ring
    rw [hd, hs j hj]
    linarith

lemma positive_iff (r : typeF4Roots) :
    typeF4RootPairing_base.IsPos r ↔ 0 < degree r.val := by
  classical
  refine ⟨degree_pos, fun h => ?_⟩
  by_contra hn
  let := typeF4RootPairing.indexNeg
  have hp := degree_pos ((RootPairing.Base.IsPos.neg_iff_not _ r).mpr hn)
  have hv : (-r).val = -r.val := by
    change typeF4RootPairing.root (-r) = -typeF4RootPairing.root r
    simp only [RootPairing.indexNeg_neg, RootPairing.root_reflectionPerm,
      RootPairing.reflection_apply_self]
  rw [hv] at hp
  simp only [degree, Pi.neg_apply] at hp h
  linarith

lemma long_of_norm (r : typeF4Roots) (h : dot r.val r.val = 2) : IsLongRoot r := by
  by_contra hn
  have := isShortRoot_norm r hn
  linarith

lemma short_of_norm (r : typeF4Roots) (h : dot r.val r.val = 1) : IsShortRoot r := by
  intro hl
  have := isLongRoot_norm r hl
  linarith

lemma scale_eq (r : typeF4Roots) :
    typeF4CorootScale r = 2 / dot r.val r.val := by
  classical
  by_cases h : IsLongRoot r
  · rw [typeF4CorootScale_of_pair r h, isLongRoot_norm r h]; norm_num
  · rw [typeF4CorootScale_of_not_pair r h, isShortRoot_norm r h]; norm_num

lemma dual_eq (r s : typeF4Roots)
    (h : ∀ i : Fin 4,
      (if (Fin.rev i).val < 2 then (1 : ℝ) else 2) *
        dot s.val (typeF4SimpleRoot (Fin.rev i)) =
      (2 / dot r.val r.val) * dot (typeF4SimpleRoot i) r.val) :
    exceptionalRootPermutation r = s := by
  have hp (i : Fin 4) :
      typeF4RootPairing.pairing (exceptionalRootPermutation r)
        (typeF4SimpleRootIndex (Fin.rev i)) =
      typeF4RootPairing.pairing s (typeF4SimpleRootIndex (Fin.rev i)) := by
    have he := congrArg (algebraMap ℤ ℝ)
      (WordRelations.exceptionalRootPermutation_pairingIn r (typeF4SimpleRootIndex i))
    simp only [RootPairing.algebraMap_pairingIn, exceptionalRootPermutation_simple,
      Fin.revPerm_apply] at he
    rw [he, typeF4RootPairing_pairing, typeF4RootPairing_pairing,
      typeF4CorootScale_simpleRoot, typeF4SimpleRootIndex_val, scale_eq]
    exact (h i).symm
  have h0 := hp 0
  have h1 := hp 1
  have h2 := hp 2
  have h3 := hp 3
  norm_num [typeF4RootPairing_pairing, typeF4CorootScale_simpleRoot,
    typeF4SimpleRootIndex_val, typeF4SimpleRoot, Fin.rev, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]
    at h0 h1 h2 h3
  apply Subtype.ext
  funext i
  fin_cases i <;> dsimp only <;> linarith! only [h0, h1, h2, h3]


/-- The positive roots, with pairs first and B₂ quartets second. -/
@[expose] public def table : Fin 24 → Vec 4
  | ⟨0, _⟩ => ![0, 1, -1, 0] -- 1000
  | ⟨1, _⟩ => ![(1 / 2), (-1 / 2), (-1 / 2), (-1 / 2)] -- 0001
  | ⟨2, _⟩ => ![0, 1, 1, 0] -- 1220
  | ⟨3, _⟩ => ![(1 / 2), (-1 / 2), (1 / 2), (1 / 2)] -- 0121
  | ⟨4, _⟩ => ![1, 0, 0, -1] -- 1222
  | ⟨5, _⟩ => ![(1 / 2), (1 / 2), (-1 / 2), (1 / 2)] -- 1121
  | ⟨6, _⟩ => ![1, 0, 0, 1] -- 1242
  | ⟨7, _⟩ => ![(1 / 2), (1 / 2), (1 / 2), (-1 / 2)] -- 1221
  | ⟨8, _⟩ => ![0, 0, 1, -1] -- 0100
  | ⟨9, _⟩ => ![0, 0, 0, 1] -- 0010
  | ⟨10, _⟩ => ![0, 0, 1, 0] -- 0110
  | ⟨11, _⟩ => ![0, 0, 1, 1] -- 0120
  | ⟨12, _⟩ => ![1, -1, 0, 0] -- 0122
  | ⟨13, _⟩ => ![0, 1, 0, 0] -- 1110
  | ⟨14, _⟩ => ![1, 0, 0, 0] -- 1232
  | ⟨15, _⟩ => ![1, 1, 0, 0] -- 2342
  | ⟨16, _⟩ => ![0, 1, 0, -1] -- 1100
  | ⟨17, _⟩ => ![(1 / 2), (-1 / 2), (-1 / 2), (1 / 2)] -- 0011
  | ⟨18, _⟩ => ![(1 / 2), (1 / 2), (-1 / 2), (-1 / 2)] -- 1111
  | ⟨19, _⟩ => ![1, 0, -1, 0] -- 1122
  | ⟨20, _⟩ => ![0, 1, 0, 1] -- 1120
  | ⟨21, _⟩ => ![(1 / 2), (-1 / 2), (1 / 2), (-1 / 2)] -- 0111
  | ⟨22, _⟩ => ![(1 / 2), (1 / 2), (1 / 2), (1 / 2)] -- 1231
  | ⟨23, _⟩ => ![1, 0, 1, 0] -- 1342
  | ⟨n + 24, h⟩ => False.elim (by omega)


/-- Simple-root coefficients in the standard Bourbaki order. -/
@[expose] public def coefficients : Fin 24 → Fin 4 → ℕ :=
  ![![1, 0, 0, 0],
    ![0, 0, 0, 1],
    ![1, 2, 2, 0],
    ![0, 1, 2, 1],
    ![1, 2, 2, 2],
    ![1, 1, 2, 1],
    ![1, 2, 4, 2],
    ![1, 2, 2, 1],
    ![0, 1, 0, 0],
    ![0, 0, 1, 0],
    ![0, 1, 1, 0],
    ![0, 1, 2, 0],
    ![0, 1, 2, 2],
    ![1, 1, 1, 0],
    ![1, 2, 3, 2],
    ![2, 3, 4, 2],
    ![1, 1, 0, 0],
    ![0, 0, 1, 1],
    ![1, 1, 1, 1],
    ![1, 1, 2, 2],
    ![1, 1, 2, 0],
    ![0, 1, 1, 1],
    ![1, 2, 3, 1],
    ![1, 3, 4, 2]]

/-- The labels of the table are the actual simple-root coefficients. -/
public theorem table_simpleCoefficient (i : Fin 24) (j : Fin 4) :
    typeF4SimpleCoefficient (table i) j = (coefficients i j : ℝ) := by
  fin_cases i <;> fin_cases j <;>
    norm_num [table, coefficients, typeF4SimpleCoefficient,
      Matrix.cons_val_two, Matrix.cons_val_three]

/-- Every row is an actual root of the standard F₄ root system. -/
public theorem table_mem (i : Fin 24) : table i ∈ typeF4Roots := by
  fin_cases i
  · refine Or.inl (Or.inl ⟨1, 2, by decide, 1, -1, by simp, by simp, ?_⟩)
    ext j
    fin_cases j <;>
      norm_num [table, basisVector, Pi.single_apply, Fin.ext_iff, halfSignVector,
        Matrix.cons_val_two, Matrix.cons_val_three]
  · refine Or.inr ⟨![true, false, false, false], ?_⟩
    ext j
    fin_cases j <;>
      norm_num [table, basisVector, Pi.single_apply, Fin.ext_iff, halfSignVector,
        Matrix.cons_val_two, Matrix.cons_val_three]
  · refine Or.inl (Or.inl ⟨1, 2, by decide, 1, 1, by simp, by simp, ?_⟩)
    ext j
    fin_cases j <;>
      norm_num [table, basisVector, Pi.single_apply, Fin.ext_iff, halfSignVector,
        Matrix.cons_val_two, Matrix.cons_val_three]
  · refine Or.inr ⟨![true, false, true, true], ?_⟩
    ext j
    fin_cases j <;>
      norm_num [table, basisVector, Pi.single_apply, Fin.ext_iff, halfSignVector,
        Matrix.cons_val_two, Matrix.cons_val_three]
  · refine Or.inl (Or.inl ⟨0, 3, by decide, 1, -1, by simp, by simp, ?_⟩)
    ext j
    fin_cases j <;>
      norm_num [table, basisVector, Pi.single_apply, Fin.ext_iff, halfSignVector,
        Matrix.cons_val_two, Matrix.cons_val_three]
  · refine Or.inr ⟨![true, true, false, true], ?_⟩
    ext j
    fin_cases j <;>
      norm_num [table, basisVector, Pi.single_apply, Fin.ext_iff, halfSignVector,
        Matrix.cons_val_two, Matrix.cons_val_three]
  · refine Or.inl (Or.inl ⟨0, 3, by decide, 1, 1, by simp, by simp, ?_⟩)
    ext j
    fin_cases j <;>
      norm_num [table, basisVector, Pi.single_apply, Fin.ext_iff, halfSignVector,
        Matrix.cons_val_two, Matrix.cons_val_three]
  · refine Or.inr ⟨![true, true, true, false], ?_⟩
    ext j
    fin_cases j <;>
      norm_num [table, basisVector, Pi.single_apply, Fin.ext_iff, halfSignVector,
        Matrix.cons_val_two, Matrix.cons_val_three]
  · refine Or.inl (Or.inl ⟨2, 3, by decide, 1, -1, by simp, by simp, ?_⟩)
    ext j
    fin_cases j <;>
      norm_num [table, basisVector, Pi.single_apply, Fin.ext_iff, halfSignVector,
        Matrix.cons_val_two, Matrix.cons_val_three]
  · refine Or.inl (Or.inr ⟨3, Or.inl ?_⟩)
    ext j
    fin_cases j <;>
      norm_num [table, basisVector, Pi.single_apply, Fin.ext_iff, halfSignVector,
        Matrix.cons_val_two, Matrix.cons_val_three]
  · refine Or.inl (Or.inr ⟨2, Or.inl ?_⟩)
    ext j
    fin_cases j <;>
      norm_num [table, basisVector, Pi.single_apply, Fin.ext_iff, halfSignVector,
        Matrix.cons_val_two, Matrix.cons_val_three]
  · refine Or.inl (Or.inl ⟨2, 3, by decide, 1, 1, by simp, by simp, ?_⟩)
    ext j
    fin_cases j <;>
      norm_num [table, basisVector, Pi.single_apply, Fin.ext_iff, halfSignVector,
        Matrix.cons_val_two, Matrix.cons_val_three]
  · refine Or.inl (Or.inl ⟨0, 1, by decide, 1, -1, by simp, by simp, ?_⟩)
    ext j
    fin_cases j <;>
      norm_num [table, basisVector, Pi.single_apply, Fin.ext_iff, halfSignVector,
        Matrix.cons_val_two, Matrix.cons_val_three]
  · refine Or.inl (Or.inr ⟨1, Or.inl ?_⟩)
    ext j
    fin_cases j <;>
      norm_num [table, basisVector, Pi.single_apply, Fin.ext_iff, halfSignVector,
        Matrix.cons_val_two, Matrix.cons_val_three]
  · refine Or.inl (Or.inr ⟨0, Or.inl ?_⟩)
    ext j
    fin_cases j <;>
      norm_num [table, basisVector, Pi.single_apply, Fin.ext_iff, halfSignVector,
        Matrix.cons_val_two, Matrix.cons_val_three]
  · refine Or.inl (Or.inl ⟨0, 1, by decide, 1, 1, by simp, by simp, ?_⟩)
    ext j
    fin_cases j <;>
      norm_num [table, basisVector, Pi.single_apply, Fin.ext_iff, halfSignVector,
        Matrix.cons_val_two, Matrix.cons_val_three]
  · refine Or.inl (Or.inl ⟨1, 3, by decide, 1, -1, by simp, by simp, ?_⟩)
    ext j
    fin_cases j <;>
      norm_num [table, basisVector, Pi.single_apply, Fin.ext_iff, halfSignVector,
        Matrix.cons_val_two, Matrix.cons_val_three]
  · refine Or.inr ⟨![true, false, false, true], ?_⟩
    ext j
    fin_cases j <;>
      norm_num [table, basisVector, Pi.single_apply, Fin.ext_iff, halfSignVector,
        Matrix.cons_val_two, Matrix.cons_val_three]
  · refine Or.inr ⟨![true, true, false, false], ?_⟩
    ext j
    fin_cases j <;>
      norm_num [table, basisVector, Pi.single_apply, Fin.ext_iff, halfSignVector,
        Matrix.cons_val_two, Matrix.cons_val_three]
  · refine Or.inl (Or.inl ⟨0, 2, by decide, 1, -1, by simp, by simp, ?_⟩)
    ext j
    fin_cases j <;>
      norm_num [table, basisVector, Pi.single_apply, Fin.ext_iff, halfSignVector,
        Matrix.cons_val_two, Matrix.cons_val_three]
  · refine Or.inl (Or.inl ⟨1, 3, by decide, 1, 1, by simp, by simp, ?_⟩)
    ext j
    fin_cases j <;>
      norm_num [table, basisVector, Pi.single_apply, Fin.ext_iff, halfSignVector,
        Matrix.cons_val_two, Matrix.cons_val_three]
  · refine Or.inr ⟨![true, false, true, false], ?_⟩
    ext j
    fin_cases j <;>
      norm_num [table, basisVector, Pi.single_apply, Fin.ext_iff, halfSignVector,
        Matrix.cons_val_two, Matrix.cons_val_three]
  · refine Or.inr ⟨![true, true, true, true], ?_⟩
    ext j
    fin_cases j <;>
      norm_num [table, basisVector, Pi.single_apply, Fin.ext_iff, halfSignVector,
        Matrix.cons_val_two, Matrix.cons_val_three]
  · refine Or.inl (Or.inl ⟨0, 2, by decide, 1, 1, by simp, by simp, ?_⟩)
    ext j
    fin_cases j <;>
      norm_num [table, basisVector, Pi.single_apply, Fin.ext_iff, halfSignVector,
        Matrix.cons_val_two, Matrix.cons_val_three]

/-- The root list has no repeated rows. -/
public theorem table_injective : Function.Injective table := by
  intro i j h
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  have h2 := congrFun h 2
  have h3 := congrFun h 3
  fin_cases i <;> fin_cases j <;>
    norm_num [table, Matrix.cons_val_two, Matrix.cons_val_three] at *

lemma table_positive (i : Fin 24) : 0 < degree (table i) := by
  fin_cases i <;> norm_num [table, degree, Matrix.cons_val_two, Matrix.cons_val_three]

/-- Every positive F₄ root occurs in the displayed list. -/
public theorem table_exhaustive (r : typeF4Roots) (hp : typeF4RootPairing_base.IsPos r) :
    ∃ i, table i = r.val := by
  have hd := degree_pos hp
  rcases r.property with (hpair | hunit) | hhalf
  · rcases hpair with ⟨i, j, hij, a, b, ha, hb, hv⟩
    have sign_cases (x : ℝ) (hx : x ∈ ({-1, 1} : Set ℝ)) : x = -1 ∨ x = 1 := hx
    rcases sign_cases a ha with rfl | rfl <;>
      rcases sign_cases b hb with rfl | rfl
    all_goals
      rw [hv] at hd ⊢
      fin_cases i <;> fin_cases j
    · exact (hij rfl).elim
    · norm_num [degree, basisVector, Pi.single_apply, Fin.ext_iff] at hd
    · norm_num [degree, basisVector, Pi.single_apply, Fin.ext_iff] at hd
    · norm_num [degree, basisVector, Pi.single_apply, Fin.ext_iff] at hd
    · norm_num [degree, basisVector, Pi.single_apply, Fin.ext_iff] at hd
    · exact (hij rfl).elim
    · norm_num [degree, basisVector, Pi.single_apply, Fin.ext_iff] at hd
    · norm_num [degree, basisVector, Pi.single_apply, Fin.ext_iff] at hd
    · norm_num [degree, basisVector, Pi.single_apply, Fin.ext_iff] at hd
    · norm_num [degree, basisVector, Pi.single_apply, Fin.ext_iff] at hd
    · exact (hij rfl).elim
    · norm_num [degree, basisVector, Pi.single_apply, Fin.ext_iff] at hd
    · norm_num [degree, basisVector, Pi.single_apply, Fin.ext_iff] at hd
    · norm_num [degree, basisVector, Pi.single_apply, Fin.ext_iff] at hd
    · norm_num [degree, basisVector, Pi.single_apply, Fin.ext_iff] at hd
    · exact (hij rfl).elim
    · exact (hij rfl).elim
    · norm_num [degree, basisVector, Pi.single_apply, Fin.ext_iff] at hd
    · norm_num [degree, basisVector, Pi.single_apply, Fin.ext_iff] at hd
    · norm_num [degree, basisVector, Pi.single_apply, Fin.ext_iff] at hd
    · refine ⟨12, ?_⟩
      ext t
      fin_cases t <;> norm_num [table, basisVector, Pi.single_apply, Fin.ext_iff,
        Matrix.cons_val_two, Matrix.cons_val_three]
    · exact (hij rfl).elim
    · norm_num [degree, basisVector, Pi.single_apply, Fin.ext_iff] at hd
    · norm_num [degree, basisVector, Pi.single_apply, Fin.ext_iff] at hd
    · refine ⟨19, ?_⟩
      ext t
      fin_cases t <;> norm_num [table, basisVector, Pi.single_apply, Fin.ext_iff,
        Matrix.cons_val_two, Matrix.cons_val_three]
    · refine ⟨0, ?_⟩
      ext t
      fin_cases t <;> norm_num [table, basisVector, Pi.single_apply, Fin.ext_iff,
        Matrix.cons_val_two, Matrix.cons_val_three]
    · exact (hij rfl).elim
    · norm_num [degree, basisVector, Pi.single_apply, Fin.ext_iff] at hd
    · refine ⟨4, ?_⟩
      ext t
      fin_cases t <;> norm_num [table, basisVector, Pi.single_apply, Fin.ext_iff,
        Matrix.cons_val_two, Matrix.cons_val_three]
    · refine ⟨16, ?_⟩
      ext t
      fin_cases t <;> norm_num [table, basisVector, Pi.single_apply, Fin.ext_iff,
        Matrix.cons_val_two, Matrix.cons_val_three]
    · refine ⟨8, ?_⟩
      ext t
      fin_cases t <;> norm_num [table, basisVector, Pi.single_apply, Fin.ext_iff,
        Matrix.cons_val_two, Matrix.cons_val_three]
    · exact (hij rfl).elim
    · exact (hij rfl).elim
    · refine ⟨12, ?_⟩
      ext t
      fin_cases t <;> norm_num [table, basisVector, Pi.single_apply, Fin.ext_iff,
        Matrix.cons_val_two, Matrix.cons_val_three]
    · refine ⟨19, ?_⟩
      ext t
      fin_cases t <;> norm_num [table, basisVector, Pi.single_apply, Fin.ext_iff,
        Matrix.cons_val_two, Matrix.cons_val_three]
    · refine ⟨4, ?_⟩
      ext t
      fin_cases t <;> norm_num [table, basisVector, Pi.single_apply, Fin.ext_iff,
        Matrix.cons_val_two, Matrix.cons_val_three]
    · norm_num [degree, basisVector, Pi.single_apply, Fin.ext_iff] at hd
    · exact (hij rfl).elim
    · refine ⟨0, ?_⟩
      ext t
      fin_cases t <;> norm_num [table, basisVector, Pi.single_apply, Fin.ext_iff,
        Matrix.cons_val_two, Matrix.cons_val_three]
    · refine ⟨16, ?_⟩
      ext t
      fin_cases t <;> norm_num [table, basisVector, Pi.single_apply, Fin.ext_iff,
        Matrix.cons_val_two, Matrix.cons_val_three]
    · norm_num [degree, basisVector, Pi.single_apply, Fin.ext_iff] at hd
    · norm_num [degree, basisVector, Pi.single_apply, Fin.ext_iff] at hd
    · exact (hij rfl).elim
    · refine ⟨8, ?_⟩
      ext t
      fin_cases t <;> norm_num [table, basisVector, Pi.single_apply, Fin.ext_iff,
        Matrix.cons_val_two, Matrix.cons_val_three]
    · norm_num [degree, basisVector, Pi.single_apply, Fin.ext_iff] at hd
    · norm_num [degree, basisVector, Pi.single_apply, Fin.ext_iff] at hd
    · norm_num [degree, basisVector, Pi.single_apply, Fin.ext_iff] at hd
    · exact (hij rfl).elim
    · exact (hij rfl).elim
    · refine ⟨15, ?_⟩
      ext t
      fin_cases t <;> norm_num [table, basisVector, Pi.single_apply, Fin.ext_iff,
        Matrix.cons_val_two, Matrix.cons_val_three]
    · refine ⟨23, ?_⟩
      ext t
      fin_cases t <;> norm_num [table, basisVector, Pi.single_apply, Fin.ext_iff,
        Matrix.cons_val_two, Matrix.cons_val_three]
    · refine ⟨6, ?_⟩
      ext t
      fin_cases t <;> norm_num [table, basisVector, Pi.single_apply, Fin.ext_iff,
        Matrix.cons_val_two, Matrix.cons_val_three]
    · refine ⟨15, ?_⟩
      ext t
      fin_cases t <;> norm_num [table, basisVector, Pi.single_apply, Fin.ext_iff,
        Matrix.cons_val_two, Matrix.cons_val_three]
    · exact (hij rfl).elim
    · refine ⟨2, ?_⟩
      ext t
      fin_cases t <;> norm_num [table, basisVector, Pi.single_apply, Fin.ext_iff,
        Matrix.cons_val_two, Matrix.cons_val_three]
    · refine ⟨20, ?_⟩
      ext t
      fin_cases t <;> norm_num [table, basisVector, Pi.single_apply, Fin.ext_iff,
        Matrix.cons_val_two, Matrix.cons_val_three]
    · refine ⟨23, ?_⟩
      ext t
      fin_cases t <;> norm_num [table, basisVector, Pi.single_apply, Fin.ext_iff,
        Matrix.cons_val_two, Matrix.cons_val_three]
    · refine ⟨2, ?_⟩
      ext t
      fin_cases t <;> norm_num [table, basisVector, Pi.single_apply, Fin.ext_iff,
        Matrix.cons_val_two, Matrix.cons_val_three]
    · exact (hij rfl).elim
    · refine ⟨11, ?_⟩
      ext t
      fin_cases t <;> norm_num [table, basisVector, Pi.single_apply, Fin.ext_iff,
        Matrix.cons_val_two, Matrix.cons_val_three]
    · refine ⟨6, ?_⟩
      ext t
      fin_cases t <;> norm_num [table, basisVector, Pi.single_apply, Fin.ext_iff,
        Matrix.cons_val_two, Matrix.cons_val_three]
    · refine ⟨20, ?_⟩
      ext t
      fin_cases t <;> norm_num [table, basisVector, Pi.single_apply, Fin.ext_iff,
        Matrix.cons_val_two, Matrix.cons_val_three]
    · refine ⟨11, ?_⟩
      ext t
      fin_cases t <;> norm_num [table, basisVector, Pi.single_apply, Fin.ext_iff,
        Matrix.cons_val_two, Matrix.cons_val_three]
    · exact (hij rfl).elim
  · rcases hunit with ⟨i, hv | hv⟩
    all_goals
      rw [hv] at hd ⊢
      fin_cases i
    · refine ⟨14, ?_⟩
      ext t
      fin_cases t <;> norm_num [table, basisVector, Pi.single_apply, Fin.ext_iff,
        Matrix.cons_val_two, Matrix.cons_val_three]
    · refine ⟨13, ?_⟩
      ext t
      fin_cases t <;> norm_num [table, basisVector, Pi.single_apply, Fin.ext_iff,
        Matrix.cons_val_two, Matrix.cons_val_three]
    · refine ⟨10, ?_⟩
      ext t
      fin_cases t <;> norm_num [table, basisVector, Pi.single_apply, Fin.ext_iff,
        Matrix.cons_val_two, Matrix.cons_val_three]
    · refine ⟨9, ?_⟩
      ext t
      fin_cases t <;> norm_num [table, basisVector, Pi.single_apply, Fin.ext_iff,
        Matrix.cons_val_two, Matrix.cons_val_three]
    · norm_num [degree, basisVector, Pi.single_apply, Fin.ext_iff] at hd
    · norm_num [degree, basisVector, Pi.single_apply, Fin.ext_iff] at hd
    · norm_num [degree, basisVector, Pi.single_apply, Fin.ext_iff] at hd
    · norm_num [degree, basisVector, Pi.single_apply, Fin.ext_iff] at hd
  · rcases hhalf with ⟨ε, hv⟩
    rw [← hv] at hd ⊢
    cases h0 : ε 0 <;> cases h1 : ε 1 <;> cases h2 : ε 2 <;> cases h3 : ε 3
    · norm_num [degree, basisVector, Pi.single_apply, Fin.ext_iff, halfSignVector, h0, h1, h2, h3] at hd
    · norm_num [degree, basisVector, Pi.single_apply, Fin.ext_iff, halfSignVector, h0, h1, h2, h3] at hd
    · norm_num [degree, basisVector, Pi.single_apply, Fin.ext_iff, halfSignVector, h0, h1, h2, h3] at hd
    · norm_num [degree, basisVector, Pi.single_apply, Fin.ext_iff, halfSignVector, h0, h1, h2, h3] at hd
    · norm_num [degree, basisVector, Pi.single_apply, Fin.ext_iff, halfSignVector, h0, h1, h2, h3] at hd
    · norm_num [degree, basisVector, Pi.single_apply, Fin.ext_iff, halfSignVector, h0, h1, h2, h3] at hd
    · norm_num [degree, basisVector, Pi.single_apply, Fin.ext_iff, halfSignVector, h0, h1, h2, h3] at hd
    · norm_num [degree, basisVector, Pi.single_apply, Fin.ext_iff, halfSignVector, h0, h1, h2, h3] at hd
    · refine ⟨1, ?_⟩
      ext t
      fin_cases t <;> norm_num [table, basisVector, Pi.single_apply, Fin.ext_iff,
        Matrix.cons_val_two, Matrix.cons_val_three, halfSignVector, h0, h1, h2, h3] <;>
          first | exact h0 | exact h1 | exact h2 | exact h3
    · refine ⟨17, ?_⟩
      ext t
      fin_cases t <;> norm_num [table, basisVector, Pi.single_apply, Fin.ext_iff,
        Matrix.cons_val_two, Matrix.cons_val_three, halfSignVector, h0, h1, h2, h3] <;>
          first | exact h0 | exact h1 | exact h2 | exact h3
    · refine ⟨21, ?_⟩
      ext t
      fin_cases t <;> norm_num [table, basisVector, Pi.single_apply, Fin.ext_iff,
        Matrix.cons_val_two, Matrix.cons_val_three, halfSignVector, h0, h1, h2, h3] <;>
          first | exact h0 | exact h1 | exact h2 | exact h3
    · refine ⟨3, ?_⟩
      ext t
      fin_cases t <;> norm_num [table, basisVector, Pi.single_apply, Fin.ext_iff,
        Matrix.cons_val_two, Matrix.cons_val_three, halfSignVector, h0, h1, h2, h3] <;>
          first | exact h0 | exact h1 | exact h2 | exact h3
    · refine ⟨18, ?_⟩
      ext t
      fin_cases t <;> norm_num [table, basisVector, Pi.single_apply, Fin.ext_iff,
        Matrix.cons_val_two, Matrix.cons_val_three, halfSignVector, h0, h1, h2, h3] <;>
          first | exact h0 | exact h1 | exact h2 | exact h3
    · refine ⟨5, ?_⟩
      ext t
      fin_cases t <;> norm_num [table, basisVector, Pi.single_apply, Fin.ext_iff,
        Matrix.cons_val_two, Matrix.cons_val_three, halfSignVector, h0, h1, h2, h3] <;>
          first | exact h0 | exact h1 | exact h2 | exact h3
    · refine ⟨7, ?_⟩
      ext t
      fin_cases t <;> norm_num [table, basisVector, Pi.single_apply, Fin.ext_iff,
        Matrix.cons_val_two, Matrix.cons_val_three, halfSignVector, h0, h1, h2, h3] <;>
          first | exact h0 | exact h1 | exact h2 | exact h3
    · refine ⟨22, ?_⟩
      ext t
      fin_cases t <;> norm_num [table, basisVector, Pi.single_apply, Fin.ext_iff,
        Matrix.cons_val_two, Matrix.cons_val_three, halfSignVector, h0, h1, h2, h3] <;>
          first | exact h0 | exact h1 | exact h2 | exact h3


/-- The linear radical omits the first pair. -/
@[expose] public def pairRow : (k : Support) → Fin (pairCount k) → Fin 4
  | .positive, i => i
  | .radical .suzuki, i => i
  | .radical .linear, i => i.succ

/-- The Suzuki radical omits the first quartet. -/
@[expose] public def quartetRow : (k : Support) → Fin (quartetCount k) → Fin 4
  | .positive, i => i
  | .radical .suzuki, i => i.succ
  | .radical .linear, i => i

/-- The row of the positive-root table assigned to a supported slot. -/
@[expose] public def index (k : Support) : Slot k → Fin 24
  | .inl (i, j) => ⟨2 * (pairRow k i).val + j.val, by
      have := (pairRow k i).isLt
      omega⟩
  | .inr (i, j) => ⟨8 + 4 * (quartetRow k i).val + j.val, by
      have := (quartetRow k i).isLt
      omega⟩

lemma index_injective (k : Support) : Function.Injective (index k) := by
  cases k with
  | positive => decide
  | radical s => cases s <;> decide

def Allowed (k : Support) (i : Fin 24) : Prop :=
  match k with
  | .positive => True
  | .radical .suzuki => i.val < 8 ∨ 12 ≤ i.val
  | .radical .linear => 2 ≤ i.val

instance (k : Support) (i : Fin 24) : Decidable (Allowed k i) := by
  cases k with
  | positive => exact inferInstanceAs (Decidable True)
  | radical s => cases s <;> unfold Allowed <;> infer_instance

lemma index_covers_allowed (k : Support) :
    ∀ i, Allowed k i → ∃ a, index k a = i := by
  cases k with
  | positive => decide
  | radical s => cases s <;> decide

lemma suzuki_radical_iff (r : typeF4Roots) :
    LargeLocalSeeds.IsRadicalRoot .suzuki r ↔
      typeF4RootPairing_base.IsPos r ∧
        (typeF4SimpleCoefficient r.val 0 ≠ 0 ∨ typeF4SimpleCoefficient r.val 3 ≠ 0) := by
  constructor
  · rintro ⟨hp, i, hi, hc⟩
    refine ⟨hp, ?_⟩
    fin_cases i
    · exact Or.inl hc
    · norm_num [LargeLocalSeeds.leviNodes] at hi
    · norm_num [LargeLocalSeeds.leviNodes, Fin.ext_iff] at hi
    · exact Or.inr hc
  · rintro ⟨hp, h0 | h3⟩
    · exact ⟨hp, 0, by simp [LargeLocalSeeds.leviNodes], h0⟩
    · exact ⟨hp, 3, by simp [LargeLocalSeeds.leviNodes, Fin.ext_iff], h3⟩

lemma linear_radical_iff (r : typeF4Roots) :
    LargeLocalSeeds.IsRadicalRoot .linear r ↔
      typeF4RootPairing_base.IsPos r ∧
        (typeF4SimpleCoefficient r.val 1 ≠ 0 ∨ typeF4SimpleCoefficient r.val 2 ≠ 0) := by
  constructor
  · rintro ⟨hp, i, hi, hc⟩
    refine ⟨hp, ?_⟩
    fin_cases i
    · norm_num [LargeLocalSeeds.leviNodes] at hi
    · exact Or.inl hc
    · exact Or.inr hc
    · norm_num [LargeLocalSeeds.leviNodes, Fin.ext_iff] at hi
  · rintro ⟨hp, h1 | h2⟩
    · exact ⟨hp, 1, by simp [LargeLocalSeeds.leviNodes, Fin.ext_iff], h1⟩
    · exact ⟨hp, 2, by simp [LargeLocalSeeds.leviNodes, Fin.ext_iff], h2⟩

lemma table_supported_iff (k : Support) (i : Fin 24) :
    Supported k ⟨table i, table_mem i⟩ ↔ Allowed k i := by
  have hp : typeF4RootPairing_base.IsPos ⟨table i, table_mem i⟩ :=
    (positive_iff _).mpr (table_positive i)
  cases k with
  | positive => exact iff_of_true hp trivial
  | radical s =>
    cases s
    · rw [Supported, suzuki_radical_iff, and_iff_right hp]
      fin_cases i <;> norm_num [table, typeF4SimpleCoefficient, Allowed,
        Matrix.cons_val_two, Matrix.cons_val_three]
    · rw [Supported, linear_radical_iff, and_iff_right hp]
      fin_cases i <;> norm_num [table, typeF4SimpleCoefficient, Allowed,
        Matrix.cons_val_two, Matrix.cons_val_three]

lemma index_allowed (k : Support) : ∀ a, Allowed k (index k a) := by
  cases k with
  | positive => decide
  | radical s => cases s <;> decide

lemma index_supported (k : Support) (a : Slot k) :
    Supported k ⟨table (index k a), table_mem _⟩ :=
  (table_supported_iff k _).mpr (index_allowed k a)

lemma index_covers (k : Support) (i : Fin 24)
    (h : Supported k ⟨table i, table_mem i⟩) : ∃ a, index k a = i :=
  index_covers_allowed k i ((table_supported_iff k i).mp h)

def rootMap (k : Support) (a : Slot k) : Root k :=
  ⟨⟨table (index k a), table_mem _⟩, index_supported k a⟩

lemma rootMap_bijective (k : Support) : Function.Bijective (rootMap k) := by
  refine ⟨fun a b h => index_injective k (table_injective
    (congrArg (fun r : Root k => r.val.val) h)), ?_⟩
  intro r
  have hp : typeF4RootPairing_base.IsPos r.val := by
    cases k with
    | positive => exact r.property
    | radical s => exact r.property.1
  obtain ⟨i, hi⟩ := table_exhaustive r.val hp
  have he : (⟨table i, table_mem i⟩ : typeF4Roots) = r.val := Subtype.ext hi
  obtain ⟨a, ha⟩ := index_covers k i (he.symm ▸ r.property)
  refine ⟨a, Subtype.ext (Subtype.ext ?_)⟩
  change table (index k a) = r.val.val
  rw [ha, hi]

def rootsEquiv (k : Support) : Slot k ≃ Root k :=
  Equiv.ofBijective (rootMap k) (rootMap_bijective k)

lemma rootsEquiv_val (k : Support) (a : Slot k) :
    (rootsEquiv k a).val.val = table (index k a) := rfl

lemma pair_norm (i : Fin 4) :
    dot (table ⟨2 * i.val, by omega⟩) (table ⟨2 * i.val, by omega⟩) = 2 := by
  fin_cases i <;> norm_num [table, dot, Fin.sum_univ_four,
    Matrix.cons_val_two, Matrix.cons_val_three]

lemma quartet_norm (i : Fin 4) :
    dot (table ⟨8 + 4 * i.val, by omega⟩) (table ⟨8 + 4 * i.val, by omega⟩) = 2 := by
  fin_cases i <;> norm_num [table, dot, Fin.sum_univ_four,
    Matrix.cons_val_two, Matrix.cons_val_three]

lemma quartet_two_norm (i : Fin 4) :
    dot (table ⟨8 + 4 * i.val + 2, by omega⟩)
      (table ⟨8 + 4 * i.val + 2, by omega⟩) = 1 := by
  fin_cases i <;> norm_num [table, dot, Fin.sum_univ_four,
    Matrix.cons_val_two, Matrix.cons_val_three]

lemma pair_dual (i : Fin 4) :
    exceptionalRootPermutation ⟨table ⟨2 * i.val, by omega⟩, table_mem _⟩ =
      ⟨table ⟨2 * i.val + 1, by omega⟩, table_mem _⟩ := by
  apply dual_eq
  intro j
  fin_cases i <;> fin_cases j <;>
    norm_num [table, dot, Fin.sum_univ_four, typeF4SimpleRoot, Fin.rev,
      Matrix.cons_val_two, Matrix.cons_val_three]

lemma quartet_dual_zero (i : Fin 4) :
    exceptionalRootPermutation ⟨table ⟨8 + 4 * i.val, by omega⟩, table_mem _⟩ =
      ⟨table ⟨8 + 4 * i.val + 1, by omega⟩, table_mem _⟩ := by
  apply dual_eq
  intro j
  fin_cases i <;> fin_cases j <;>
    norm_num [table, dot, Fin.sum_univ_four, typeF4SimpleRoot, Fin.rev,
      Matrix.cons_val_two, Matrix.cons_val_three]

lemma quartet_dual_two (i : Fin 4) :
    exceptionalRootPermutation ⟨table ⟨8 + 4 * i.val + 2, by omega⟩, table_mem _⟩ =
      ⟨table ⟨8 + 4 * i.val + 3, by omega⟩, table_mem _⟩ := by
  apply dual_eq
  intro j
  fin_cases i <;> fin_cases j <;>
    norm_num [table, dot, Fin.sum_univ_four, typeF4SimpleRoot, Fin.rev,
      Matrix.cons_val_two, Matrix.cons_val_three]

lemma pair_dot (i : Fin 4) :
    dot (table ⟨2 * i.val, by omega⟩) (table ⟨2 * i.val + 1, by omega⟩) = 0 := by
  fin_cases i <;> norm_num [table, dot, Fin.sum_univ_four,
    Matrix.cons_val_two, Matrix.cons_val_three]

lemma quartet_dot (i : Fin 4) :
    dot (table ⟨8 + 4 * i.val, by omega⟩)
      (table ⟨8 + 4 * i.val + 1, by omega⟩) = -1 := by
  fin_cases i <;> norm_num [table, dot, Fin.sum_univ_four,
    Matrix.cons_val_two, Matrix.cons_val_three]

lemma quartet_add (i : Fin 4) :
    table ⟨8 + 4 * i.val + 2, by omega⟩ =
      table ⟨8 + 4 * i.val, by omega⟩ + table ⟨8 + 4 * i.val + 1, by omega⟩ := by
  ext j
  fin_cases i <;> fin_cases j <;> norm_num [table,
    Matrix.cons_val_two, Matrix.cons_val_three]

lemma quartet_add_two (i : Fin 4) :
    table ⟨8 + 4 * i.val + 3, by omega⟩ =
      table ⟨8 + 4 * i.val, by omega⟩ + (2 : ℝ) • table ⟨8 + 4 * i.val + 1, by omega⟩ := by
  ext j
  fin_cases i <;> fin_cases j <;> norm_num [table,
    Matrix.cons_val_two, Matrix.cons_val_three]

end RootPartition

open RootPartition

/-- The explicit stable pair/quartet partition of each Ree support. -/
public def rootBlocks (k : Support) : RootBlocks k where
  roots := rootsEquiv k
  pair_long i := long_of_norm _ (pair_norm (pairRow k i))
  pair_dual i := pair_dual (pairRow k i)
  pair_dot i := pair_dot (pairRow k i)
  quartet_long i := long_of_norm _ (quartet_norm (quartetRow k i))
  quartet_dual_zero i := quartet_dual_zero (quartetRow k i)
  quartet_short_two i := short_of_norm _ (quartet_two_norm (quartetRow k i))
  quartet_dual_two i := quartet_dual_two (quartetRow k i)
  quartet_dot i := quartet_dot (quartetRow k i)
  quartet_add i := quartet_add (quartetRow k i)
  quartet_add_two i := quartet_add_two (quartetRow k i)

/-- The layout retains the concrete table order on every support. -/
public theorem rootBlocks_roots_val (k : Support) (a : Slot k) :
    ((rootBlocks k).roots a).val.val = table (index k a) := by
  exact rootsEquiv_val k a

/-- All geometric obligations in `RootBlocks` hold for each of the three supports. -/
public theorem rootBlocks_nonempty (k : Support) : Nonempty (RootBlocks k) :=
  ⟨rootBlocks k⟩

end ReeF4.Parabolics.RadicalCoordinates.FixedCoordinates
