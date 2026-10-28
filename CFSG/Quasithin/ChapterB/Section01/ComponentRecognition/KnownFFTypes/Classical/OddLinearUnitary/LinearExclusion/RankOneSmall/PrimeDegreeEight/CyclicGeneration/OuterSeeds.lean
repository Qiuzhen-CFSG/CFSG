module

public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.KnownFFTypes.Classical.OddLinearUnitary.LinearExclusion.RankOneSmall.PrimeDegreeEight.CyclicGeneration.Seeds
public import GorensteinWalter.PGL2DeterminantSquare
public import Mathlib.Algebra.Field.ZMod
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

/-!
# Four conjugates of a diagonal outer involution

For p = 13, 17, 19, 23 take respectively d = 2, 3, 2, 5 and the PGL₂
class of [[0,-d],[1,0]]. Its square is scalar, and its nonsquare determinant
puts it outside the canonical PSL₂ image. Conjugate it by the PSL₂ classes
of 1, U(1), U(2), L(1). Eight explicit words, checked by kernel reduction,
give nonzero scalar multiples of U(1) and L(1). Scalars disappear in PGL₂;
the two root elements generate SL₂ over the prime field, proving containment
of the entire canonical PSL₂ image.

The words were found by finite search; only their checked matrix identities
are used in the proof. This supplies the diagonal-outer representative input
to the cyclic actor reduction, not the whole representation-theoretic exclusion.

Source: Guralnick--Malle, Classification of 2F-modules I, Proposition 4.1,
manuscript pp.8--9; Aschbacher--Smith K.2, printed p.453.
-/

open Matrix Subgroup
open scoped MatrixGroups

namespace CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Classical.OddLinearUnitary.LinearExclusion.RankOneSmall.PrimeDegreeEight.CyclicGeneration

private def raw {F : Type*} [CommRing F] (d : F) : Fin 4 → Matrix (Fin 2) (Fin 2) F :=
  ![!![0, -d; 1, 0], !![1, -d - 1; 1, -1],
    !![2, -d - 4; 1, -2], !![d, -d; 1 + d, -d]]

private def upper {F : Type*} [Field F] (a : F) : SL(2, F) :=
  SpecialLinearGroup.transvection (by decide : (0 : Fin 2) ≠ 1) a

private def lower {F : Type*} [Field F] (a : F) : SL(2, F) :=
  SpecialLinearGroup.transvection (by decide : (1 : Fin 2) ≠ 0) a

private def conjugators {F : Type*} [Field F] : Fin 4 → SL(2, F) :=
  ![1, upper 1, upper 2, lower 1]

private def lift {F : Type*} [Field F] (d : F) (hd : d ≠ 0) : GL (Fin 2) F :=
  GeneralLinearGroup.mkOfDetNeZero !![0, -d; 1, 0] (by simpa using hd)

private theorem conjugate_val {F : Type*} [Field F] (d : F) (hd : d ≠ 0) (i : Fin 4) :
    ((SpecialLinearGroup.toGL (conjugators i) * lift d hd *
      (SpecialLinearGroup.toGL (conjugators i))⁻¹ : GL (Fin 2) F) :
        Matrix (Fin 2) (Fin 2) F) = raw d i := by
  rw [← map_inv]
  fin_cases i <;>
    ext j k <;> fin_cases j <;> fin_cases k <;>
    simp [conjugators, upper, lower, SpecialLinearGroup.transvection_inv,
      SpecialLinearGroup.transvection_coe, lift, raw,
      Matrix.mul_apply, Fin.sum_univ_two] <;> ring

private theorem root_mem {p : ℕ} [Fact p.Prime] (H : Subgroup SL(2, ZMod p))
    (hu : upper 1 ∈ H) (hl : lower 1 ∈ H) : H = ⊤ := by
  have ht {i j : Fin 2} (hij : i ≠ j)
      (h : SpecialLinearGroup.transvection hij (1 : ZMod p) ∈ H) (a : ZMod p) :
      SpecialLinearGroup.transvection hij a ∈ H := by
    have hpow (n : ℕ) : SpecialLinearGroup.transvection hij (1 : ZMod p) ^ n =
        SpecialLinearGroup.transvection hij (n : ZMod p) := by
      induction n with
      | zero => simp [SpecialLinearGroup.transvection_coeff_zero]
      | succ n ih => rw [pow_succ, ih, ← SpecialLinearGroup.transvection_add, Nat.cast_add, Nat.cast_one]
    rw [← ZMod.natCast_zmod_val a, ← hpow]
    exact H.pow_mem h _
  apply top_unique
  intro A _
  apply Matrix.SL2.transvection_induction (fun A => A ∈ H) ?_ (fun _ _ => H.mul_mem) A
  intro i j hij a
  fin_cases i <;> fin_cases j
  · exact (hij rfl).elim
  · exact ht hij hu a
  · exact ht hij hl a
  · exact (hij rfl).elim


private def liftedConjugate {F : Type*} [Field F] (d : F) (hd : d ≠ 0) (i : Fin 4) :
    GL (Fin 2) F :=
  SpecialLinearGroup.toGL (conjugators i) * lift d hd *
    (SpecialLinearGroup.toGL (conjugators i))⁻¹

private def generated {F : Type*} [Field F] (d : F) (hd : d ≠ 0) : Subgroup PGL(2, F) :=
  closure (Set.range fun i => ProjGenLinGroup.mk (liftedConjugate d hd i))

private theorem lifted_prod_val {F : Type*} [Field F] (d : F) (hd : d ≠ 0)
    (w : List (Fin 4)) :
    (((w.map (liftedConjugate d hd)).prod : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
      (w.map (raw d)).prod := by
  induction w with
  | nil => rfl
  | cons i w ih =>
    simp only [List.map_cons, List.prod_cons, GeneralLinearGroup.coe_mul,
      ih]
    rw [show (liftedConjugate d hd i : Matrix (Fin 2) (Fin 2) F) = raw d i from conjugate_val d hd i]

private theorem word_mem {F : Type*} [Field F] (d : F) (hd : d ≠ 0)
    (w : List (Fin 4)) :
    ProjGenLinGroup.mk ((w.map (liftedConjugate d hd)).prod) ∈ generated d hd := by
  induction w with
  | nil => exact (generated d hd).one_mem
  | cons i w ih =>
    simp only [List.map_cons, List.prod_cons, map_mul]
    exact (generated d hd).mul_mem (subset_closure ⟨i, rfl⟩) ih

private theorem scalar_word_mem {F : Type*} [Field F] (d : F) (hd : d ≠ 0)
    (w : List (Fin 4)) (a : F) (ha : a ≠ 0) (S : SL(2, F))
    (hw : (w.map (raw d)).prod = a • (S : Matrix (Fin 2) (Fin 2) F)) :
    SpecialLinearGroup.toPGL S ∈ generated d hd := by
  have he : (w.map (liftedConjugate d hd)).prod =
      GeneralLinearGroup.scalar (Fin 2) (Units.mk0 a ha) * SpecialLinearGroup.toGL S := by
    apply Units.ext
    rw [lifted_prod_val, hw]
    ext i j
    simp [GeneralLinearGroup.coe_scalar, Matrix.scalar, Matrix.diagonal_mul, smul_eq_mul]
  have hm := word_mem d hd w
  rw [he, map_mul, ProjGenLinGroup.mk_scalar, one_mul] at hm
  exact hm

private theorem seed_square {F : Type*} [Field F] (d : F) (hd : d ≠ 0) :
    ProjGenLinGroup.mk (lift d hd) ^ 2 = 1 := by
  have he : lift d hd ^ 2 = GeneralLinearGroup.scalar (Fin 2) (Units.mk0 (-d) (neg_ne_zero.mpr hd)) := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [pow_two, lift, Matrix.mul_apply, Fin.sum_univ_two,
        GeneralLinearGroup.coe_scalar, Matrix.scalar]
  rw [← map_pow, he, ProjGenLinGroup.mk_scalar]

private theorem seed_outer {F : Type*} [Field F] (d : F) (hd : d ≠ 0) (hns : ¬ IsSquare d) :
    ProjGenLinGroup.mk (lift d hd) ∉
      (ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := F)).range := by
  rw [GorensteinWalter.pgl2_mk_mem_psl2_range_iff_det_isSquare]
  simpa [lift] using hns

private theorem generated_contains_range {p : ℕ} [Fact p.Prime] (d : ZMod p) (hd : d ≠ 0)
    (hu : SpecialLinearGroup.toPGL (upper (1 : ZMod p)) ∈ generated d hd)
    (hl : SpecialLinearGroup.toPGL (lower (1 : ZMod p)) ∈ generated d hd) :
    (ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := ZMod p)).range ≤
      generated d hd := by
  have ht := root_mem ((generated d hd).comap SpecialLinearGroup.toPGL) hu hl
  rintro _ ⟨x, rfl⟩
  obtain ⟨S, rfl⟩ := QuotientGroup.mk_surjective x
  exact (show S ∈ (generated d hd).comap SpecialLinearGroup.toPGL from ht.symm ▸ mem_top S)


private def Configuration (p : ℕ) : Prop :=
  ∃ t : PGL(2, ZMod p), t ^ 2 = 1 ∧
      t ∉ (ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := ZMod p)).range ∧
      ∃ c : Fin 4 → PSL(2, ZMod p),
        (ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := ZMod p)).range ≤
          closure (Set.range fun i => ProjectiveSpecialLinearGroup.toPGL (c i) * t *
            (ProjectiveSpecialLinearGroup.toPGL (c i))⁻¹)

private theorem outer_configuration {p : ℕ} [Fact p.Prime] (d : ZMod p) (hd : d ≠ 0)
    (hns : ¬ IsSquare d)
    (hu : SpecialLinearGroup.toPGL (upper (1 : ZMod p)) ∈ generated d hd)
    (hl : SpecialLinearGroup.toPGL (lower (1 : ZMod p)) ∈ generated d hd) :
    Configuration p := by
  refine ⟨ProjGenLinGroup.mk (lift d hd), seed_square d hd, seed_outer d hd hns,
    fun i => QuotientGroup.mk (conjugators i), ?_⟩
  simpa only [generated, liftedConjugate, map_mul, map_inv,
    ProjectiveSpecialLinearGroup.toPGL_mk] using generated_contains_range d hd hu hl


local instance : Fact (Nat.Prime 13) := ⟨by decide⟩

private theorem configuration13 : Configuration 13 := by
  apply outer_configuration 2 (by decide) (by decide)
  · apply scalar_word_mem 2 (by decide) [0, 1, 3, 0, 2, 0] 8 (by decide)
    decide
  · apply scalar_word_mem 2 (by decide) [0, 2, 3, 1, 0, 1, 3, 1] 3 (by decide)
    decide

local instance : Fact (Nat.Prime 17) := ⟨by decide⟩

private theorem configuration17 : Configuration 17 := by
  apply outer_configuration 3 (by decide) (by decide)
  · apply scalar_word_mem 3 (by decide) [0, 2, 0, 1, 2, 0, 3, 2] 13 (by decide)
    decide
  · apply scalar_word_mem 3 (by decide) [0, 2, 0, 1, 0, 3, 0, 3] 4 (by decide)
    decide

local instance : Fact (Nat.Prime 19) := ⟨by decide⟩

private theorem configuration19 : Configuration 19 := by
  apply outer_configuration 2 (by decide) (by decide)
  · apply scalar_word_mem 2 (by decide) [3, 1, 2, 0, 2, 1, 2, 0, 2, 3] 6 (by decide)
    decide
  · apply scalar_word_mem 2 (by decide) [0, 2, 3, 0, 1, 2, 3, 0, 3, 0] 6 (by decide)
    decide

local instance : Fact (Nat.Prime 23) := ⟨by decide⟩

private theorem configuration23 : Configuration 23 := by
  apply outer_configuration 5 (by decide) (by decide)
  · apply scalar_word_mem 5 (by decide) [0, 2, 1, 3, 2, 0, 3, 1, 3, 0] 20 (by decide)
    decide
  · apply scalar_word_mem 5 (by decide) [1, 2, 1, 2, 0, 2, 1, 3] 19 (by decide)
    decide

/-- Four inner conjugates of an explicit diagonal outer involution contain
all of the canonical PSL₂ image at each of the four small primes. This supplies
the outer-seed premise of `cyclicModelGeneration_of_seeds`. -/
public theorem outerSeeds : OuterSeeds := by
  intro p _ hp
  rcases hp with rfl | rfl | rfl | rfl
  · exact configuration13
  · exact configuration17
  · exact configuration19
  · exact configuration23

end CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Classical.OddLinearUnitary.LinearExclusion.RankOneSmall.PrimeDegreeEight.CyclicGeneration
