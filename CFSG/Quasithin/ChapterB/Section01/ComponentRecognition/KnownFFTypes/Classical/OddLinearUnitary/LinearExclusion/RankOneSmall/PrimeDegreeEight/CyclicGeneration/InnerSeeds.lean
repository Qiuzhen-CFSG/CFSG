module

public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.KnownFFTypes.Classical.OddLinearUnitary.LinearExclusion.RankOneSmall.PrimeDegreeEight.CyclicGeneration.Seeds

/-!
# Four generating inner involutions over the four small prime fields

For p = 13, 17, 19, 23, use the image of the matrix `[[0,-1],[1,0]]`
in the literal quotient SL₂/Z(SL₂), with conjugators `1`, `U(1)`, `U(2)`,
and `L(1)`. The displayed words below give `±U(1)` and `±L(1)`. Their
identities are checked by the kernel using `decide`; since the initial lift
squares to `-I`, the lifted subgroup contains both root generators. Powers
give all prime-field transvections, so SL₂ generation descends to PSL₂.

This constructs the inner seed premise used by
`cyclicModelGeneration_of_seeds`. It is the small-prime calculation for
Guralnick--Malle, *Classification of 2F-modules I*, Proposition 4.1,
manuscript pp.8--9, as used in Aschbacher--Smith K.2, printed p.453.
The diagonal outer seed premise has a separate construction and assembly owner.
-/

open Matrix Subgroup GorensteinWalter
open scoped MatrixGroups

namespace CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Classical.OddLinearUnitary.LinearExclusion.RankOneSmall.PrimeDegreeEight.CyclicGeneration

private def upper {F : Type*} [CommRing F] (a : F) : SL(2,F) :=
  SpecialLinearGroup.transvection (by decide : (0 : Fin 2) ≠ 1) a

private def lower {F : Type*} [CommRing F] (a : F) : SL(2,F) :=
  SpecialLinearGroup.transvection (by decide : (1 : Fin 2) ≠ 0) a

private def lift {F : Type*} [CommRing F] : SL(2,F) :=
  ⟨!![0, -1; 1, 0], by simp⟩

private def conjugators {F : Type*} [CommRing F] : Fin 4 → SL(2,F) :=
  ![1, upper 1, upper 2, lower 1]

private def raw {F : Type*} [CommRing F] : Fin 4 → Matrix (Fin 2) (Fin 2) F :=
  ![!![0, -1; 1, 0], !![1, -2; 1, -1],
    !![2, -5; 1, -2], !![1, -1; 2, -1]]

private theorem conjugate_val {F : Type*} [CommRing F] (i : Fin 4) :
    ((conjugators i * lift * (conjugators i)⁻¹ : SL(2,F)) :
      Matrix (Fin 2) (Fin 2) F) = raw i := by
  simp only [SpecialLinearGroup.coe_mul]
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

private theorem lift_sq {F : Type*} [CommRing F] : (lift : SL(2,F)) ^ 2 = -1 := by
  rw [pow_two]
  apply Subtype.ext
  simp only [SpecialLinearGroup.coe_mul, SpecialLinearGroup.coe_neg,
    SpecialLinearGroup.coe_one]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [lift, Matrix.mul_apply, Fin.sum_univ_two]

private theorem words_generate {p : ℕ} [Fact p.Prime] (wu wl : List (Fin 4))
    (hu : (wu.map (raw (F := ZMod p))).prod = (upper 1).val ∨
      (wu.map (raw (F := ZMod p))).prod = -(upper 1).val)
    (hl : (wl.map (raw (F := ZMod p))).prod = (lower 1).val ∨
      (wl.map (raw (F := ZMod p))).prod = -(lower 1).val) :
    closure (Set.range fun i : Fin 4 =>
      (conjugators i * lift * (conjugators i)⁻¹ : SL(2, ZMod p))) = ⊤ := by
  let s (i : Fin 4) : SL(2, ZMod p) := conjugators i * lift * (conjugators i)⁻¹
  let H := closure (Set.range s)
  have hs (i : Fin 4) : s i ∈ H := subset_closure ⟨i, rfl⟩
  have ht : (lift : SL(2, ZMod p)) ∈ H := by
    simpa [s, conjugators] using hs 0
  have hneg : (-1 : SL(2, ZMod p)) ∈ H := by
    rw [← lift_sq]
    exact H.pow_mem ht 2
  have hw (w : List (Fin 4)) : (w.map s).prod ∈ H := by
    apply H.list_prod_mem
    intro x hx
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp hx
    exact hs i
  have hv (w : List (Fin 4)) : ((w.map s).prod).val =
      (w.map (raw (F := ZMod p))).prod := by
    change SpecialLinearGroup.coeMonoidHom _ = _
    simp only [map_list_prod, List.map_map, Function.comp_def,
      SpecialLinearGroup.coeMonoidHom_apply, s, conjugate_val]
  have mem_of_word (w : List (Fin 4)) (A : SL(2, ZMod p))
      (h : (w.map (raw (F := ZMod p))).prod = A.val ∨
        (w.map (raw (F := ZMod p))).prod = -A.val) : A ∈ H := by
    rcases h with h | h
    · have he : (w.map s).prod = A := Subtype.ext ((hv w).trans h)
      exact he ▸ hw w
    · have he : (w.map s).prod = -A := Subtype.ext ((hv w).trans h)
      have hm := H.mul_mem hneg (he ▸ hw w)
      simpa using hm
  exact root_mem H (mem_of_word wu _ hu) (mem_of_word wl _ hl)

private theorem upper13 : (([3, 0, 2, 3, 0, 2, 0, 2] : List (Fin 4)).map
    (raw (F := ZMod 13))).prod = -(upper 1).val := by decide

private theorem lower13 : (([1, 0, 2, 0, 2, 0, 3, 2] : List (Fin 4)).map
    (raw (F := ZMod 13))).prod = -(lower 1).val := by decide

private theorem upper17 : (([0, 1, 0, 1, 0, 1, 0, 3, 2, 3, 2] : List (Fin 4)).map
    (raw (F := ZMod 17))).prod = (upper 1).val := by decide

private theorem lower17 : (([0, 2, 3, 2, 3, 0, 1, 0, 1, 0, 1] : List (Fin 4)).map
    (raw (F := ZMod 17))).prod = -(lower 1).val := by decide

private theorem upper19 : (([0, 2, 3, 0, 3, 0, 1, 0, 2, 3] : List (Fin 4)).map
    (raw (F := ZMod 19))).prod = (upper 1).val := by decide

private theorem lower19 : (([0, 3, 2, 0, 1, 0, 3, 0, 3, 2] : List (Fin 4)).map
    (raw (F := ZMod 19))).prod = (lower 1).val := by decide

private theorem upper23 : (([0, 1, 0, 1, 0, 3, 2, 3, 0, 1, 3, 2] : List (Fin 4)).map
    (raw (F := ZMod 23))).prod = (upper 1).val := by decide

private theorem lower23 : (([2, 0, 3, 0, 1, 2, 0, 1, 0, 3, 2] : List (Fin 4)).map
    (raw (F := ZMod 23))).prod = -(lower 1).val := by decide

private theorem seed_of_generation {p : ℕ} [Fact p.Prime]
    (hgen : closure (Set.range fun i : Fin 4 =>
      (conjugators i * lift * (conjugators i)⁻¹ : SL(2, ZMod p))) = ⊤) :
    ∃ t : PSL2 (ZMod p), t ≠ 1 ∧ t ^ 2 = 1 ∧
      ∃ c : Fin 4 → PSL2 (ZMod p),
        closure (Set.range fun i => c i * t * (c i)⁻¹) = ⊤ := by
  let q : SL(2, ZMod p) →* PSL2 (ZMod p) := QuotientGroup.mk' (center _)
  refine ⟨q lift, ?_, ?_, fun i => q (conjugators i), ?_⟩
  · intro ht
    obtain ⟨a, _, ha⟩ := SpecialLinearGroup.mem_center_iff.mp
      ((QuotientGroup.eq_one_iff lift).mp ht)
    have hentry := congrArg (fun M : Matrix (Fin 2) (Fin 2) (ZMod p) => M 1 0) ha
    simp [lift] at hentry
  · rw [← map_pow, lift_sq]
    exact (QuotientGroup.eq_one_iff _).mpr
      (Subgroup.mem_center_iff.mpr fun g => by simp)
  · let H := closure (Set.range fun i : Fin 4 =>
      q (conjugators i) * q lift * (q (conjugators i))⁻¹)
    have hle : closure (Set.range fun i : Fin 4 =>
        (conjugators i * lift * (conjugators i)⁻¹ : SL(2, ZMod p))) ≤ H.comap q := by
      apply (closure_le _).mpr
      rintro _ ⟨i, rfl⟩
      change q (conjugators i * lift * (conjugators i)⁻¹) ∈ H
      simp only [map_mul, map_inv]
      exact subset_closure ⟨i, rfl⟩
    apply top_unique
    intro x _
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (center SL(2, ZMod p)) x
    apply hle
    rw [hgen]
    exact mem_top y

/-- The four prime fields admit four generating conjugates of an actual inner involution. -/
public theorem innerSeeds : InnerSeeds := by
  intro p _ hp
  rcases hp with rfl | rfl | rfl | rfl
  · apply seed_of_generation
    apply words_generate [3, 0, 2, 3, 0, 2, 0, 2] [1, 0, 2, 0, 2, 0, 3, 2]
    · exact Or.inr upper13
    · exact Or.inr lower13
  · apply seed_of_generation
    apply words_generate [0, 1, 0, 1, 0, 1, 0, 3, 2, 3, 2] [0, 2, 3, 2, 3, 0, 1, 0, 1, 0, 1]
    · exact Or.inl upper17
    · exact Or.inr lower17
  · apply seed_of_generation
    apply words_generate [0, 2, 3, 0, 3, 0, 1, 0, 2, 3] [0, 3, 2, 0, 1, 0, 3, 0, 3, 2]
    · exact Or.inl upper19
    · exact Or.inl lower19
  · apply seed_of_generation
    apply words_generate [0, 1, 0, 1, 0, 3, 2, 3, 0, 1, 3, 2] [2, 0, 3, 0, 1, 2, 0, 1, 0, 3, 2]
    · exact Or.inl upper23
    · exact Or.inr lower23

end CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Classical.OddLinearUnitary.LinearExclusion.RankOneSmall.PrimeDegreeEight.CyclicGeneration
