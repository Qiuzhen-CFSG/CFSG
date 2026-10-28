module

public import Theory.SpecificGroups.PSp4Three.ProjectiveGeometry
public import Mathlib.GroupTheory.GroupAction.Primitive
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.Field.ZMod

/-!
# Primitivity of the projective action of PSp₄(3)

A block through a point is a union of full point-stabilizer orbits. The orbit
sizes 1, 12, and 27 force its size to be 1, 13, 28, or 40; divisibility leaves
only 1 and 40. This establishes primitivity without a subgroup catalogue.

Adapted from Gerald Höhn, ATLAS, revision `8eabb35afe2b5e45bf913a2d05c53e558d2e2917`,
from `Atlas/GroupTheory/FiniteSuborbitPrimitivity.lean`, `Atlas/GroupTheory/RankThreePrimitivity.lean`.
Covered adaptations retain the ATLAS Research and Attribution License 1.0
(`LICENSES/ATLAS.txt`; citation: `LICENSES/ATLAS-CITATION.cff`).
Changes: CFSG imports and module boundaries; local namespace to avoid
collisions with other ports; unused results outside this argument omitted.
-/

@[expose] public section

noncomputable section
namespace Matrix.PSp4Three.Blocks
open scoped Pointwise BigOperators
open MulAction

/-- A finite partition into transitive point-stabilizer classes determines every block size. -/
theorem block_card_suborbit_sum {G X I : Type*} [Group G] [MulAction G X]
    [Finite X] [Fintype I] [DecidableEq I] (a : X) (f : X → I)
    (htrans : ∀ x y, f x = f y → ∃ g : stabilizer G a, g • x = y)
    (d : I → ℕ) (hd : ∀ i, Nat.card {x : X // f x = i} = d i)
    (B : Set X) (ha : a ∈ B) (hB : IsBlock G B) :
    ∃ T : Finset I, f a ∈ T ∧ Nat.card B = ∑ i ∈ T, d i := by
  classical
  let : Fintype X := Fintype.ofFinite _
  let T := Finset.univ.filter (fun i => ∃ x ∈ B, f x = i)
  have hs (i : I) (hi : i ∈ T) (y : X) (hy : f y = i) : y ∈ B := by
    obtain ⟨x,hx,hf⟩ := (Finset.mem_filter.mp hi).2
    obtain ⟨g,hg⟩ := htrans x y (hf.trans hy.symm)
    have hfix : g.val • B = B := hB.stabilizer_le ha g.prop
    rw [← hg]
    change g.val • x ∈ B
    rw [← hfix,Set.smul_mem_smul_set_iff]
    exact hx
  have hf (i : I) : Nat.card {x : B // f x.val = i} = if i ∈ T then d i else 0 := by
    split_ifs with hi
    · let e : {x : B // f x.val = i} ≃ {x : X // f x = i} :=
        { toFun := fun x => ⟨x.val.val,x.prop⟩
          invFun := fun x => ⟨⟨x.val,hs i hi x.val x.prop⟩,x.prop⟩
          left_inv := fun _ => rfl
          right_inv := fun _ => rfl }
      exact (Nat.card_congr e).trans (hd i)
    · have he : IsEmpty {x : B // f x.val = i} := ⟨fun x => hi
        (Finset.mem_filter.mpr ⟨Finset.mem_univ _,x.val.val,x.val.prop,x.prop⟩)⟩
      let := he
      simp
  refine ⟨T,Finset.mem_filter.mpr ⟨Finset.mem_univ _,a,ha,rfl⟩,?_⟩
  rw [← Nat.card_congr (Equiv.sigmaFiberEquiv (fun x : B => f x.val)),Nat.card_sigma]
  simp_rw [hf]
  simp

/-- Primitivity from a finite suborbit partition and its divisibility obstruction. -/
theorem primitive_of_suborbit_sums {G X I : Type*} [Group G] [MulAction G X]
    [Finite X] [IsPretransitive G X] [Fintype I] [DecidableEq I]
    (a : X) (f : X → I)
    (htrans : ∀ x y, f x = f y → ∃ g : stabilizer G a, g • x = y)
    (d : I → ℕ) (hd : ∀ i, Nat.card {x : X // f x = i} = d i)
    (harith : ∀ T : Finset I, f a ∈ T → (∑ i ∈ T, d i) ∣ Nat.card X →
      (∑ i ∈ T, d i) = 1 ∨ (∑ i ∈ T, d i) = Nat.card X) :
    IsPreprimitive G X := by
  apply IsPreprimitive.of_isTrivialBlock_base a
  intro B ha hB
  obtain ⟨T,haT,hc⟩ := block_card_suborbit_sum a f htrans d hd B ha hB
  have hh : (∑ i ∈ T, d i) ∣ Nat.card X := hc ▸ hB.ncard_dvd_card ⟨a,ha⟩
  rcases harith T haT hh with he | he
  · left
    exact B.ncard_le_one_iff_subsingleton.mp (by change Nat.card B ≤ 1; omega)
  · right
    exact B.eq_univ_iff_ncard.mpr (by change Nat.card B = Nat.card X; omega)

end Matrix.PSp4Three.Blocks
end

noncomputable section
namespace Matrix.PSp4Three.Blocks
open MulAction
open scoped BigOperators

/-- There are only four suborbit sums containing a singleton base orbit. -/
theorem rankThree_suborbit_sum_cases (d : Fin 3 → ℕ) (h0 : d 0=1)
    (T : Finset (Fin 3)) (hT : 0 ∈ T) :
    (∑ i ∈ T,d i)=1 ∨ (∑ i ∈ T,d i)=1+d 1 ∨
      (∑ i ∈ T,d i)=1+d 2 ∨ (∑ i ∈ T,d i)=1+d 1+d 2 := by
  classical
  have he : (∑ i ∈ T,d i)=∑ i : Fin 3,if i ∈ T then d i else 0 := by simp
  rw [he,Fin.sum_univ_three]
  by_cases h1 : (1 : Fin 3) ∈ T <;> by_cases h2 : (2 : Fin 3) ∈ T <;>
    simp [hT,h1,h2,h0]

/-- Every block through a point in a three-suborbit action has one of these
four sizes, by the already proved general suborbit partition theorem. -/
theorem block_card_rankThree {G X : Type*} [Group G] [MulAction G X]
    [Finite X] (a : X) (f : X → Fin 3) (ha : f a=0)
    (htrans : ∀ x y, f x=f y → ∃ g : stabilizer G a, g • x=y)
    (d : Fin 3 → ℕ) (h0 : d 0=1)
    (hd : ∀ i, Nat.card {x : X // f x=i}=d i)
    (B : Set X) (haB : a ∈ B) (hB : IsBlock G B) :
    Nat.card B=1 ∨ Nat.card B=1+d 1 ∨ Nat.card B=1+d 2 ∨
      Nat.card B=1+d 1+d 2 := by
  obtain ⟨T,hT,hcard⟩ := block_card_suborbit_sum a f htrans d hd B haB hB
  rw [ha] at hT
  rw [hcard]
  exact rankThree_suborbit_sum_cases d h0 T hT

/-- Exact full suborbits of sizes 1,a,b imply primitivity when the two
proper nonsingleton sums fail the block-size divisibility test. -/
theorem primitive_of_rankThree_nondivisibility {G X : Type*}
    [Group G] [MulAction G X] [Finite X] [IsPretransitive G X]
    (a : X) (f : X → Fin 3) (ha : f a=0)
    (htrans : ∀ x y, f x=f y → ∃ g : stabilizer G a, g • x=y)
    (d : Fin 3 → ℕ) (h0 : d 0=1)
    (hd : ∀ i, Nat.card {x : X // f x=i}=d i)
    (hcard : Nat.card X=1+d 1+d 2)
    (hfirst : ¬(1+d 1) ∣ Nat.card X) (hsecond : ¬(1+d 2) ∣ Nat.card X) :
    IsPreprimitive G X := by
  apply primitive_of_suborbit_sums a f htrans d hd
  intro T hT hdiv
  rw [ha] at hT
  rcases rankThree_suborbit_sum_cases d h0 T hT with h | h | h | h
  · exact Or.inl h
  · exact False.elim (hfirst (h ▸ hdiv))
  · exact False.elim (hsecond (h ▸ hdiv))
  · exact Or.inr (h.trans hcard.symm)

end Matrix.PSp4Three.Blocks
end

namespace Matrix.PSp4Three

/-- The 40-point action has suborbits 1, 12, 27; neither 13 nor 28 divides 40. -/
theorem projective_preprimitive_three :
    MulAction.IsPreprimitive (PSp 2 (ZMod 3)) (Points 2 (ZMod 3)) := by
  classical
  let p : Points 2 (ZMod 3) := ePoint 0
  have hcard : Nat.card (Points 2 (ZMod 3)) = 40 := by
    rw [card_points]
    norm_num
  have hperp : Nat.card {q : Points 2 (ZMod 3) // Orthogonal p q} = 13 := by
    rw [card_perpendicular_points]
    norm_num
  apply Blocks.primitive_of_rankThree_nondivisibility p (suborbitIndex p)
    (suborbitIndex_self p) (fun x y h => suborbitIndex_transitive (by decide) p x y h)
    ![1,12,27] rfl
  · intro i
    fin_cases i
    · exact card_suborbit_zero p
    · simp [card_suborbit_one, hperp]
    · simp [card_suborbit_two, hperp, hcard]
  · exact hcard
  · rw [hcard]
    decide
  · rw [hcard]
    decide

end Matrix.PSp4Three
