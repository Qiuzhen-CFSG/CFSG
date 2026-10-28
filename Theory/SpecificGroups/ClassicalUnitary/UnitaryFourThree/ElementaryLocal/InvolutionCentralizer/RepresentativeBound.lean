module

public import Theory.SpecificGroups.ClassicalUnitary.UnitaryFourThree.Model
public import Theory.SpecificGroups.ClassicalUnitary.UnitaryFourThree.TwoLocal.StandardInvolution
public import Theory.SpecificGroups.ClassicalUnitary.UnitaryFourThree.ElementaryLocal.InvolutionCentralizer.RepresentativeBound.UnitaryTwo
public import Mathlib.GroupTheory.Coset.Card
/-!
# The three-part of the standard projective involution centralizer

The full inverse image in SU₄(3) of the centralizer of the projective image
of diag(-1,-1,1,1) embeds into the group of unitary matrices which commute
or anticommute with this diagonal matrix. Such a matrix either preserves
the two coordinate planes or interchanges them. The two cases are disjoint,
and each is parametrized by two independent GU₂(3) matrices. Consequently
this overgroup has order `2 * 96² = 18432`.

The actual SU-to-PSU projection surjects from the full inverse image to the
centralizer. Lagrange's theorem and the order formula for a homomorphic
image therefore show that the centralizer order divides 18432, excluding
27. No injectivity of the projective map is asserted: its scalar kernel is
retained, and the anticommuting lifts are included throughout.

This supplies the standard-representative calculation used in the PSU₄(3)
case of Aschbacher–Smith, Theorem 0.1.2(4), printed p.4, restated as 0.1.1(4)
on p.482 of `refs/quasithin.pdf`. Unitary and projective conventions follow
GLS3, chapter 2, §2.7 (`refs/KGroup/GLS3/chapter2.tex`). Transport to arbitrary
involutions belongs to the separate involution-centralizer assembly.
-/

open Matrix BenderSuzuki.MatrixGroups
open Theory.SpecificGroups.ClassicalUnitary.UnitaryFourThree
namespace Theory.SpecificGroups.ClassicalUnitary.UnitaryFourThree.TwoLocal
private abbrev M (n : ℕ) := Matrix (Fin n) (Fin n) FiniteField.Nine
private abbrev U (n : ℕ) := Matrix.unitaryGroup (Fin n) FiniteField.Nine
private abbrev D := standardInvolutionMatrix
private theorem star_D : star D = D := by decide

private def signed : Subgroup (U 4) where
  carrier := {g | g.val * D = D * g.val ∨ g.val * D = -(D * g.val)}
  one_mem' := by left; simp
  mul_mem' := by
    intro a b ha hb
    change (a.val * b.val) * D = D * (a.val * b.val) ∨
      (a.val * b.val) * D = -(D * (a.val * b.val))
    rcases ha with ha | ha <;> rcases hb with hb | hb
    · left; rw [mul_assoc, hb, ← mul_assoc, ha, mul_assoc]
    · right; rw [mul_assoc, hb, mul_neg, ← mul_assoc, ha, mul_assoc]
    · right; rw [mul_assoc, hb, ← mul_assoc, ha, neg_mul, mul_assoc]
    · left; rw [mul_assoc, hb, mul_neg, ← mul_assoc, ha, neg_mul, neg_neg, mul_assoc]
  inv_mem' := by
    intro a ha
    change star a.val * D = D * star a.val ∨ star a.val * D = -(D * star a.val)
    rcases ha with ha | ha
    · left
      simpa only [star_mul, star_D] using (congrArg star ha).symm
    · right
      have h := congrArg star ha
      simp only [star_mul, star_D, star_neg] at h
      rw [h, neg_neg]

private def block (A B : M 2) : M 4 :=
  !![A 0 0, A 0 1, 0, 0; A 1 0, A 1 1, 0, 0;
     0, 0, B 0 0, B 0 1; 0, 0, B 1 0, B 1 1]
private def swap : M 4 := !![0,0,1,0; 0,0,0,1; 1,0,0,0; 0,1,0,0]
private theorem swap_sq : swap * swap = 1 := by decide
private theorem star_swap : star swap = swap := by decide
private theorem swap_anti : swap * D = -(D * swap) := by decide

private theorem block_star (A B : M 2) : star (block A B) = block (star A) (star B) := by
  apply Matrix.ext; intro i j
  fin_cases i <;> fin_cases j <;> simp [block, Matrix.star_apply]
private theorem block_mul (A B C E : M 2) :
    block A B * block C E = block (A * C) (B * E) := by
  apply Matrix.ext; intro i j
  fin_cases i <;> fin_cases j <;> simp [block, Matrix.mul_apply, Fin.sum_univ_succ]
private theorem block_one : block 1 1 = 1 := by decide

private def top (A : M 4) : M 2 := fun i j => A (Fin.castAdd 2 i) (Fin.castAdd 2 j)
private def bot (A : M 4) : M 2 := fun i j => A (Fin.natAdd 2 i) (Fin.natAdd 2 j)

private theorem top_block (A B : M 2) : top (block A B) = A := by
  apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> rfl
private theorem bot_block (A B : M 2) : bot (block A B) = B := by
  apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> rfl

private theorem commute_shape (A : M 4) (h : A * D = D * A) : A = block (top A) (bot A) := by
  have hneg (x : FiniteField.Nine) : -x = x ↔ x = 0 := by revert x; decide
  have hneg' (x : FiniteField.Nine) : x = -x ↔ x = 0 := by revert x; decide
  have hh (i j : Fin 4) := congrArg (fun B : M 4 => B i j) h
  simp only [D, standardInvolutionMatrix, Matrix.mul_diagonal, Matrix.diagonal_mul] at hh
  apply Matrix.ext; intro i j
  have hij := hh i j
  fin_cases i <;> fin_cases j <;>
    first | rfl | simpa [block, top, bot, hneg, hneg'] using hij


private theorem block_commute (A B : M 2) : block A B * D = D * block A B := by
  apply Matrix.ext; intro i j
  fin_cases i <;> fin_cases j <;>
    simp [block, D, standardInvolutionMatrix, Matrix.mul_diagonal, Matrix.diagonal_mul]

private def blockUnitary (A B : U 2) : U 4 := ⟨block A.val B.val, by
  rw [Matrix.mem_unitaryGroup_iff', block_star, block_mul,
    Matrix.mem_unitaryGroup_iff'.mp A.property, Matrix.mem_unitaryGroup_iff'.mp B.property,
    block_one]⟩
private def swapUnitary : U 4 := ⟨swap, by rw [Matrix.mem_unitaryGroup_iff', star_swap, swap_sq]⟩

private theorem commute_exists (g : U 4) (h : g.val * D = D * g.val) :
    ∃ A B : U 2, g.val = block A.val B.val := by
  have hs := commute_shape g.val h
  have hu := Matrix.mem_unitaryGroup_iff'.mp g.property
  rw [hs, block_star, block_mul, ← block_one] at hu
  have hA : top g.val ∈ Matrix.unitaryGroup (Fin 2) FiniteField.Nine := by
    rw [Matrix.mem_unitaryGroup_iff']
    simpa only [top_block] using congrArg top hu
  have hB : bot g.val ∈ Matrix.unitaryGroup (Fin 2) FiniteField.Nine := by
    rw [Matrix.mem_unitaryGroup_iff']
    simpa only [bot_block] using congrArg bot hu
  exact ⟨⟨top g.val, hA⟩, ⟨bot g.val, hB⟩, hs⟩

private def param : (U 2 × U 2) ⊕ (U 2 × U 2) → signed
  | .inl (A,B) => ⟨blockUnitary A B, Or.inl (block_commute A.val B.val)⟩
  | .inr (A,B) => ⟨blockUnitary A B * swapUnitary, Or.inr (by
      change (block A.val B.val * swap) * D = -(D * (block A.val B.val * swap))
      rw [mul_assoc, swap_anti, mul_neg, ← mul_assoc, block_commute, mul_assoc])⟩

private theorem param_surjective : Function.Surjective param := by
  intro g
  rcases g.property with h | h
  · obtain ⟨A,B,he⟩ := commute_exists g.val h
    exact ⟨.inl (A,B), Subtype.ext (Subtype.ext he.symm)⟩
  · have hh : (g.val * swapUnitary).val * D = D * (g.val * swapUnitary).val := by
      change (g.val.val * swap) * D = D * (g.val.val * swap)
      rw [mul_assoc, swap_anti, mul_neg, ← mul_assoc, h, neg_mul, neg_neg, mul_assoc]
    obtain ⟨A,B,he⟩ := commute_exists (g.val * swapUnitary) hh
    refine ⟨.inr (A,B), Subtype.ext (Subtype.ext ?_)⟩
    change block A.val B.val * swap = g.val.val
    rw [← he]
    change (g.val.val * swap) * swap = g.val.val
    rw [mul_assoc, swap_sq, mul_one]

private theorem top_block_swap (A B : M 2) : top (block A B * swap) = 0 := by
  apply Matrix.ext; intro i j
  fin_cases i <;> fin_cases j <;>
    simp [top, block, swap, Matrix.mul_apply, Fin.sum_univ_succ]

private theorem block_injective {A B C E : U 2} (h : block A.val B.val = block C.val E.val) :
    (A,B) = (C,E) := by
  apply Prod.ext <;> apply Subtype.ext
  · simpa only [top_block] using congrArg top h
  · simpa only [bot_block] using congrArg bot h

private theorem block_ne_block_swap (A B C E : U 2) : block A.val B.val ≠ block C.val E.val * swap := by
  intro h
  have hz : A.val = 0 := by simpa only [top_block, top_block_swap] using congrArg top h
  have hu := Matrix.mem_unitaryGroup_iff'.mp A.property
  rw [hz, mul_zero] at hu
  exact zero_ne_one hu

private theorem param_injective : Function.Injective param := by
  intro x y h
  have hm := congrArg (fun g : signed => g.val.val) h
  rcases x with ⟨A,B⟩ | ⟨A,B⟩ <;> rcases y with ⟨C,E⟩ | ⟨C,E⟩
  · exact congrArg Sum.inl (block_injective hm)
  · exact False.elim (block_ne_block_swap A B C E hm)
  · exact False.elim (block_ne_block_swap C E A B hm.symm)
  · apply congrArg Sum.inr
    apply block_injective
    have hh := congrArg (fun M : M 4 => M * swap) hm
    change (block A.val B.val * swap) * swap = (block C.val E.val * swap) * swap at hh
    simpa only [mul_assoc, swap_sq, mul_one] using hh


private theorem signed_card : Nat.card signed = 18432 := by
  rw [← Nat.card_congr (Equiv.ofBijective param ⟨param_injective, param_surjective⟩),
    Nat.card_sum, Nat.card_prod, RepresentativeBound.unitaryTwo_card]


private abbrev lifted := standardCentralizer.comap (project 4)

private def liftEmbedding : lifted →* signed where
  toFun g := ⟨⟨g.val.val.val, by
    rw [Matrix.mem_unitaryGroup_iff']
    have h := ((form 4).mem_specialSubgroup_iff g.val.val).mp g.val.property |>.1
    change star g.val.val.val * 1 * g.val.val.val = 1 at h
    simpa only [mul_one] using h⟩,
    (project_mem_standardCentralizer_iff g.val).mp g.property⟩
  map_one' := by apply Subtype.ext; apply Subtype.ext; rfl
  map_mul' _ _ := by apply Subtype.ext; apply Subtype.ext; rfl

private theorem liftEmbedding_injective : Function.Injective liftEmbedding := by
  intro g h he
  apply Subtype.ext
  apply Subtype.ext
  apply Units.ext
  exact congrArg (fun u : signed => u.val.val) he

private def projectCentralizer : lifted →* standardCentralizer :=
  ((project 4).comp lifted.subtype).codRestrict _ (fun a => a.property)

private theorem projectCentralizer_surjective : Function.Surjective projectCentralizer := by
  intro g
  obtain ⟨a,ha⟩ := project_surjective 4 g.val
  refine ⟨⟨a, ?_⟩, ?_⟩
  · change project 4 a ∈ standardCentralizer
    rw [ha]
    exact g.property
  · exact Subtype.ext ha

/-- The full projective centralizer order divides the order of the unitary block overgroup. -/
public theorem standardCentralizer_card_dvd : Nat.card standardCentralizer ∣ 18432 := by
  calc
    Nat.card standardCentralizer ∣ Nat.card lifted :=
      Subgroup.card_dvd_of_surjective projectCentralizer projectCentralizer_surjective
    _ ∣ Nat.card signed := Subgroup.card_dvd_of_injective liftEmbedding liftEmbedding_injective
    _ = 18432 := signed_card

/-- The actual standard involution centralizer in PSU₄(3) has three-part at most nine. -/
public theorem standardCentralizer_three_part : ¬ 3 ^ 3 ∣ Nat.card standardCentralizer := by
  intro h
  have hd := h.trans standardCentralizer_card_dvd
  norm_num at hd


end Theory.SpecificGroups.ClassicalUnitary.UnitaryFourThree.TwoLocal
