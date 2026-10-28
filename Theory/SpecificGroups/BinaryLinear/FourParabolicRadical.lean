module

public import Theory.SpecificGroups.BinaryLinear.SmallParabolicLevi.Models
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Abel

/-!
# The sixteen-element radical of the middle parabolic in GL₄(2)

The stabilizer of the first summand of F₂² ⊕ F₂² is the parabolic whose
Levi nodes are the two end nodes of A₃. Its radical is the additive group
of two-by-two matrices acting by (u,v) ↦ (u+Av,v). Elementary row and
column operations extract every matrix unit from a nonzero invariant
subgroup, proving irreducibility of conjugation by the full parabolic.
The existing block-action theorem identifies this radical with the actual
two-core. A coordinate change and the canonical binary projective comparison
identify the ambient linear group with PSL₄(2).

Source: Aschbacher--Smith, combined manuscript (1 March 2004), final
paragraph of the proof of 15.3.35, printed p.1139. This module proves the
model calculation, not recognition of an arbitrary local subgroup.
-/

@[expose] public section

open Subgroup Matrix
namespace BinaryLinear.FourParabolicRadical
abbrev F := ZMod 2
abbrev Vec := Fin 2 → F
abbrev Mat := Matrix (Fin 2) (Fin 2) F
abbrev Space := Vec × Vec
abbrev Lin := BinaryLinear.GL Space

/-- The marked two-space whose stabilizer is the end-node parabolic. -/
def plane : Submodule F Space := LinearMap.ker (LinearMap.snd F Vec Vec)

/-- An upper block-unipotent linear automorphism. -/
def shear (A : Mat) : Lin where
  toFun v := (v.1 + A.mulVec v.2, v.2)
  invFun v := (v.1 - A.mulVec v.2, v.2)
  left_inv v := by simp
  right_inv v := by simp
  map_add' v w := by simp [mulVec_add, add_add_add_comm]
  map_smul' a v := by simp [mulVec_smul, smul_add]

/-- The actual upper block-unipotent embedding. -/
def upper : Multiplicative Mat →* Lin where
  toFun A := shear A.toAdd
  map_one' := by ext v i <;> simp [shear]
  map_mul' A B := by
    apply LinearEquiv.ext
    intro v
    apply Prod.ext
    · change v.1 + (A.toAdd + B.toAdd).mulVec v.2 =
        (v.1 + B.toAdd.mulVec v.2) + A.toAdd.mulVec v.2
      rw [add_mulVec]
      abel
    · rfl

theorem upper_injective : Function.Injective upper := by
  intro A B h
  apply Multiplicative.toAdd.injective
  ext i j
  have hh := congrArg (fun g : Lin => (g (0, Pi.single j 1)).1 i) h
  simpa [upper, shear, mulVec_single] using hh

/-- The upper block group is exactly the geometric radical. -/
theorem range_upper : upper.range = BinaryLinear.radical plane := by
  apply le_antisymm
  · rintro _ ⟨A, rfl⟩
    constructor
    · intro v hv
      change v.2 = 0 at hv
      apply Prod.ext <;> simp [upper, shear, hv]
    · intro v
      change v.2 - v.2 = 0
      exact sub_self _
  · intro g hg
    let f : Vec →ₗ[F] Vec := (LinearMap.fst F Vec Vec).comp
      (g.toLinearMap.comp (LinearMap.inr F Vec Vec))
    refine ⟨Multiplicative.ofAdd (LinearMap.toMatrix' f), ?_⟩
    apply LinearEquiv.ext
    intro v
    have hfix := hg.1 (v.1, 0) (by simp [plane])
    have hdiff := hg.2 (0, v.2)
    change (g (0, v.2)).2 - (0, v.2).2 = 0 at hdiff
    have hsum := g.map_add (v.1, 0) (0, v.2)
    rw [hfix] at hsum
    simp only [Prod.mk_add_mk, add_zero, zero_add] at hsum
    rw [hsum]
    change (v.1 + (LinearMap.toMatrix' f).mulVec v.2, v.2) = _
    rw [LinearMap.toMatrix'_mulVec]
    refine Prod.ext rfl ?_
    simpa using (sub_eq_zero.mp hdiff).symm

/-- The radical has sixteen elements. -/
theorem card_radical : Nat.card (BinaryLinear.radical plane) = 16 := by
  rw [← range_upper, ← Nat.card_congr (MonoidHom.ofInjective upper_injective).toEquiv]
  rw [Nat.card_congr Multiplicative.toAdd]
  simp [Mat, Matrix]

private def diagonal (a b : BinaryLinear.GL Vec) : Lin := a.prodCongr b

private theorem diagonal_mem (a b : BinaryLinear.GL Vec) :
    diagonal a b ∈ BinaryLinear.parabolic plane := by
  intro v
  change b v.2 = 0 ↔ v.2 = 0
  exact b.map_eq_zero_iff

private theorem conjugate_upper (a b : BinaryLinear.GL Vec) (A : Mat) :
    diagonal a b * upper (Multiplicative.ofAdd A) * (diagonal a b)⁻¹ =
      upper (Multiplicative.ofAdd (LinearMap.toMatrix'
        (a.toLinearMap.comp ((Matrix.toLin' A).comp b.symm.toLinearMap)))) := by
  apply LinearEquiv.ext
  intro v
  apply Prod.ext
  · simp [diagonal, upper, shear, LinearMap.toMatrix'_mulVec, map_add]
  · simp [diagonal, upper, shear]

private theorem binary_add_self (a : F) : a + a = 0 := (by decide : ∀ x : F, x + x = 0) a

private theorem binary_cancel (a b : F) : a + b + a = b := by
  rw [add_right_comm, binary_add_self, zero_add]

private theorem rev_ne (i : Fin 2) : i.rev ≠ i := by fin_cases i <;> decide

private def elementary (i : Fin 2) : BinaryLinear.GL Vec :=
  BinaryLinear.transvection (Pi.single i.rev 1) (LinearMap.proj i)
    (by simp [LinearMap.proj_apply, Ne.symm (rev_ne i)])

private theorem elementary_apply (i : Fin 2) (v : Vec) (r : Fin 2) :
    elementary i v r = v r + if r = i.rev then v i else 0 := by
  simp [elementary, BinaryLinear.transvection, Pi.single_apply]

private theorem elementary_inv (i : Fin 2) : (elementary i)⁻¹ = elementary i := by
  apply LinearEquiv.ext
  intro v
  rfl

private def rowExtract (i : Fin 2) (A : Mat) : Mat := fun r c => if r = i.rev then A i c else 0

private def colExtract (j : Fin 2) (A : Mat) : Mat := fun r c => if c = j.rev then A r j else 0

private theorem row_identity (i : Fin 2) (A : Mat) :
    LinearMap.toMatrix' ((elementary i).toLinearMap.comp (Matrix.toLin' A)) + A =
      rowExtract i A := by
  ext r c
  simp only [Matrix.add_apply, LinearMap.toMatrix'_apply, LinearMap.comp_apply,
    LinearEquiv.coe_coe, Matrix.toLin'_apply, elementary_apply, rowExtract]
  simp only [mulVec_single, MulOpposite.op_one, one_smul]
  split_ifs <;> simp [binary_cancel, binary_add_self]

private theorem col_identity (j : Fin 2) (A : Mat) :
    LinearMap.toMatrix' ((Matrix.toLin' A).comp (elementary j).toLinearMap) + A =
      colExtract j.rev A := by
  ext r c
  simp only [Matrix.add_apply, LinearMap.toMatrix'_apply, LinearMap.comp_apply,
    LinearEquiv.coe_coe, Matrix.toLin'_apply, colExtract]
  change (A.mulVec (elementary j (Pi.single c 1))) r + A r c = _
  have he : elementary j (Pi.single c 1) = Pi.single c 1 +
      (if j = c then Pi.single j.rev 1 else 0) := by
    ext k
    simp [elementary_apply, Pi.single_apply]
    split_ifs <;> simp_all
  rw [he, mulVec_add]
  simp only [Pi.add_apply, mulVec_single, MulOpposite.op_one, one_smul, Fin.rev_rev]
  by_cases h : j = c
  · subst c
    simp [binary_add_self, add_right_comm]
  · simp [h, Ne.symm h, binary_add_self]


private theorem extraction_closed (H : AddSubgroup Mat)
    (hleft : ∀ a : BinaryLinear.GL Vec, ∀ A ∈ H,
      LinearMap.toMatrix' (a.toLinearMap.comp (Matrix.toLin' A)) ∈ H)
    (hright : ∀ b : BinaryLinear.GL Vec, ∀ A ∈ H,
      LinearMap.toMatrix' ((Matrix.toLin' A).comp b.toLinearMap) ∈ H)
    (A : Mat) (hA : A ∈ H) (i j : Fin 2) :
    rowExtract i A ∈ H ∧ colExtract j A ∈ H := by
  constructor
  · rw [← row_identity]
    exact H.add_mem (hleft (elementary i) A hA) hA
  · rw [← Fin.rev_rev j, ← col_identity]
    exact H.add_mem (hright (elementary j.rev) A hA) hA

private def unitMatrix (i j : Fin 2) : Mat := fun r c => if r = i ∧ c = j then 1 else 0

private theorem invariant_matrices (H : AddSubgroup Mat)
    (hleft : ∀ a : BinaryLinear.GL Vec, ∀ A ∈ H,
      LinearMap.toMatrix' (a.toLinearMap.comp (Matrix.toLin' A)) ∈ H)
    (hright : ∀ b : BinaryLinear.GL Vec, ∀ A ∈ H,
      LinearMap.toMatrix' ((Matrix.toLin' A).comp b.toLinearMap) ∈ H) :
    H = ⊥ ∨ H = ⊤ := by
  classical
  by_cases hH : H = ⊥
  · exact Or.inl hH
  right
  have hexA : ∃ A ∈ H, A ≠ 0 := by
    by_contra! hz
    apply hH
    apply le_antisymm
    · intro x hx
      exact hz x hx
    · exact bot_le
  obtain ⟨A, hA, hA0⟩ := hexA
  have hex : ∃ i j, A i j ≠ 0 := by
    by_contra! h
    exact hA0 (by ext i j; exact h i j)
  obtain ⟨i, j, hij⟩ := hex
  have ha1 : A i j = 1 := (by decide : ∀ x : F, x ≠ 0 → x = 1) _ hij
  have hseed : unitMatrix i.rev j.rev ∈ H := by
    have hh := (extraction_closed H hleft hright _
      ((extraction_closed H hleft hright A hA i j).1) i j).2
    convert hh using 1
    ext r c
    simp only [unitMatrix, colExtract, rowExtract, ha1]
    split_ifs <;> simp_all
  have row_move {a b : Fin 2} (h : unitMatrix a b ∈ H) : unitMatrix a.rev b ∈ H := by
    have hh := (extraction_closed H hleft hright _ h a b).1
    convert hh using 1
    ext r c
    simp only [unitMatrix, rowExtract]
    split_ifs <;> simp_all
  have col_move {a b : Fin 2} (h : unitMatrix a b ∈ H) : unitMatrix a b.rev ∈ H := by
    have hh := (extraction_closed H hleft hright _ h a b).2
    convert hh using 1
    ext r c
    simp only [unitMatrix, colExtract]
    split_ifs <;> simp_all
  have hall (a b : Fin 2) : unitMatrix a b ∈ H := by
    have hr := row_move hseed
    have hc := col_move hseed
    have hrc := col_move hr
    fin_cases i <;> fin_cases j <;> fin_cases a <;> fin_cases b <;>
      first | exact hseed | exact hr | exact hc | exact hrc
  apply top_unique
  intro B _
  have hterm (a b : Fin 2) : (if B a b = 1 then unitMatrix a b else 0) ∈ H := by
    split_ifs
    · exact hall a b
    · exact H.zero_mem
  have heq : B = ∑ a : Fin 2, ∑ b : Fin 2,
      if B a b = 1 then unitMatrix a b else 0 := by
    exact (by decide : ∀ C : Mat, C = ∑ a : Fin 2, ∑ b : Fin 2,
      if C a b = 1 then unitMatrix a b else 0) B
  rw [heq]
  exact H.sum_mem fun a _ => H.sum_mem fun b _ => hterm a b


/-- Conjugation by the parabolic has no nonzero proper invariant subgroup. -/
theorem radical_irreducible (W : Subgroup Lin) (hW : W ≤ BinaryLinear.radical plane)
    (hN : BinaryLinear.parabolic plane ≤ normalizer (W : Set Lin)) :
    W = ⊥ ∨ W = BinaryLinear.radical plane := by
  let H : AddSubgroup Mat :=
    { carrier := {A | upper (Multiplicative.ofAdd A) ∈ W}
      zero_mem' := by
        change upper 1 ∈ W
        rw [map_one]
        exact W.one_mem
      add_mem' := by
        intro A B hA hB
        change upper (Multiplicative.ofAdd A * Multiplicative.ofAdd B) ∈ W
        rw [map_mul]
        exact W.mul_mem hA hB
      neg_mem' := by
        intro A hA
        change upper (Multiplicative.ofAdd A)⁻¹ ∈ W
        rw [map_inv]
        exact W.inv_mem hA }
  have hc (a b : BinaryLinear.GL Vec) (A : Mat) (hA : A ∈ H) :
      LinearMap.toMatrix' (a.toLinearMap.comp
        ((Matrix.toLin' A).comp b.symm.toLinearMap)) ∈ H := by
    have hh := le_set_normalizer_iff.mp hN (diagonal a b) (diagonal_mem a b)
      (upper (Multiplicative.ofAdd A)) hA
    rw [conjugate_upper] at hh
    exact hh
  have hl (a : BinaryLinear.GL Vec) (A : Mat) (hA : A ∈ H) :
      LinearMap.toMatrix' (a.toLinearMap.comp (Matrix.toLin' A)) ∈ H := by
    have hh := hc a 1 A hA
    change LinearMap.toMatrix' (a.toLinearMap.comp
      ((Matrix.toLin' A).comp LinearMap.id)) ∈ H at hh
    simpa only [LinearMap.comp_id] using hh
  have hr (b : BinaryLinear.GL Vec) (A : Mat) (hA : A ∈ H) :
      LinearMap.toMatrix' ((Matrix.toLin' A).comp b.toLinearMap) ∈ H := by
    have hh := hc 1 b.symm A hA
    rw [LinearEquiv.symm_symm] at hh
    change LinearMap.toMatrix' (LinearMap.id.comp
      ((Matrix.toLin' A).comp b.toLinearMap)) ∈ H at hh
    simpa only [LinearMap.id_comp] using hh
  rcases invariant_matrices H hl hr with hz | ht
  · left
    apply bot_unique
    intro g hg
    obtain ⟨A, rfl⟩ := (show g ∈ upper.range from range_upper.symm ▸ hW hg)
    have ha : A.toAdd ∈ H := hg
    have ha0 : A.toAdd = 0 := by simpa only [hz, AddSubgroup.mem_bot] using ha
    have ha1 : A = 1 := Multiplicative.toAdd.injective ha0
    simp [ha1]
  · right
    apply le_antisymm hW
    intro g hg
    obtain ⟨A, rfl⟩ := (show g ∈ upper.range from range_upper.symm ▸ hg)
    exact (show A.toAdd ∈ H from ht ▸ AddSubgroup.mem_top _)


def spaceEquiv : Space ≃ₗ[F] (Fin 4 → F) where
  toFun v := ![v.1 0, v.1 1, v.2 0, v.2 1]
  invFun v := (![v 0, v 1], ![v 2, v 3])
  left_inv v := by
    apply Prod.ext <;> ext i <;> fin_cases i <;> rfl
  right_inv v := by ext i; fin_cases i <;> rfl
  map_add' v w := by ext i; fin_cases i <;> rfl
  map_smul' a v := by ext i; fin_cases i <;> rfl

/-- Canonical comparison with PSL₄(2), through its usual natural action. -/
noncomputable def projectiveEquiv :
    Matrix.ProjectiveSpecialLinearGroup (Fin 4) F ≃* Lin :=
  (BinaryLinear.OuterCyclic.projectiveEquivLinear (by decide : 0 < 4)).trans
    (BinaryLinear.SmallParabolicLevi.linearGroupCongr spaceEquiv.symm)

/-- The computed radical is the image of the intrinsic two-core. -/
theorem twoCore_eq_radical :
    (pCore 2 (BinaryLinear.parabolic plane)).map (BinaryLinear.parabolic plane).subtype =
      BinaryLinear.radical plane :=
  BinaryLinear.SmallParabolicLevi.map_twoCore_eq_radical plane

end BinaryLinear.FourParabolicRadical



