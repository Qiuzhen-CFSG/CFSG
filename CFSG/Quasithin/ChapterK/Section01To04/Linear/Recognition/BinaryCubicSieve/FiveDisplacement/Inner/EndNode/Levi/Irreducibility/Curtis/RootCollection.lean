module
public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Recognition.BinaryCubicSieve.FiveDisplacement.Inner.EndNode.Levi.Irreducibility.GeometryData
public import Theory.Representation.SLHigherNaturalFirstCohomology.Elementary

/-!
# Root collection for the binary Curtis argument

For a chosen simple root, collect its transvection to the right of the
positive unipotent subgroup. The other positive roots form a subgroup
normalized by that transvection and carried into the positive subgroup by
the adjacent coordinate exchange. Inverse transpose gives the literal
opposite collection. The lower roots and exchanges generate SL₅(2).

The matrix calculations use single-matrix multiplication and the natural
action of a coordinate exchange; they require no enumeration of SL₅(2).
This is the group-theoretic input to opposite-unipotent cyclicity in GLS,
Volume 3, Theorem 2.8.9, `refs/KGroup/GLS3/chapter2.tex`, printed p.94.
-/

public section

namespace CFSG.Quasithin.ChapterK.Linear.Recognition.BinaryCubicSieve.FiveDisplacement.Inner.EndNode.Levi.Irreducibility.Curtis
open Representation Representation.SL5TenDimensional Representation.SL5TenDimensional.Classification
open HeckeAction BinaryLinear.OuterCyclic

private def positive (a b : Fin 5) : SL5TenDimensional.Group :=
  if h : a < b then Matrix.SpecialLinearGroup.transvection (ne_of_lt h) (1 : ZMod 2)
  else 1

private def omitted (i : Fin 4) : Subgroup SL5TenDimensional.Group :=
  Subgroup.closure {g | ∃ a b : Fin 5, a < b ∧
    ¬ (a = i.castSucc ∧ b = i.succ) ∧ g = positive a b}

private theorem positive_mem (a b : Fin 5) : positive a b ∈ upper := by
  unfold positive
  split_ifs with h
  · exact Subgroup.subset_closure ⟨a, b, h, rfl⟩
  · exact upper.one_mem

private theorem positive_mem_omitted (i : Fin 4) (a b : Fin 5)
    (h : ¬ (a = i.castSucc ∧ b = i.succ)) : positive a b ∈ omitted i := by
  by_cases hab : a < b
  · exact Subgroup.subset_closure ⟨a, b, hab, h, rfl⟩
  · simp only [positive, dif_neg hab]; exact (omitted i).one_mem

private theorem omitted_le (i : Fin 4) : omitted i ≤ upper := by
  apply (Subgroup.closure_le _).mpr
  rintro _ ⟨a,b,_,_,rfl⟩
  exact positive_mem a b

private theorem simpleUpper_sq (i : Fin 4) : simpleUpper i * simpleUpper i = 1 := by
  simpa only [simpleUpper, ← Matrix.SpecialLinearGroup.transvection_add,
    show (1 : ZMod 2) + 1 = 0 by decide] using
    Matrix.SpecialLinearGroup.transvection_coeff_zero (F := ZMod 2)
      (i := i.castSucc) (j := i.succ) (ne_of_lt (by simp))

private theorem conjugate_positive (i : Fin 4) (a b : Fin 5) (hab : a < b) :
    simpleUpper i * positive a b * simpleUpper i =
      positive a b * ((if b = i.castSucc then positive a i.succ else 1) *
        (if a = i.succ then positive i.castSucc b else 1)) := by
  have hi : i.castSucc < i.succ := by simp
  by_cases hb : b = i.castSucc
  · subst b
    have ha : a ≠ i.succ := ne_of_lt (hab.trans hi)
    apply Subtype.ext
    simp only [simpleUpper, positive, hab, ↓reduceDIte, Matrix.SpecialLinearGroup.coe_mul,
      Matrix.SpecialLinearGroup.transvection_coe, add_comm, mul_add, add_mul, ne_eq,
      Ne.symm ha, not_false_eq_true, Matrix.single_mul_single_of_ne, one_mul, add_zero,
      mul_one, Matrix.single_mul_single_same, hi.ne.symm, add_left_comm, add_assoc,
      ↓reduceIte, hab.trans hi, ha, hab.ne.symm, add_right_inj]
    ext r c
    exact CharTwo.add_cancel_left (R := ZMod 2) _ _
  · by_cases ha : a = i.succ
    · subst a
      have hc : i.castSucc < b := hi.trans hab
      apply Subtype.ext
      simp only [simpleUpper, positive, hab, ↓reduceDIte, Matrix.SpecialLinearGroup.coe_mul,
        Matrix.SpecialLinearGroup.transvection_coe, add_comm, mul_add, add_mul,
        Matrix.single_mul_single_same, mul_one, one_mul, add_left_comm, add_assoc,
        ne_eq, hb, not_false_eq_true, Matrix.single_mul_single_of_ne, hi.ne.symm,
        add_zero, ↓reduceIte, hc, add_right_inj]
      ext r c
      exact CharTwo.add_cancel_left (R := ZMod 2) _ _
    · apply Subtype.ext
      simp only [simpleUpper, positive, hab, ↓reduceDIte, Matrix.SpecialLinearGroup.coe_mul,
        Matrix.SpecialLinearGroup.transvection_coe, add_comm, mul_add, add_mul, ne_eq,
        Ne.symm ha, not_false_eq_true, Matrix.single_mul_single_of_ne, one_mul, add_zero,
        mul_one, hb, hi.ne.symm, add_left_comm, ↓reduceIte, ha, add_right_inj]
      ext r c
      exact CharTwo.add_cancel_left (R := ZMod 2) _ _


private theorem swap_mulVec (i : Fin 4) (v : Fin 5 → ZMod 2) :
    (simpleSwap i).val.mulVec v = v ∘ Equiv.swap i.castSucc i.succ := by
  simp only [simpleSwap, simpleLower, simpleUpper, Matrix.SpecialLinearGroup.coe_mul,
    Matrix.SpecialLinearGroup.transvection_coe, ← Matrix.mulVec_mulVec,
    Matrix.add_mulVec, Matrix.one_mulVec, Matrix.single_mulVec_eq]
  have hcancel (a b : ZMod 2) : a + (b + a) = b := by
    rw [add_comm b a, CharTwo.add_cancel_left]
  ext a
  fin_cases i <;> fin_cases a <;>
    simp [Equiv.swap_apply_def, hcancel, add_assoc]

private theorem swap_positive (i : Fin 4) (a b : Fin 5) (hab : a < b)
    (hne : ¬ (a = i.castSucc ∧ b = i.succ)) :
    simpleSwap i * positive a b * simpleSwap i =
      positive (Equiv.swap i.castSucc i.succ a) (Equiv.swap i.castSucc i.succ b) := by
  have hs : Equiv.swap i.castSucc i.succ a < Equiv.swap i.castSucc i.succ b := by
    revert i a b
    decide
  apply Subtype.ext
  apply Matrix.ext_of_mulVec_single
  intro j
  simp only [Matrix.SpecialLinearGroup.coe_mul, ← Matrix.mulVec_mulVec, swap_mulVec,
    positive, dif_pos hab, dif_pos hs, Matrix.SpecialLinearGroup.transvection_coe,
    Matrix.add_mulVec, Matrix.one_mulVec, Matrix.single_mulVec_eq]
  ext k
  simp only [Function.comp_apply, Pi.add_apply, Equiv.swap_apply_self, Pi.single_apply,
    one_mul, Equiv.swap_apply_eq_iff, Pi.smul_apply, Pi.single_apply]

private theorem upper_conjugate_omitted (i : Fin 4) {h : SL5TenDimensional.Group}
    (hh : h ∈ omitted i) : simpleUpper i * h * simpleUpper i ∈ omitted i := by
  have hi : (simpleUpper i)⁻¹ = simpleUpper i :=
    inv_eq_of_mul_eq_one_left (simpleUpper_sq i)
  have hn : omitted i ≤ (omitted i).comap (MulAut.conj (simpleUpper i)).toMonoidHom := by
    apply (Subgroup.closure_le _).mpr
    rintro _ ⟨a,b,hab,hne,rfl⟩
    change simpleUpper i * positive a b * (simpleUpper i)⁻¹ ∈ omitted i
    rw [hi, conjugate_positive i a b hab]
    apply (omitted i).mul_mem (positive_mem_omitted i a b hne)
    apply (omitted i).mul_mem
    · split_ifs with hb
      · apply positive_mem_omitted
        rintro ⟨ha,_⟩
        subst a; subst b
        exact lt_irrefl _ hab
      · exact (omitted i).one_mem
    · split_ifs with ha
      · apply positive_mem_omitted
        rintro ⟨_,hb⟩
        subst a; subst b
        exact lt_irrefl _ hab
      · exact (omitted i).one_mem
  have hm := hn hh
  change simpleUpper i * h * (simpleUpper i)⁻¹ ∈ omitted i at hm
  rwa [hi] at hm

private theorem swap_conjugate_omitted (i : Fin 4) {h : SL5TenDimensional.Group}
    (hh : h ∈ omitted i) : simpleSwap i * h * simpleSwap i ∈ upper := by
  have hi : (simpleSwap i)⁻¹ = simpleSwap i := inv_eq_of_mul_eq_one_left (swap_sq i)
  have hn : omitted i ≤ upper.comap (MulAut.conj (simpleSwap i)).toMonoidHom := by
    apply (Subgroup.closure_le _).mpr
    rintro _ ⟨a,b,hab,hne,rfl⟩
    change simpleSwap i * positive a b * (simpleSwap i)⁻¹ ∈ upper
    rw [hi, swap_positive i a b hab hne]
    exact positive_mem _ _
  have hm := hn hh
  change simpleSwap i * h * (simpleSwap i)⁻¹ ∈ upper at hm
  rwa [hi] at hm

/-- Separate a chosen simple root from the other positive roots. -/
theorem upper_collection (i : Fin 4) {u : SL5TenDimensional.Group} (hu : u ∈ upper) :
    ∃ h ∈ upper, simpleSwap i * h * simpleSwap i ∈ upper ∧
      (u = h ∨ u = h * simpleUpper i) := by
  have hc : ∃ h ∈ omitted i, u = h ∨ u = h * simpleUpper i := by
    have root (a b : Fin 5) (hab : a < b) :
        ∃ h ∈ omitted i, positive a b = h ∨ positive a b = h * simpleUpper i := by
      by_cases he : a = i.castSucc ∧ b = i.succ
      · refine ⟨1, (omitted i).one_mem, Or.inr ?_⟩
        obtain ⟨rfl,rfl⟩ := he
        simp only [one_mul, positive, dif_pos hab]
        rfl
      · exact ⟨positive a b, positive_mem_omitted i a b he, Or.inl rfl⟩
    induction hu using Subgroup.closure_induction'' with
    | mem g hg =>
      obtain ⟨a,b,hab,rfl⟩ := hg
      simpa only [positive, dif_pos hab] using root a b hab
    | inv_mem g hg =>
      obtain ⟨a,b,hab,rfl⟩ := hg
      rw [Matrix.SpecialLinearGroup.transvection_inv,
        show -(1 : ZMod 2) = 1 by decide]
      simpa only [positive, dif_pos hab] using root a b hab
    | one => exact ⟨1, (omitted i).one_mem, Or.inl rfl⟩
    | mul a b _ _ ha hb =>
      obtain ⟨x,hx,hax⟩ := ha
      obtain ⟨y,hy,hby⟩ := hb
      rcases hax with hax | hax <;> rcases hby with hby | hby <;> rw [hax, hby]
      · exact ⟨x*y, (omitted i).mul_mem hx hy, Or.inl rfl⟩
      · exact ⟨x*y, (omitted i).mul_mem hx hy, Or.inr (mul_assoc _ _ _).symm⟩
      · refine ⟨x * (simpleUpper i * y * simpleUpper i),
          (omitted i).mul_mem hx (upper_conjugate_omitted i hy), Or.inr ?_⟩
        simp only [mul_assoc, simpleUpper_sq, mul_one]
      · refine ⟨x * (simpleUpper i * y * simpleUpper i),
          (omitted i).mul_mem hx (upper_conjugate_omitted i hy), Or.inl ?_⟩
        simp only [mul_assoc]
  obtain ⟨h,hh,he⟩ := hc
  exact ⟨h, omitted_le i hh, swap_conjugate_omitted i hh, he⟩

/-- Inverse transpose is involutive on the literal binary matrix group. -/
theorem graph_involution (g : SL5TenDimensional.Group) : graphSL 5 (graphSL 5 g) = g :=
  (graphSL 5).symm_apply_apply g

/-- Inverse transpose exchanges the elementary positive and negative roots. -/
theorem graph_transvection (a b : Fin 5) (hab : a ≠ b) :
    graphSL 5 (Matrix.SpecialLinearGroup.transvection hab (1 : ZMod 2)) =
      Matrix.SpecialLinearGroup.transvection hab.symm (1 : ZMod 2) := by
  change (Matrix.SpecialLinearGroup.transpose
    (Matrix.SpecialLinearGroup.transvection hab (1 : ZMod 2)))⁻¹ = _
  have ht : Matrix.SpecialLinearGroup.transpose
      (Matrix.SpecialLinearGroup.transvection hab (1 : ZMod 2)) =
      Matrix.SpecialLinearGroup.transvection hab.symm (1 : ZMod 2) := by
    apply Subtype.ext
    simp [Matrix.SpecialLinearGroup.transpose, Matrix.SpecialLinearGroup.transvection_coe,
      Matrix.transpose_add, Matrix.transpose_single]
  rw [ht, Matrix.SpecialLinearGroup.transvection_inv]
  rfl

theorem graph_simpleUpper (i : Fin 4) : graphSL 5 (simpleUpper i) = simpleLower i :=
  graph_transvection _ _ _

theorem graph_simpleSwap (i : Fin 4) : graphSL 5 (simpleSwap i) = simpleSwap i := by
  have hl : graphSL 5 (simpleLower i) = simpleUpper i := graph_transvection _ _ _
  change graphSL 5 (simpleLower i * simpleUpper i * simpleLower i) = simpleSwap i
  rw [map_mul, map_mul, hl, graph_simpleUpper, mul_assoc]
  exact upper_lower_upper i

theorem simpleLower_mem (i : Fin 4) : simpleLower i ∈ lower := by
  rw [← graph_simpleUpper]
  apply Subgroup.mem_map_of_mem
  exact Subgroup.subset_closure ⟨i.castSucc, i.succ, by simp, rfl⟩

/-- The opposite root collection, on the literal graph image. -/
theorem lower_collection (i : Fin 4) {u : SL5TenDimensional.Group} (hu : u ∈ lower) :
    ∃ h ∈ lower, simpleSwap i * h * simpleSwap i ∈ lower ∧
      (u = h ∨ u = h * simpleLower i) := by
  obtain ⟨v,hv,rfl⟩ := hu
  obtain ⟨h,hh,hs,he⟩ := upper_collection i hv
  refine ⟨graphSL 5 h, Subgroup.mem_map_of_mem _ hh, ?_, ?_⟩
  · have hm := Subgroup.mem_map_of_mem (graphSL 5).toMonoidHom hs
    change graphSL 5 (simpleSwap i * h * simpleSwap i) ∈ lower at hm
    simpa only [map_mul, graph_simpleSwap] using hm
  · rcases he with rfl | rfl
    · exact Or.inl rfl
    · right
      change graphSL 5 (h * simpleUpper i) = _
      rw [map_mul, graph_simpleUpper]

end CFSG.Quasithin.ChapterK.Linear.Recognition.BinaryCubicSieve.FiveDisplacement.Inner.EndNode.Levi.Irreducibility.Curtis

namespace CFSG.Quasithin.ChapterK.Linear.Recognition.BinaryCubicSieve.FiveDisplacement.Inner.EndNode.Levi.Irreducibility.Curtis
open Representation Representation.SL5TenDimensional Representation.SL5TenDimensional.Classification
open HeckeAction BinaryLinear.OuterCyclic

/-- Lower roots and adjacent exchanges generate the binary special linear group. -/
theorem lower_swap_induction (P : SL5TenDimensional.Group → Prop)
    (hone : P 1) (hmul : ∀ g h, P g → P h → P (g * h))
    (hlower : ∀ g ∈ lower, P g) (hswap : ∀ i, P (simpleSwap i))
    (g : SL5TenDimensional.Group) : P g := by
  have hsimple (i : Fin 4) : P (simpleUpper i) := by
    have he : simpleUpper i = simpleSwap i * simpleLower i * simpleSwap i := by
      rw [simpleLower_eq_swap_upper_swap]
      simp only [← mul_assoc, swap_sq, one_mul]
      simp only [mul_assoc, swap_sq, mul_one]
    rw [he]
    exact hmul _ _ (hmul _ _ (hswap i) (hlower _ (simpleLower_mem i))) (hswap i)
  have hpos (n : ℕ) (a b : Fin 5) (hab : a < b) (hn : b.val - a.val = n) :
      P (Matrix.SpecialLinearGroup.transvection (ne_of_lt hab) (1 : ZMod 2)) := by
    induction n using Nat.strong_induction_on generalizing a b with
    | h n ih =>
      let i : Fin 4 := ⟨a.val, by have := b.isLt; change a.val < b.val at hab; omega⟩
      have hai : i.castSucc = a := Fin.ext rfl
      have hik : a < i.succ := by rw [← hai]; simp
      by_cases he : i.succ = b
      · simpa only [simpleUpper, hai, he] using hsimple i
      · have hkb : i.succ < b := by
          have hne : i.succ.val ≠ b.val := fun h => he (Fin.ext h)
          change i.val + 1 < b.val
          change a.val < b.val at hab
          dsimp [i] at hne ⊢
          omega
        have hA := hsimple i
        change P (Matrix.SpecialLinearGroup.transvection (ne_of_lt hik) (1 : ZMod 2)) at hA
        have hB := ih (b.val - i.succ.val) (by
          change a.val < b.val at hab
          dsimp [i]
          omega) i.succ b hkb rfl
        let A := Matrix.SpecialLinearGroup.transvection (ne_of_lt hik) (1 : ZMod 2)
        let B := Matrix.SpecialLinearGroup.transvection (ne_of_lt hkb) (1 : ZMod 2)
        let C := Matrix.SpecialLinearGroup.transvection (ne_of_lt hab) (1 : ZMod 2)
        have hchain : A * B = B * C * A := by
          simpa only [A, B, C, one_mul] using
            Representation.OneCohomology.SLHigherNatural.transvection_chain
              (ne_of_lt hik) (ne_of_lt hkb) (ne_of_lt hab) (1 : ZMod 2) 1
        have hAA : A * A = 1 := by
          rw [← Matrix.SpecialLinearGroup.transvection_add]
          exact Matrix.SpecialLinearGroup.transvection_coeff_zero _
        have hBB : B * B = 1 := by
          rw [← Matrix.SpecialLinearGroup.transvection_add]
          exact Matrix.SpecialLinearGroup.transvection_coeff_zero _
        have hC : C = B * (A * B) * A := by
          rw [hchain]
          simp only [← mul_assoc, hBB, one_mul]
          simp only [mul_assoc, hAA, mul_one]
        change P C
        rw [hC]
        exact hmul _ _ (hmul _ _ hB (hmul _ _ hA hB)) hA
  apply Matrix.SpecialLinearGroup.diagonal_transvection_induction' P g
  · intro a b hab c hc
    have hc1 : c = 1 := (by decide : ∀ c : ZMod 2, c ≠ 0 → c = 1) c hc
    subst c
    have hd : Matrix.SpecialLinearGroup.diag2n hab (1 : ZMod 2) hc = 1 := by
      apply Subtype.ext
      simp [Matrix.SpecialLinearGroup.diag2n_coe]
    rwa [hd]
  · intro a b hab c
    rcases (by decide : ∀ c : ZMod 2, c = 0 ∨ c = 1) c with rfl | rfl
    · simpa only [Matrix.SpecialLinearGroup.transvection_coeff_zero] using hone
    · rcases lt_or_gt_of_ne hab with h | h
      · exact hpos _ a b h rfl
      · apply hlower
        rw [← graph_transvection b a hab.symm]
        apply Subgroup.mem_map_of_mem
        exact Subgroup.subset_closure ⟨b,a,h,rfl⟩
  · exact hmul

end CFSG.Quasithin.ChapterK.Linear.Recognition.BinaryCubicSieve.FiveDisplacement.Inner.EndNode.Levi.Irreducibility.Curtis
