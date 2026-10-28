module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.Propagation.Backward.Products.Selection.Pencil.Choices.FiniteGeometry
public import Theory.GroupTheory.PGroup.MaximalIndex

/-!
# Two choices in the binary natural module

Mark an order-two subgroup D as the first coordinate line inside a plane
containing a given proper subgroup C. For an edge of order two, choose two
lines outside that plane. For an edge of order four, choose two planes
missing D whose common line is outside the containing plane. Transitivity
on lines and planes realizes both choices as translates of the original
edge. Only small vector calculations are checked by kernel reduction.

This is the finite geometry used in the source choices after MS93 (4.4.5),
printed p.895. The ambient application is in ChoiceConstruction.LocalChoice.
-/

public section

open Matrix Subgroup
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.Propagation.Backward.Products.Selection.Choices
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.Propagation.Backward.Products.Selection.Choices.FiniteGeometry
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.FinalCalculation.Conclusion.ProductSource.ChoiceConstruction

private def firstLine : Subgroup Space where
  carrier := {v | v.toAdd 1 = 0 ∧ v.toAdd 2 = 0}
  one_mem' := ⟨rfl, rfl⟩
  mul_mem' := by
    rintro v w ⟨hv1, hv2⟩ ⟨hw1, hw2⟩
    exact ⟨by change v.toAdd 1 + w.toAdd 1 = 0; rw [hv1, hw1, add_zero],
      by change v.toAdd 2 + w.toAdd 2 = 0; rw [hv2, hw2, add_zero]⟩
  inv_mem' := by
    rintro v ⟨hv1, hv2⟩
    exact ⟨by change -v.toAdd 1 = 0; rw [hv1, neg_zero],
      by change -v.toAdd 2 = 0; rw [hv2, neg_zero]⟩
private instance : DecidablePred (· ∈ firstLine) := fun _ => inferInstanceAs (Decidable (_ ∧ _))

private theorem firstLine_card : Nat.card firstLine = 2 := by
  rw [Nat.card_eq_fintype_card]
  decide

private theorem line_transitive (A : Subgroup Space) (hA : Nat.card A = 2) :
    ∃ g : SL, move g firstLine = A := by
  classical
  have : Nontrivial A := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  obtain ⟨u, hu⟩ := exists_ne (1 : A)
  have hu0 : u.val.toAdd ≠ 0 := fun h => hu (Subtype.ext h)
  have other : ∀ u : Fin 3 → ZMod 2, ∃ v : Fin 3 → ZMod 2, v ≠ 0 ∧ u ≠ v := by decide
  obtain ⟨v, hv, huv⟩ := other u.val.toAdd
  obtain ⟨w, hw⟩ := complete_pair u.val.toAdd v hu0 hv huv
  let g : SL := ⟨(fun i => ![u.val.toAdd i, v i, w i]), hw⟩
  have hg0 : modelAction g e0 = u.val := by
    change g.val.mulVec ![1, 0, 0] = u.val.toAdd
    ext i
    simp [g, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
  have shape : ∀ z : Space, z ∈ firstLine → z = 1 ∨ z = e0 := by decide
  refine ⟨g, Subgroup.eq_of_le_of_card_ge ?_ ?_⟩
  · rintro _ ⟨z, hz, rfl⟩
    rcases shape z hz with rfl | rfl
    · simpa only [map_one] using A.one_mem
    · change modelAction g e0 ∈ A
      rw [hg0]
      exact u.property
  · rw [move_card, firstLine_card, hA]

/-- Complete the actual critical line to a marked plane containing the kernel. -/
private theorem flag_coordinates (D C : Subgroup Space) (hD : Nat.card D = 2)
    (hDC : D ≤ C) (hC : C ≠ ⊤) :
    ∃ k : SL, move k firstLine = D ∧ C ≤ move k standardPlane := by
  classical
  obtain ⟨P, hP, hCP⟩ := (eq_top_or_exists_le_coatom C).resolve_left hC
  have hp : IsPGroup 2 Space := IsPGroup.of_card (n := 3) (by
    rw [Nat.card_eq_fintype_card]; decide)
  have hPc : Nat.card P = 4 := by
    have h := P.card_mul_index
    rw [hp.index_of_isCoatom P hP] at h
    have h8 : Nat.card Space = 8 := by rw [Nat.card_eq_fintype_card]; decide
    rw [h8] at h
    omega
  have : Nontrivial D := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  obtain ⟨u, hu⟩ := exists_ne (1 : D)
  let r : P := ⟨u, hCP (hDC u.property)⟩
  obtain ⟨v, hv, hvr⟩ := ENat.exists_ne_ne_of_three_le
    (α := P) (by rw [ENat.card_eq_coe_natCard, hPc]; decide) 1 r
  have hu0 : u.val.toAdd ≠ 0 := fun h => hu (Subtype.ext h)
  have hv0 : v.val.toAdd ≠ 0 := fun h => hv (Subtype.ext h)
  have huv : u.val.toAdd ≠ v.val.toAdd := fun h => hvr (Subtype.ext h.symm)
  obtain ⟨w, hw⟩ := complete_pair u.val.toAdd v.val.toAdd hu0 hv0 huv
  let k : SL := ⟨(fun i => ![u.val.toAdd i, v.val.toAdd i, w i]), hw⟩
  have hk0 : modelAction k e0 = u.val := by
    change k.val.mulVec ![1, 0, 0] = u.val.toAdd
    ext i
    simp [k, mulVec, dotProduct, Fin.sum_univ_three]
  have hk1 : modelAction k e1 = v.val := by
    change k.val.mulVec ![0, 1, 0] = v.val.toAdd
    ext i
    simp [k, mulVec, dotProduct, Fin.sum_univ_three]
  have hplane : move k standardPlane = P := by
    apply Subgroup.eq_of_le_of_card_ge
    · apply Subgroup.map_le_iff_le_comap.mpr
      apply standardPlane_le
      · change modelAction k e0 ∈ P
        rw [hk0]
        exact r.property
      · change modelAction k e1 ∈ P
        rw [hk1]
        exact v.property
    · rw [move_card, standardPlane_card, hPc]
  refine ⟨k, ?_, hplane.symm ▸ hCP⟩
  apply Subgroup.eq_of_le_of_card_ge
  · rintro _ ⟨z, hz, rfl⟩
    have shape : ∀ z : Space, z ∈ firstLine → z = 1 ∨ z = e0 := by decide
    rcases shape z hz with rfl | rfl
    · simpa only [map_one] using D.one_mem
    · change modelAction k e0 ∈ D
      rw [hk0]
      exact u.property
  · rw [move_card, firstLine_card, hD]

-- Both choices contain a vector outside the marked kernel plane.
private def lineChoice : Fin 2 → SL := ![
  ⟨!![0, 0, 1; 0, 1, 0; 1, 0, 0], by decide⟩,
  ⟨!![1, 0, 1; 0, 1, 0; 1, 0, 0], by decide⟩]

private theorem standard_line_choices :
    ∃ g h : SL,
      ¬ firstLine ≤ move g firstLine ∧ ¬ firstLine ≤ move h firstLine ∧
      ¬ move g firstLine ≤ standardPlane ∧ ¬ move h firstLine ≤ standardPlane ∧
      (move g firstLine ⊓ move h firstLine) ⊓ standardPlane = ⊥ := by
  refine ⟨lineChoice 0, lineChoice 1, ?_, ?_, ?_, ?_, ?_⟩
  · intro h
    have hh := h (show e0 ∈ firstLine from ⟨rfl, rfl⟩)
    rw [Subgroup.mem_map_equiv] at hh
    revert hh
    decide +kernel
  · intro h
    have hh := h (show e0 ∈ firstLine from ⟨rfl, rfl⟩)
    rw [Subgroup.mem_map_equiv] at hh
    revert hh
    decide +kernel
  · intro h
    have hh := h (mem_map_of_mem (modelAction (lineChoice 0)).toMonoidHom
      (show e0 ∈ firstLine from ⟨rfl, rfl⟩))
    revert hh
    decide +kernel
  · intro h
    have hh := h (mem_map_of_mem (modelAction (lineChoice 1)).toMonoidHom
      (show e0 ∈ firstLine from ⟨rfl, rfl⟩))
    revert hh
    decide +kernel
  · apply le_bot_iff.mp
    intro v hv
    have h0 := (Subgroup.mem_map_equiv).mp hv.1.1
    have h1 := (Subgroup.mem_map_equiv).mp hv.1.2
    change v = 1
    have test : ∀ v : Space,
        (modelAction (lineChoice 0)).symm v ∈ firstLine →
        (modelAction (lineChoice 1)).symm v ∈ firstLine → v = 1 := by decide +kernel
    exact test v h0 h1

private theorem standard_plane_choices :
    ∃ g h : SL,
      ¬ firstLine ≤ move g standardPlane ∧ ¬ firstLine ≤ move h standardPlane ∧
      ¬ move g standardPlane ≤ standardPlane ∧ ¬ move h standardPlane ≤ standardPlane ∧
      (move g standardPlane ⊓ move h standardPlane) ⊓ standardPlane = ⊥ := by
  refine ⟨crossActor 0, crossActor 2, ?_, ?_, ?_, ?_, ?_⟩
  · intro h
    have hh := (mem_crossPlane 0 e0).mp (h (show e0 ∈ firstLine from ⟨rfl, rfl⟩))
    exact (by decide : crossEval 0 e0.toAdd ≠ 0) hh
  · intro h
    have hh := (mem_crossPlane 2 e0).mp (h (show e0 ∈ firstLine from ⟨rfl, rfl⟩))
    exact (by decide : crossEval 2 e0.toAdd ≠ 0) hh
  · intro h
    have hh := h ((mem_crossPlane 0 _).mpr (show crossEval 0 ![0,0,1] = 0 from rfl))
    exact (by decide : (Multiplicative.ofAdd ![0,0,1] : Space) ∉ standardPlane) hh
  · intro h
    have hh := h ((mem_crossPlane 2 _).mpr (show crossEval 2 ![0,0,1] = 0 by decide))
    exact (by decide : (Multiplicative.ofAdd ![0,0,1] : Space) ∉ standardPlane) hh
  · apply le_bot_iff.mp
    intro v hv
    have h0 := (mem_crossPlane 0 v).mp hv.1.1
    have h2 := (mem_crossPlane 2 v).mp hv.1.2
    change v = 1
    have test : ∀ v : Space, crossEval 0 v.toAdd = 0 → crossEval 2 v.toAdd = 0 →
        v ∈ standardPlane → v = 1 := by decide
    exact test v h0 h2 hv.2

theorem finite_choices (A D C : Subgroup Space) (hA : Nat.card A = 2 ∨ Nat.card A = 4)
    (hD : Nat.card D = 2) (hDC : D ≤ C) (hC : C ≠ ⊤) :
    ∃ g h : SL,
      ¬ D ≤ move g A ∧ ¬ D ≤ move h A ∧
      ¬ move g A ≤ C ∧ ¬ move h A ≤ C ∧
      (move g A ⊓ move h A) ⊓ C = ⊥ := by
  obtain ⟨k, hkD, hkC⟩ := flag_coordinates D C hD hDC hC
  have transport (B : Subgroup Space) (a : SL) (ha : move a B = A)
      (choices : ∃ g h : SL,
        ¬ firstLine ≤ move g B ∧ ¬ firstLine ≤ move h B ∧
        ¬ move g B ≤ standardPlane ∧ ¬ move h B ≤ standardPlane ∧
        (move g B ⊓ move h B) ⊓ standardPlane = ⊥) :
      ∃ g h : SL, ¬ D ≤ move g A ∧ ¬ D ≤ move h A ∧
        ¬ move g A ≤ C ∧ ¬ move h A ≤ C ∧
        (move g A ⊓ move h A) ⊓ C = ⊥ := by
    obtain ⟨g, h, hgD, hhD, hgC, hhC, hsep⟩ := choices
    have he (s : SL) : move (k * s * a⁻¹) A = move k (move s B) := by
      rw [← ha, ← move_mul, move_cancel, ← move_mul]
    have refl_le (X Y : Subgroup Space) (h : move k X ≤ move k Y) : X ≤ Y := by
      intro x hx
      exact (Subgroup.mem_map_iff_mem (modelAction k).injective).mp
        (h (mem_map_of_mem (modelAction k).toMonoidHom hx))
    refine ⟨k * g * a⁻¹, k * h * a⁻¹, ?_, ?_, ?_, ?_, ?_⟩
    · rw [he, ← hkD]
      exact fun hn => hgD (refl_le _ _ hn)
    · rw [he, ← hkD]
      exact fun hn => hhD (refl_le _ _ hn)
    · rw [he]
      exact fun hn => hgC (refl_le _ _ (hn.trans hkC))
    · rw [he]
      exact fun hn => hhC (refl_le _ _ (hn.trans hkC))
    · rw [he, he]
      apply le_bot_iff.mp
      apply le_trans (inf_le_inf_left _ hkC)
      rw [← Subgroup.map_inf _ _ (modelAction k).toMonoidHom (modelAction k).injective,
        ← Subgroup.map_inf _ _ (modelAction k).toMonoidHom (modelAction k).injective,
        hsep, Subgroup.map_bot]
  rcases hA with hA | hA
  · obtain ⟨a, ha⟩ := line_transitive A hA
    exact transport firstLine a ha standard_line_choices
  · obtain ⟨a, ha⟩ := plane_transitive A hA
    exact transport standardPlane a ha standard_plane_choices
end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.FinalCalculation.Conclusion.ProductSource.ChoiceConstruction
