module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.Propagation.Backward.Products.Selection.Pencil.Choices.FiniteGeometry.Planes

/-!
# Separating line and plane translates in the marked binary three-space

Choose a vector v moved by an element s of the actor. Completing v, sv to a
basis gives two planes through v which exclude sv; their intersection is the
line through v, which contains no nonidentity common fixed point. For lines,
the lines through v and sv are both moved. Transitivity realizes these
subgroups as translates of any subgroup of the same order.

This supplies the finite geometry for the two conjugates in the first
paragraph of MS93 (4.4.2), printed p.893. It covers both edge orders, two and
four, and imposes no particular actor order or fixed-space dimension. The
consumer in Selection.lean uses the actual compatible local quotient and
natural marking. The only finite reductions concern eight-vector coordinate
identities and the existing binary basis-completion lemma.
-/

public section

open Matrix Subgroup
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.Propagation.Backward.Products.Selection.Choices
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.Propagation.Backward.Products.Selection.Choices.FiniteGeometry

namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.RegularPaths.OrbitEscape.JointNormality.Selection.BinaryGeometry

private def line : Subgroup Space where
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

private instance : DecidablePred (· ∈ line) := fun _ => inferInstanceAs (Decidable (_ ∧ _))

private theorem line_card : Nat.card line = 2 := by rw [Nat.card_eq_fintype_card]; decide

private theorem line_shape : ∀ z : Space, z ∈ line ↔ z = 1 ∨ z = e0 := by decide

private theorem line_transitive (A : Subgroup Space) (hA : Nat.card A = 2) :
    ∃ g : SL, move g line = A := by
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
  refine ⟨g, Subgroup.eq_of_le_of_card_ge ?_ ?_⟩
  · rintro _ ⟨z, hz, rfl⟩
    rcases (line_shape z).mp hz with rfl | rfl
    · simpa only [map_one] using A.one_mem
    · change modelAction g e0 ∈ A
      rw [hg0]
      exact u.property
  · rw [move_card, line_card, hA]

private theorem equal_card_transitive (A B : Subgroup Space)
    (hA : Nat.card A = 2 ∨ Nat.card A = 4) (hB : Nat.card B = Nat.card A) :
    ∃ g : SL, move g A = B := by
  rcases hA with hA | hA
  · obtain ⟨a, rfl⟩ := line_transitive A hA
    obtain ⟨b, hb⟩ := line_transitive B (hB.trans hA)
    exact ⟨b * a⁻¹, by rw [← move_mul, move_cancel]; exact hb⟩
  · obtain ⟨a, rfl⟩ := plane_transitive A hA
    obtain ⟨b, hb⟩ := plane_transitive B (hB.trans hA)
    exact ⟨b * a⁻¹, by rw [← move_mul, move_cancel]; exact hb⟩

private def swap01 : SL := ⟨!![0,1,0; 1,0,0; 0,0,1], by decide⟩
private def plane1Actor : SL := ⟨!![1,0,0; 0,0,1; 0,1,0], by decide⟩
private def plane2Actor : SL := ⟨!![1,0,0; 0,1,0; 0,1,1], by decide⟩
private abbrev plane1 := move plane1Actor standardPlane
private abbrev plane2 := move plane2Actor standardPlane

private theorem mem_plane1 (v : Space) : v ∈ plane1 ↔ v.toAdd 1 = 0 := by
  rw [Subgroup.mem_map_equiv]
  change ((plane1Actor⁻¹).val.mulVec v.toAdd) 2 = 0 ↔ v.toAdd 1 = 0
  have test : ∀ v : Fin 3 → ZMod 2,
      ((plane1Actor⁻¹).val.mulVec v) 2 = 0 ↔ v 1 = 0 := by decide +kernel
  exact test v.toAdd

private theorem mem_plane2 (v : Space) : v ∈ plane2 ↔ v.toAdd 1 = v.toAdd 2 := by
  rw [Subgroup.mem_map_equiv]
  change ((plane2Actor⁻¹).val.mulVec v.toAdd) 2 = 0 ↔ v.toAdd 1 = v.toAdd 2
  have test : ∀ v : Fin 3 → ZMod 2,
      ((plane2Actor⁻¹).val.mulVec v) 2 = 0 ↔ v 1 = v 2 := by decide +kernel
  exact test v.toAdd

private theorem planes_inf : plane1 ⊓ plane2 = line := by
  ext v
  rw [mem_inf, mem_plane1, mem_plane2]
  change (v.toAdd 1 = 0 ∧ v.toAdd 1 = v.toAdd 2) ↔
    (v.toAdd 1 = 0 ∧ v.toAdd 2 = 0)
  aesop

private theorem move_line_shape (k : SL) (v : Space) :
    v ∈ move k line ↔ v = 1 ∨ v = modelAction k e0 := by
  constructor
  · rintro ⟨z, hz, rfl⟩
    rcases (line_shape z).mp hz with rfl | rfl
    · exact Or.inl (map_one _)
    · exact Or.inr rfl
  · rintro (rfl | rfl)
    · exact (move k line).one_mem
    · exact mem_map_of_mem _ ((line_shape e0).mpr (Or.inr rfl))

/-- Two translates moved by the actor have trivial common intersection with its fixed space. -/
theorem exists_separating_translates (A : Subgroup Space)
    (hA : Nat.card A = 2 ∨ Nat.card A = 4) (H : Subgroup SL)
    (hmoved : ∃ s ∈ H, ∃ v : Space, modelAction s v ≠ v) :
    ∃ g h : SL, ¬ H ≤ planeStabilizer (move g A) ∧
      ¬ H ≤ planeStabilizer (move h A) ∧
      (move g A ⊓ move h A) ⊓ fixedSpace H = ⊥ := by
  obtain ⟨s, hs, v, hv⟩ := hmoved
  have hv0 : v.toAdd ≠ 0 := by
    intro he
    have h : v = 1 := he
    exact hv (by rw [h, map_one])
  have hsv0 : (modelAction s v).toAdd ≠ 0 := by
    intro he
    apply hv0
    change modelAction s v = 1 at he
    change v = 1
    exact (modelAction s).injective (he.trans (map_one _).symm)
  obtain ⟨w, hw⟩ := complete_pair v.toAdd (modelAction s v).toAdd hv0 hsv0 (Ne.symm hv)
  let k : SL := ⟨fun i => ![v.toAdd i, (modelAction s v).toAdd i, w i], hw⟩
  have hk0 : modelAction k e0 = v := by
    change k.val.mulVec ![1,0,0] = v.toAdd
    ext i
    simp [k, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
  have hk1 : modelAction k e1 = modelAction s v := by
    change k.val.mulVec ![0,1,0] = (modelAction s v).toAdd
    ext i
    simp [k, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
  have line_fixed : move k line ⊓ fixedSpace H = ⊥ := by
    apply le_antisymm _ bot_le
    intro z hz
    rcases (move_line_shape k z).mp hz.1 with rfl | hzv
    · exact one_mem _
    · rw [hk0] at hzv
      exact (hv (hzv ▸ hz.2 s hs)).elim
  rcases hA with hA | hA
  · let B := move k line
    let D := move (k * swap01) line
    have hd : modelAction (k * swap01) e0 = modelAction s v := by
      rw [map_mul, MulAut.mul_apply]
      exact hk1
    have hnB : ¬ H ≤ planeStabilizer B := by
      intro h
      have hx : v ∈ B := hk0 ▸ mem_map_of_mem (modelAction k).toMonoidHom
        ((line_shape e0).mpr (Or.inr rfl))
      have hy := (mem_planeStabilizer_iff s B).mp (h hs) v hx
      rcases (move_line_shape k _).mp hy with h1 | h1
      · exact hsv0 h1
      · exact hv (h1.trans hk0)
    have hnD : ¬ H ≤ planeStabilizer D := by
      intro h
      have hx : modelAction s v ∈ D := hd ▸ mem_map_of_mem
        (modelAction (k * swap01)).toMonoidHom ((line_shape e0).mpr (Or.inr rfl))
      have hy := (mem_planeStabilizer_iff s D).mp (h hs) _ hx
      rcases (move_line_shape (k * swap01) _).mp hy with h1 | h1
      · exact hsv0 ((modelAction s).injective (h1.trans (map_one _).symm))
      · exact hv ((modelAction s).injective (h1.trans hd))
    obtain ⟨g, hg⟩ := equal_card_transitive A B (Or.inl hA)
      (by rw [move_card, line_card, hA])
    obtain ⟨h, hh⟩ := equal_card_transitive A D (Or.inl hA)
      (by rw [move_card, line_card, hA])
    refine ⟨g, h, by rwa [hg], by rwa [hh], ?_⟩
    apply le_antisymm _ bot_le
    exact (inf_le_inf inf_le_left le_rfl).trans_eq (by rwa [hg])
  · have hn (B : Subgroup Space) (h0 : e0 ∈ B) (h1 : e1 ∉ B) :
        ¬ H ≤ planeStabilizer (move k B) := by
      intro h
      have hx : v ∈ move k B := hk0 ▸ mem_map_of_mem (modelAction k).toMonoidHom h0
      have hy := (mem_planeStabilizer_iff s (move k B)).mp (h hs) v hx
      rw [← hk1] at hy
      exact h1 ((Subgroup.mem_map_iff_mem (modelAction k).injective).mp hy)
    have hn1 := hn plane1 ((mem_plane1 e0).mpr rfl)
      (by rw [mem_plane1]; decide)
    have hn2 := hn plane2 ((mem_plane2 e0).mpr rfl)
      (by rw [mem_plane2]; decide)
    obtain ⟨g, hg⟩ := equal_card_transitive A (move k plane1) (Or.inr hA)
      (by rw [move_card, move_card, standardPlane_card, hA])
    obtain ⟨h, hh⟩ := equal_card_transitive A (move k plane2) (Or.inr hA)
      (by rw [move_card, move_card, standardPlane_card, hA])
    refine ⟨g, h, by rwa [hg], by rwa [hh], ?_⟩
    rw [hg, hh, ← Subgroup.map_inf _ _ (modelAction k).toMonoidHom
      (modelAction k).injective, planes_inf]
    exact line_fixed

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.RegularPaths.OrbitEscape.JointNormality.Selection.BinaryGeometry
