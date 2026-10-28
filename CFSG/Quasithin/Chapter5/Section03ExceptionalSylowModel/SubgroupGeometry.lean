module

public import Theory.SpecificGroups.PSL3Four.SylowModel
public import Stellmacher.ElementaryAbelianMaxDefs

/-!
# Subgroup geometry of the exceptional Sylow model

The commutator on the two root coordinates is the determinant over F4.
Two noncommuting elements of a subgroup of the unipotent group therefore
force its center into the highest-root subgroup. The quotient calculations
use the central involution fixed by the field automorphism.

Source: Aschbacher--Smith, *The Classification of Quasithin Groups*,
§5.3.7, printed pp. 660--661 (PDF pp. 677--678).
-/

@[expose] public section
noncomputable section
namespace Matrix.PSL3Four.SylowModel

private theorem root_coordinates_zero_of_commutes
    (a b d : U) (hab : a * b ≠ b * a)
    (hda : d * a = a * d) (hdb : d * b = b * d) :
    d.x = 0 ∧ d.y = 0 := by
  have hdet : a.x * b.y - b.x * a.y ≠ 0 := by
    intro h
    apply hab
    apply (commute_iff a b).mpr
    exact sub_eq_zero.mp h
  have ha := (commute_iff d a).mp hda
  have hb := (commute_iff d b).mp hdb
  have hx : (a.x * b.y - b.x * a.y) * d.x = 0 := by
    calc
      (a.x * b.y - b.x * a.y) * d.x =
          a.x * (d.x * b.y - b.x * d.y) -
          b.x * (d.x * a.y - a.x * d.y) := by ring
      _ = 0 := by rw [sub_eq_zero.mpr hb, sub_eq_zero.mpr ha]; ring
  have hy : (a.x * b.y - b.x * a.y) * d.y = 0 := by
    calc
      (a.x * b.y - b.x * a.y) * d.y =
          b.y * (a.x * d.y - d.x * a.y) -
          a.y * (b.x * d.y - d.x * b.y) := by ring
      _ = 0 := by rw [sub_eq_zero.mpr ha.symm, sub_eq_zero.mpr hb.symm]; ring
  exact ⟨(mul_eq_zero.mp hx).resolve_left hdet,
    (mul_eq_zero.mp hy).resolve_left hdet⟩

/-- The highest-root subgroup is the center of every nonabelian subgroup
of the unipotent group which contains it. -/
theorem center_nonabelian_le_S (W : Subgroup T)
    (hZ : Z ≤ W) (hS : W ≤ S) (hnoncomm : ¬ IsMulCommutative W) :
    (Subgroup.center W).map W.subtype = Z := by
  rw [isMulCommutative_iff] at hnoncomm
  push Not at hnoncomm
  obtain ⟨a, b, hab⟩ := hnoncomm
  have hab' : a.val.left * b.val.left ≠ b.val.left * a.val.left := by
    intro h
    apply hab
    apply Subtype.ext
    change a.val * b.val = b.val * a.val
    apply SemidirectProduct.ext
    · simpa only [SemidirectProduct.mul_left, (mem_S a.val).mp (hS a.property),
        (mem_S b.val).mp (hS b.property), map_one, MulAut.one_apply] using h
    · simp [(mem_S a.val).mp (hS a.property),
        (mem_S b.val).mp (hS b.property)]
  apply le_antisymm
  · rintro d ⟨e, he, rfl⟩
    have hda : e.val.left * a.val.left = a.val.left * e.val.left := by
      have hc := Subgroup.mem_center_iff.mp he a
      have hc' := congrArg (fun t : T => t.left) (congrArg Subtype.val hc)
      change (a.val * e.val).left = (e.val * a.val).left at hc'
      simpa only [SemidirectProduct.mul_left, (mem_S e.val).mp (hS e.property),
        (mem_S a.val).mp (hS a.property), map_one, MulAut.one_apply] using hc'.symm
    have hdb : e.val.left * b.val.left = b.val.left * e.val.left := by
      have hc := Subgroup.mem_center_iff.mp he b
      have hc' := congrArg (fun t : T => t.left) (congrArg Subtype.val hc)
      change (b.val * e.val).left = (e.val * b.val).left at hc'
      simpa only [SemidirectProduct.mul_left, (mem_S e.val).mp (hS e.property),
        (mem_S b.val).mp (hS b.property), map_one, MulAut.one_apply] using hc'.symm
    exact (mem_Z e.val).mpr ⟨(mem_S e.val).mp (hS e.property),
      root_coordinates_zero_of_commutes _ _ _ hab' hda hdb⟩
  · intro d hd
    have hdW : d ∈ W := hZ hd
    refine ⟨⟨d, hdW⟩, ?_, rfl⟩
    apply Subgroup.mem_center_iff.mpr
    intro a
    apply Subtype.ext
    change a.val * d = d * a.val
    apply SemidirectProduct.ext
    · have hz := (mem_Z d).mp hd
      have hs := (mem_S a.val).mp (hS a.property)
      simpa only [SemidirectProduct.mul_left, hz.1, hs, map_one,
        MulAut.one_apply] using (commute_iff d.left a.val.left).mpr
          (by simp [hz.2.1, hz.2.2]) |>.symm
    · simp [(mem_Z d).mp hd |>.1, (mem_S a.val).mp (hS a.property)]

end Matrix.PSL3Four.SylowModel
