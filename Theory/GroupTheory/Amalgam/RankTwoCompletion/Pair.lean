module

public import Theory.GroupTheory.Amalgam.RankTwoCompletion.CommonCover

/-!
# Paired faithful completions

The image of the universal amalgam in the product of two completions is
itself a faithful completion. Its projections preserve both endpoint maps.
A homomorphism preserving the marking is a coset covering whenever both
completions have the whole marked overlap.

This supplies a concrete common completion for comparing small rank-two
geometries, as in Aschbacher–Smith F.3.3–4, printed p.270.
-/

@[expose] public section

open Subgroup Subgroup.CosetGeometry.RankTwo
namespace Theory.GroupTheory.RankTwoAmalgam.FaithfulCompletion
universe u v w
variable {L B R : Type u} [Group L] [Group B] [Group R]
variable {G : Type v} [Group G] {H : Type w} [Group H]
variable {α : RankTwoAmalgam L B R}
variable (c : FaithfulCompletion α (G := G)) (d : FaithfulCompletion α (G := H))
noncomputable section

def pairMap : α.Universal →* G × H := (Universal.lift α c).prod (Universal.lift α d)
abbrev Pair := (pairMap c d).range

def pairCompletion : FaithfulCompletion α (G := Pair c d) where
  left := (pairMap c d).rangeRestrict.comp (Universal.left α)
  right := (pairMap c d).rangeRestrict.comp (Universal.right α)
  compatible := by rw [MonoidHom.comp_assoc, MonoidHom.comp_assoc, Universal.compatible]
  left_injective := by
    intro x y h
    apply c.left_injective
    exact (Universal.lift_left α c x).symm.trans
      ((congrArg (fun z : Pair c d => z.val.1) h).trans (Universal.lift_left α c y))
  right_injective := by
    intro x y h
    apply c.right_injective
    exact (Universal.lift_right α c x).symm.trans
      ((congrArg (fun z : Pair c d => z.val.1) h).trans (Universal.lift_right α c y))
  middle_injective := by
    intro x y h
    apply c.middle_injective
    have he := congrArg (fun z : Pair c d => z.val.1) h
    change Universal.lift α c (Universal.left α (α.left x)) =
      Universal.lift α c (Universal.left α (α.left y)) at he
    simpa only [Universal.lift_left, MonoidHom.comp_apply] using he
  generated := by
    rw [MonoidHom.range_comp, MonoidHom.range_comp, ← Subgroup.map_sup,
      Universal.generated]
    exact Subgroup.map_top_of_surjective _ (pairMap c d).rangeRestrict_surjective

def pairFst : Pair c d →* G := (MonoidHom.fst G H).comp (pairMap c d).range.subtype
def pairSnd : Pair c d →* H := (MonoidHom.snd G H).comp (pairMap c d).range.subtype

@[simp] theorem pairFst_left (x : L) : pairFst c d ((pairCompletion c d).left x) = c.left x :=
  Universal.lift_left α c x
@[simp] theorem pairFst_right (x : R) : pairFst c d ((pairCompletion c d).right x) = c.right x :=
  Universal.lift_right α c x
@[simp] theorem pairSnd_left (x : L) : pairSnd c d ((pairCompletion c d).left x) = d.left x :=
  Universal.lift_left α d x
@[simp] theorem pairSnd_right (x : R) : pairSnd c d ((pairCompletion c d).right x) = d.right x :=
  Universal.lift_right α d x

variable {c d}
/-- A homomorphism of generated faithful completions is a covering when both overlaps are whole. -/
theorem coverData_of_hom (f : G →* H)
    (hl : f.comp c.left = d.left) (hr : f.comp c.right = d.right)
    (hc : c.left.range ⊓ c.right.range = c.middle.range)
    (hd : d.left.range ⊓ d.right.range = d.middle.range) :
    CoverData c.cosetFamily d.cosetFamily f where
  surjective := by
    apply MonoidHom.range_eq_top.mp
    apply top_unique
    rw [←d.generated]
    apply sup_le
    · rw [←hl, MonoidHom.range_comp]
      exact Subgroup.map_le_range _ _
    · rw [←hr, MonoidHom.range_comp]
      exact Subgroup.map_le_range _ _
  map_eq i := by
    cases i
    · change c.left.range.map f = d.left.range
      rw [←MonoidHom.range_comp, hl]
    · change c.right.range.map f = d.right.range
      rw [←MonoidHom.range_comp, hr]
  injective i := by
    cases i
    · rintro ⟨_,x,rfl⟩ ⟨_,y,rfl⟩ he
      have hxy : x=y := d.left_injective (by
        simpa only [←hl,MonoidHom.comp_apply] using he)
      subst y
      rfl
    · rintro ⟨_,x,rfl⟩ ⟨_,y,rfl⟩ he
      have hxy : x=y := d.right_injective (by
        simpa only [←hr,MonoidHom.comp_apply] using he)
      subst y
      rfl
  map_inf := by
    change (c.left.range ⊓ c.right.range).map f = d.left.range ⊓ d.right.range
    rw [hc,hd,←MonoidHom.range_comp]
    congr 1
    exact (MonoidHom.comp_assoc _ _ _).symm.trans (congrArg (fun h => h.comp α.left) hl)
end
end Theory.GroupTheory.RankTwoAmalgam.FaithfulCompletion
