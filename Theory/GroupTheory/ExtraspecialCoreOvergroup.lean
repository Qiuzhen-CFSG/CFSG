module

public import Theory.ElementaryAbelian.Extraspecial
public import Theory.GroupTheory.PCoreCentralQuotientImage
public import Theory.GroupTheory.AbelianImageCoreEquality

/-!
# Extraspecial overgroups of a self-centralizing prime core

Suppose a finite group has self-centralizing p-core, contained in an
extraspecial p-subgroup R whose center is central in the whole group.
Quotient by that embedded center. The core image is self-centralizing and
lies in the abelian image of R, so the two images coincide. The quotient
kernel lies in the core, and equality lifts to the original subgroups.

This gives the core comparison in Aschbacher--Smith 14.2.16, printed p.986,
using the central-quotient argument of A.1.6 and 14.2.21's chain (*).
-/

public noncomputable section
open Subgroup
open scoped IsMulCommutative

namespace Subgroup
variable {D : Type*} [Group D] [Finite D] {p : ℕ} [Fact p.Prime]

theorem pCore_eq_of_extraspecial_overgroup (R : Subgroup D) [IsExtraspecial p R]
    (hQR : pCore p D ≤ R)
    (hcenter : (center R).map R.subtype ≤ center D)
    (hc : centralizer (pCore p D : Set D) ≤ pCore p D) : pCore p D = R := by
  let Z := (center R).map R.subtype
  have hZ : Z ≤ center D := hcenter
  let : Z.Normal := ⟨fun a ha b => by
    simpa only [mem_center_iff.mp (hZ ha) b, mul_inv_cancel_right] using ha⟩
  let q := QuotientGroup.mk' Z
  let f : R →* D ⧸ Z := q.comp R.subtype
  have hk : center R ≤ f.ker := by
    intro x hx
    exact (QuotientGroup.eq_one_iff _).mpr ⟨x, hx, rfl⟩
  let ff : R ⧸ center R →* D ⧸ Z := QuotientGroup.lift (center R) f hk
  let : IsElementaryAbelian p (R ⧸ center R) :=
    IsExtraspecial.quotient_elementary_abelian p R
  have hrange : ff.range = R.map q := by
    ext x
    constructor
    · rintro ⟨v, rfl⟩
      obtain ⟨r, rfl⟩ := QuotientGroup.mk'_surjective (center R) v
      exact ⟨r, r.property, rfl⟩
    · rintro ⟨r, hr, rfl⟩
      exact ⟨QuotientGroup.mk' (center R) ⟨r,hr⟩, rfl⟩
  have : IsMulCommutative ff.range := ⟨⟨fun a b => by
    obtain ⟨x, rfl⟩ := ff.rangeRestrict_surjective a
    obtain ⟨y, rfl⟩ := ff.rangeRestrict_surjective b
    simpa only [← map_mul] using congrArg ff.rangeRestrict (mul_comm x y)⟩⟩
  let : IsMulCommutative (R.map q) := hrange ▸ this
  apply eq_of_abelian_map_of_centralizer_le q (pCore p D) R _ hQR
    (centralizer_image_pCore_le_of_central_quotient Z hZ hc)
  rw [QuotientGroup.ker_mk']
  exact (hZ.trans (center_le_centralizer _)).trans hc
end Subgroup
