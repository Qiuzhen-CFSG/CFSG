module

public import Theory.SpecificGroups.PSL2.PGL2SylowNormalizedFive
public import Theory.SpecificGroups.GL2.SubgroupCenter
public import Theory.SpecificGroups.SL2.PrimeFiveEquiv
public import GorensteinWalter.SL2ProjectiveCover

/-!
# The linear centralizer application of the prime-five restriction

The projective image of a noncommutative subgroup of GL₂ is its quotient
by its own center: every matrix centralizing the subgroup is scalar.
Consequently an SL₂(5) subgroup projects to A₅, and normalization by a
full Sylow two-subgroup forces the prime field parameter to be five.

This is the actual GL₂ centralizer application in Aschbacher–Smith C.5.8;
the full Sylow hypothesis is retained through the projective quotient.
-/

public noncomputable section
open Subgroup
open scoped MatrixGroups
namespace Matrix.GeneralLinearGroup

/-- The actual projective image of a noncommutative binary linear
subgroup is its quotient by its own center. -/
theorem projective_image_equiv_quotient_center
    {F : Type*} [Field F] (B : Subgroup (GL (Fin 2) F))
    (hB : ¬ IsMulCommutative B) :
    Nonempty (B.map ProjGenLinGroup.mk ≃* B ⧸ center B) := by
  let f : B →* ProjGenLinGroup (Fin 2) F := ProjGenLinGroup.mk.comp B.subtype
  have hk : f.ker = center B := by
    apply Subgroup.map_injective (f := B.subtype) B.subtype_injective
    rw [show f.ker = (center (GL (Fin 2) F)).comap B.subtype by
      rw [← ProjGenLinGroup.ker_mk]
      rfl]
    rw [map_comap_eq, B.range_subtype, center_eq_range_scalar,
      center_map_eq_inf_scalar_of_noncommutative B hB]
  have hr : f.range = B.map ProjGenLinGroup.mk := by
    rw [MonoidHom.range_comp, B.range_subtype]
  exact ⟨((MulEquiv.subgroupCongr hr.symm).trans
    (QuotientGroup.quotientKerEquivRange f).symm).trans
      (QuotientGroup.quotientMulEquivOfEq hk)⟩

/-- The original GL₂ centralizer form: a full Sylow two-subgroup
normalizing an SL₂(5) subgroup forces characteristic five. -/
theorem prime_eq_five_of_sylow_normalizes_sl2_five
    {F : Type*} [Field F] [Finite F] {p : ℕ} [Fact p.Prime]
    (ho : Odd p) (hF : Nat.card F = p)
    (T : Sylow 2 (GL (Fin 2) F)) (B : Subgroup (GL (Fin 2) F))
    (hB : Nonempty (B ≃* SL(2, ZMod 5)))
    (hTB : (T : Subgroup _) ≤ normalizer (B : Set (GL (Fin 2) F))) : p = 5 := by
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  obtain ⟨e⟩ := hB
  let : Group.IsPerfect SL(2, ZMod 5) :=
    GorensteinWalter.sl2_isPerfect_of_card_gt_three (ZMod 5) (by norm_num)
  let : Group.IsPerfect B :=
    Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  let : IsSimpleGroup PSL(2, ZMod 5) :=
    Matrix.ProjectiveSpecialLinearGroup.rank_two_simple (by norm_num)
  let : Nontrivial SL(2, ZMod 5) :=
    Function.Surjective.nontrivial (GorensteinWalter.sl2ProjectiveProjection_surjective (ZMod 5))
  let : Nontrivial B := e.nontrivial
  obtain ⟨d⟩ := projective_image_equiv_quotient_center B
    (Group.IsPerfect.not_isMulCommutative B)
  let q : B ⧸ center B ≃* SL(2, ZMod 5) ⧸ center SL(2, ZMod 5) :=
    QuotientGroup.congr _ _ e (by
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact (centerCongr e ⟨y, hy⟩).property
      · intro hx
        exact ⟨e.symm x, (centerCongr e.symm ⟨x, hx⟩).property, e.apply_symm_apply x⟩)
  obtain ⟨a⟩ := Matrix.ProjectiveSpecialLinearGroup.equiv_alternatingGroup_five
  let S := T.mapSurjective ProjGenLinGroup.mk_surjective
  apply Theory.PSL2.pgl2_prime_eq_five_of_sylow_normalizes_alternating_five
    ho hF S (B.map ProjGenLinGroup.mk) ⟨(d.trans q).trans a⟩
  exact (map_mono hTB).trans (B.le_normalizer_map ProjGenLinGroup.mk)

end Matrix.GeneralLinearGroup
