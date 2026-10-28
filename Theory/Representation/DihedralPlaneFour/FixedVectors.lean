module
public import Theory.Representation.DihedralPlaneFour
public import Theory.SpecificGroups.SL2.OddFixedVectors
/-!
# Fixed vectors for dihedral actions over four elements

Reflections have determinant of order dividing both two and three. Thus the
whole image lies in SL₂(4). A nonidentity odd element cannot fix a nonzero
vector, since the stabilizer of a nonzero natural vector is a two-group.
This applies to the actual multiplicity action in Aschbacher–Smith 8.2.8(5),
printed pp.718–719, refs/quasithin.pdf.
-/
public noncomputable section
namespace Representation
open Matrix Subgroup
open scoped MatrixGroups

/-- Every nonidentity odd element acts without nonzero fixed vectors in a faithful dihedral plane over F₄. -/
theorem dihedral_plane_four_odd_fixed_eq_zero {F : Type*} [Field F] [Finite F] [CharP F 2]
    (hF : Nat.card F = 4) {n : ℕ}
    (ρ : Representation F (DihedralGroup n) (Fin 2 → F))
    (hi : Function.Injective ρ.asGroupHom)
    (g : DihedralGroup n) (m : ℕ) (hm : Odd m) (hg : g^m = 1) (hne : g ≠ 1)
    (v : Fin 2 → F) (hv : ρ g v = v) : v = 0 := by
  let f : DihedralGroup n →* GL (Fin 2) F :=
    GeneralLinearGroup.toLin.symm.toMonoidHom.comp ρ.asGroupHom
  have hf : Function.Injective f := GeneralLinearGroup.toLin.symm.injective.comp hi
  let d := GeneralLinearGroup.det.comp f
  have hs (j : ZMod n) : d (DihedralGroup.sr j) = 1 := by
    have h2 : d (DihedralGroup.sr j)^2 = 1 := by
      rw [←map_pow,pow_two,DihedralGroup.sr_mul_self,map_one]
    have h3 : d (DihedralGroup.sr j)^3 = 1 := by
      have hh := pow_card_eq_one' (x := d (DihedralGroup.sr j))
      simpa only [Nat.card_units,hF] using hh
    exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp
      (show orderOf (d (DihedralGroup.sr j)) ∣ 1 from
        Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one h2) (orderOf_dvd_of_pow_eq_one h3)))
  have hd (g : DihedralGroup n) : f g ∈ GeneralLinearGroup.det.ker := by
    change d g = 1
    cases g with
    | sr j => exact hs j
    | r j =>
      rw [show DihedralGroup.r j = DihedralGroup.sr 0 * DihedralGroup.sr j by
        rw [DihedralGroup.sr_mul_sr,sub_zero],map_mul,hs,hs,mul_one]
  let a : SL(2,F) := ⟨(f g).val, congrArg Units.val (hd g)⟩
  have he : a.toGL = f g := Units.ext rfl
  have ha : a ^ m = 1 := by
    apply SpecialLinearGroup.toGL_injective
    rw [map_pow,he,←map_pow,hg,map_one,map_one]
  have hna : a ≠ 1 := by
    intro hh
    apply hne
    apply hf
    rw [←he,hh,map_one,map_one]
  apply Matrix.SL2.odd_power_fixed_eq_zero a m hm ha hna
  have hfρ : GeneralLinearGroup.toLin (f g) = ρ.asGroupHom g :=
    GeneralLinearGroup.toLin.apply_symm_apply _
  have hh := congrArg (fun u : LinearMap.GeneralLinearGroup F (Fin 2 → F) => u.val v) hfρ
  change (f g).val *ᵥ v = ρ g v at hh
  exact hh.trans hv
end Representation
