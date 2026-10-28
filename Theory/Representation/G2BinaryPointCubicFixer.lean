module
public import Theory.AtlasPort.LinearGroups.G2.BinaryParabolicPair.PointCubicFixer
public import Theory.Representation.G2BinaryPointMarking

/-!
# Natural-coordinate transport of the binary point-parabolic obstruction

Mark the given nonzero vector by conjugating both the group and module
coordinates. The actual point stabilizer maps onto the standard point
parabolic. An involution fixing that vector cannot centralize every
order-three element of the point stabilizer in the derived subgroup.

The original HS application is `SourceAction.G2Exclusion.source_no_caseSix`.
Source: Aschbacher--Smith 14.3.32, printed pp.1003--1004.
-/

public section
namespace Atlas.G2.Natural.BinaryPointFlag
open Subgroup Representation
variable {D V : Type*} [Group D] [AddCommGroup V] [Module (ZMod 2) V]

/-- Transport the point-parabolic obstruction through actual natural coordinates. -/
theorem eq_one_of_point_cubic_fixer
    (ρ : Representation (ZMod 2) D V)
    (e : D ≃* Model F) (c : V ≃ₗ[F] Natural.Space F)
    (he : ∀ a w, c (ρ a w)=Natural.action F (e a) (c w))
    (v : V) (hv : v≠0) (z : D) (hz : ρ z v=v) (hz2 : z^2=1)
    (hfix : ∀ a : D, ρ a v=v → a∈commutator D → a^3=1 → z*a=a*z) : z=1 := by
  let C : Subgroup D := {
    carrier := {a | ρ a v=v}
    one_mem' := by simp
    mul_mem' := by
      intro a b ha hb
      change ρ a v=v at ha
      change ρ b v=v at hb
      change ρ (a*b) v=v
      rw [map_mul,Module.End.mul_apply,hb,ha]
    inv_mem' := by
      intro a ha
      change ρ a v=v at ha
      change ρ a⁻¹ v=v
      have hh := congrArg (ρ a⁻¹) ha
      simpa only [← Module.End.mul_apply,← map_mul,inv_mul_cancel,map_one,
        Module.End.one_apply] using hh.symm }
  let : IsElementaryAbelian 2 (⊥ : Subgroup D) := {
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr
      (fun _ => Subsingleton.elim _ _) }
  obtain ⟨f,_,hf,_,_,hC,_,_⟩ := exists_compatible_point_marking ρ e.toMonoidHom
    e.injective (by rw [MonoidHom.range_eq_top.mpr e.surjective]; exact le_top)
    c.toLinearMap c.surjective he C ⊥ bot_le le_normalizer_of_normal v (by
      intro hh; exact hv (c.injective (hh.trans c.map_zero.symm)))
    (by intro a; change ρ a v=v ↔ Natural.action F (e a) (c v)=c v
        rw [← he,c.injective.eq_iff])
  have hfs : Function.Surjective f := (hf.bijective_of_nat_card_le
    (Nat.card_congr e.toEquiv).ge).surjective
  have hCP : C.map f = BinaryCore.secondParabolic := by
    rw [hC,MonoidHom.range_eq_top.mpr hfs,inf_top_eq]
  have hderived : (commutator D).map f = commutator (Model F) := by
    rw [map_commutator_eq,MonoidHom.range_eq_top.mpr hfs,commutator_def]
  have hfe : f z=1 := BinaryParabolicPair.point_involution_eq_one_of_cubic_fixer
    (f z) (hCP ▸ mem_map_of_mem f hz) (by rw [←map_pow,hz2,map_one]) (by
      intro a ha had ha3
      obtain ⟨b,rfl⟩ := hfs a
      have hb : b∈C := by
        have hh : f b∈C.map f := hCP.symm ▸ ha
        obtain ⟨b',hb',he'⟩ := hh
        exact hf he' ▸ hb'
      have hbd : b∈commutator D := by
        have hh : f b∈(commutator D).map f := hderived.symm ▸ had
        obtain ⟨b',hb',he'⟩ := hh
        exact hf he' ▸ hb'
      have hb3 : b^3=1 := hf (by simpa only [map_pow,map_one] using ha3)
      simpa only [map_mul] using congrArg f (hfix b hb hbd hb3))
  exact hf (hfe.trans f.map_one.symm)
end Atlas.G2.Natural.BinaryPointFlag
