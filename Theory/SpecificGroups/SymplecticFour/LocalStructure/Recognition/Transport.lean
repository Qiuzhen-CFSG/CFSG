module

public import Theory.SpecificGroups.SymplecticFour.LocalStructure.Recognition.Basic

/-!
# Transport of natural extension data

An actual multiplicative equivalence pulls back the kernel, the central
quotient, and the conjugation formula. This permits recognition inside a
local overgroup without imposing normality in any larger ambient group.

Source: intrinsic block convention in Aschbacher–Smith C.1.7/C.1.12.
-/

public section

open scoped IsMulCommutative
namespace Theory.SpecificGroups.SymplecticFour.NaturalExtension
variable {F L H : Type*} [Field F] [Group L] [Group H]
variable {Q : Subgroup L} [Q.Normal] (d : NaturalExtension (F := F) Q)

private def kernelEquiv (e : H ≃* L) : Q.comap e.toMonoidHom ≃* Q where
  toFun x := ⟨e x, x.property⟩
  invFun x := ⟨e.symm x, by
    change e (e.symm x) ∈ Q
    simpa only [e.apply_symm_apply] using x.property⟩
  left_inv x := by ext; simp
  right_inv x := by ext; simp
  map_mul' x y := Subtype.ext (e.map_mul x y)

private theorem center_mem (e : H ≃* L) (x : H) :
    e x ∈ Subgroup.center L ↔ x ∈ Subgroup.center H := by
  simp only [Subgroup.mem_center_iff]
  constructor
  · intro h y
    apply e.injective
    simpa only [map_mul] using h (e y)
  · intro h y
    obtain ⟨y, rfl⟩ := e.surjective y
    simpa only [map_mul] using congrArg e (h y)

omit [Q.Normal] in
private theorem fixed_map (e : H ≃* L) :
    ((Subgroup.center H).subgroupOf (Q.comap e.toMonoidHom)).map
      (kernelEquiv (Q := Q) e).toMonoidHom = (Subgroup.center L).subgroupOf Q := by
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    exact (center_mem e x).mpr hx
  · intro x hx
    refine ⟨(kernelEquiv (Q := Q) e).symm x, ?_, MulEquiv.apply_symm_apply _ x⟩
    apply (center_mem e (e.symm x)).mp
    change (x : L) ∈ Subgroup.center L at hx
    simpa only [e.apply_symm_apply] using hx

/-- Pull back all extension data along an actual group isomorphism. Normality
is in the new local group, never in a larger ambient group. -/
noncomputable def comap (e : H ≃* L) :
    NaturalExtension (F := F) (Q.comap e.toMonoidHom) := by
  let := d.elementary
  let k := kernelEquiv (Q := Q) e
  refine {
    elementary := ?_
    projection := d.projection.comp e.toMonoidHom
    surjective := d.surjective.comp e.surjective
    kernel := ?_
    commutator_eq := ?_
    moduleIso := (QuotientGroup.congr _ _ k (fixed_map e)).trans d.moduleIso
    intertwining := ?_
  }
  · refine { toIsMulCommutative := ⟨⟨fun a b => ?_⟩⟩, exponent_dvd_p := ?_ }
    · apply k.injective
      simp only [map_mul, mul_comm]
    · apply Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr
      intro a
      apply k.injective
      rw [map_pow, map_one]
      exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
        (IsElementaryAbelian.exponent_dvd_p 2 Q) (k a)
  · rw [← MonoidHom.comap_ker, d.kernel]
  · apply Subgroup.map_injective (f := e.toMonoidHom) e.injective
    rw [Subgroup.map_commutator, Subgroup.map_top_of_surjective _ e.surjective,
      Subgroup.map_comap_eq_self_of_surjective e.surjective, d.commutator_eq]
  · intro l u
    have he : k (extensionConjugate (Q.comap e.toMonoidHom) l u) =
        extensionConjugate Q (e l) (k u) := by
      apply Subtype.ext
      change e (l * (u : H) * l⁻¹) = e l * e (u : H) * (e l)⁻¹
      simp only [map_mul, map_inv]
    change Multiplicative.toAdd (d.moduleIso (QuotientGroup.mk' _
      (k (extensionConjugate (Q.comap e.toMonoidHom) l u)))) = _
    rw [he]
    exact d.intertwining (e l) (k u)
end Theory.SpecificGroups.SymplecticFour.NaturalExtension
