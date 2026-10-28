module
public import Theory.Representation.BinaryOffender.SchurNormalizerDisplacement
public import Theory.Representation.FiniteFieldSemilinearDisplacement.Saturation

/-!
# Strict Schur displacement for elementary actors of rank greater than one

Conjugation constructs the literal normalizer action on the original Schur field.
Its kernel is exactly Schur linearity. Equality in the half-space displacement
bound would make the whole elementary actor inject into this field's cyclic
automorphism group; hence every larger actor has strictly greater displacement.

The Chapter D Hermitian-square application uses the full preserving actor,
including both nonzero component kernels.
Source: Aschbacher--Smith D.3.7, pp.198--199, and Guralnick--Malle,
Classification of 2F-modules II, Section 3.5, equations (3.3)--(3.5).
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender
open scoped MonoidAlgebra
namespace Representation.BinaryOffender.SchurNormalizer
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V)

private def conjugateMap (t : linearNormalizer ρ) (f : IntertwiningMap ρ ρ) :
    IntertwiningMap ρ ρ where
  toLinearMap := t.val.val * f.toLinearMap * (↑t.val⁻¹ : Module.End (ZMod 2) V)
  isIntertwining' := by
    intro g
    obtain ⟨h, hh⟩ := (Subgroup.mem_normalizer_iff''.mp t.property
      (ρ.asGroupHom g)).mp ⟨g, rfl⟩
    have he : ρ h = (↑t.val⁻¹ : Module.End (ZMod 2) V) * ρ g * t.val.val :=
      congrArg Units.val hh
    have hf : f.toLinearMap * ρ h = ρ h * f.toLinearMap := f.isIntertwining' h
    have hc := congrArg (fun a : Module.End (ZMod 2) V =>
      t.val.val * a * (↑t.val⁻¹ : Module.End (ZMod 2) V)) hf
    change (_ * _ * _) * ρ g = ρ g * (_ * _ * _)
    simpa [he, mul_assoc] using hc

private theorem conjugateMap_apply (t : linearNormalizer ρ) (f : IntertwiningMap ρ ρ) (v : V) :
    conjugateMap ρ t f v = t.val.val (f ((↑t.val⁻¹ : Module.End (ZMod 2) V) v)) := rfl

private def conjugateEquiv (t : linearNormalizer ρ) :
    IntertwiningMap ρ ρ ≃+* IntertwiningMap ρ ρ where
  toFun := conjugateMap ρ t
  invFun := conjugateMap ρ t⁻¹
  left_inv f := by
    ext v
    simp only [conjugateMap_apply]
    change (↑t.val⁻¹ : Module.End (ZMod 2) V)
      (t.val.val (f ((↑t.val⁻¹ : Module.End (ZMod 2) V) (t.val.val v)))) = f v
    simp only [←Module.End.mul_apply,Units.inv_mul,Module.End.one_apply]
  right_inv f := by
    ext v
    simp only [conjugateMap_apply]
    change t.val.val ((↑t.val⁻¹ : Module.End (ZMod 2) V)
      (f (t.val.val ((↑t.val⁻¹ : Module.End (ZMod 2) V) v)))) = f v
    simp only [←Module.End.mul_apply,Units.mul_inv,Module.End.one_apply]
  map_add' f g := by
    ext v
    change t.val.val (f ((↑t.val⁻¹ : Module.End (ZMod 2) V) v) +
      g ((↑t.val⁻¹ : Module.End (ZMod 2) V) v)) = _
    exact map_add _ _ _
  map_mul' f g := by
    ext v
    change t.val.val (f (g ((↑t.val⁻¹ : Module.End (ZMod 2) V) v))) =
      t.val.val (f ((↑t.val⁻¹ : Module.End (ZMod 2) V)
        (t.val.val (g ((↑t.val⁻¹ : Module.End (ZMod 2) V) v)))))
    simp only [←Module.End.mul_apply,Units.inv_mul,Module.End.one_apply]

/-- The actual conjugation action on the original Schur ring. -/
def coefficientAction : linearNormalizer ρ →*
    (Module.End (ZMod 2)[G] ρ.asModule ≃+* Module.End (ZMod 2)[G] ρ.asModule) where
  toFun t := (IntertwiningMap.equivAlgEnd ρ).symm.toRingEquiv.trans
    ((conjugateEquiv ρ t).trans (IntertwiningMap.equivAlgEnd ρ).toRingEquiv)
  map_one' := by
    ext f v
    change (1 : Module.End (ZMod 2) V) (f ((1 : Module.End (ZMod 2) V) v)) = f v
    rfl
  map_mul' a b := by
    ext f v
    change (a.val.val * b.val.val) (f
      (((↑b.val⁻¹ : Module.End (ZMod 2) V) * (↑a.val⁻¹ : Module.End (ZMod 2) V)) v)) = _
    rfl

/-- Conjugation gives the actual semilinearity equation on the unchanged carrier. -/
theorem coefficientAction_apply (t : linearNormalizer ρ)
    (c : Module.End (ZMod 2)[G] ρ.asModule) (v : ρ.asModule) :
    ρ.asModuleEquiv.symm (t.val.val (ρ.asModuleEquiv (c • v))) =
      coefficientAction ρ t c • ρ.asModuleEquiv.symm (t.val.val (ρ.asModuleEquiv v)) := by
  apply ρ.asModuleEquiv.injective
  let f := (IntertwiningMap.equivAlgEnd ρ).symm c
  change t.val.val (f (ρ.asModuleEquiv v)) = t.val.val (f ((↑t.val⁻¹ : Module.End (ZMod 2) V) (t.val.val (ρ.asModuleEquiv v))))
  simp only [←Module.End.mul_apply,Units.inv_mul,Module.End.one_apply]

/-- The coefficient kernel is precisely Schur linearity. -/
theorem coefficientAction_eq_one_iff (t : linearNormalizer ρ) :
    coefficientAction ρ t = 1 ↔ IsSchurLinear ρ t := by
  constructor
  · intro h
    apply (isSchurLinear_iff_endField ρ t).mpr
    intro c v
    have hh := coefficientAction_apply ρ t c v
    rw [h] at hh
    exact congrArg ρ.asModuleEquiv hh
  · intro h
    ext c v
    apply ρ.asModuleEquiv.injective
    let f := (IntertwiningMap.equivAlgEnd ρ).symm c
    change t.val.val (f ((↑t.val⁻¹ : Module.End (ZMod 2) V) (ρ.asModuleEquiv v))) = f (ρ.asModuleEquiv v)
    rw [h f,←Module.End.mul_apply,Units.mul_inv,Module.End.one_apply]

variable [FiniteDimensional (ZMod 2) V] [IsIrreducible ρ]

/-- If an elementary actor moves the Schur field but fixes at least half the
binary space, it is cyclic of order at most two. -/
theorem rank_le_one_of_half_fixed (A : Subgroup (linearNormalizer ρ))
    [Finite A] [IsElementaryAbelian 2 A]
    (t : linearNormalizer ρ) (ht : t ∈ A) (hlin : ¬ IsSchurLinear ρ t)
    (hd : 2 * fixedCodim (normalizerRepresentation ρ) A ≤ Module.finrank (ZMod 2) V) :
    rank A ≤ 1 := by
  let ψ := ρ.asModuleEquiv.symm.conjRingEquiv.toMonoidHom.comp (normalizerRepresentation ρ)
  have hf : Function.Injective ψ := ρ.asModuleEquiv.symm.conjRingEquiv.injective.comp
    (fun a b hh => Subtype.ext (Units.ext hh))
  have hcodim : fixedCodim (normalizerRepresentation ρ) A = fixedCodim ψ A := by
    simpa only [Subgroup.map_id] using fixedCodim_map_equivariant
      (normalizerRepresentation ρ) ψ (MonoidHom.id _) ρ.asModuleEquiv.symm (fun _ _ => rfl) A
  have hn : coefficientAction ρ t ≠ 1 := by
    intro he
    exact hlin ((coefficientAction_eq_one_iff ρ t).mp he)
  apply FiniteFieldSemilinearDisplacement.rank_le_one_of_half_fixed ψ hf
    (coefficientAction ρ) (coefficientAction_apply ρ) A ht hn
  rw [←hcodim,ρ.asModuleEquiv.finrank_eq]
  exact hd

/-- A larger elementary actor moving the Schur field has strictly more than
half the full binary degree as displacement. -/
theorem finrank_lt_twice_fixedCodim (A : Subgroup (linearNormalizer ρ))
    [Finite A] [IsElementaryAbelian 2 A] (hr : 1 < rank A)
    (t : linearNormalizer ρ) (ht : t ∈ A) (hlin : ¬ IsSchurLinear ρ t) :
    Module.finrank (ZMod 2) V < 2 * fixedCodim (normalizerRepresentation ρ) A := by
  by_contra! hh
  exact (not_le_of_gt hr) (rank_le_one_of_half_fixed ρ A t ht hlin hh)
end Representation.BinaryOffender.SchurNormalizer
