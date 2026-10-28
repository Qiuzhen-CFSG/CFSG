module

public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Short.LocalA5.SourceConstruction.Geometry.Extension.RootJ2Alignment.SubgroupPlacement.CubicGeometry.Fusion.Ambient.OctadLocalFusion.Image.SelectedFusion.GeometryInterface
public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Short.LocalA5.SourceConstruction.Geometry.Extension.RootJ2Alignment.SubgroupPlacement.CubicGeometry.Fusion.Ambient.OctadLocalFusion.Image.SelectedFusion.PlaneFusion.OmegaGeometry
public import Mathlib.FieldTheory.Finiteness
public import Mathlib.GroupTheory.Index

/-!
# Quaternion commutators give anisotropic moved planes

The actual quotient coordinates send `[action.ker, ⟨r⟩]` onto the range of
`M.orthogonalAction r - 1`. This is proved using the ambient commutator
convention, then all powers of the actor, rather than changing actions.

On a quaternion commutator the coordinate kernel is exactly its square-one
subgroup: every square-one element of Q₈ is a square, and the binary vector
image kills squares. Conversely, the model's square-form identity detects
square-one elements in the coordinate kernel. Thus the image has four vectors,
its dimension is two, and every nonzero vector is anisotropic. Extraspeciality
and the actor's order are not needed for this implication.

The final theorem applies this result to two cubics and the proved conjugacy
of their cyclic subgroups inside the specified Siegel-generated Omega subgroup.
The model's exact image and two-group kernel then lift this conjugacy to literal
octad image fusion. Only the structural `OrthogonalModel` remains an input;
its construction belongs to the source-theorem assembly.

Source: Aschbacher, *Sporadic Groups* (1994), 25.1–25.5 and the quaternion
commutator definition of Δ_H in §46, printed p.251 (PDF p.131).
-/

@[expose] public noncomputable section
open Theory.AlgebraicGroup
open scoped commutatorElement
namespace Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.LocalA5.SourceConstruction.CubicFusion.OctadRestriction

namespace OrthogonalModel

/-- The quotient coordinates, evaluated on the actual restriction kernel. -/
def kernelCoordinates (M : OrthogonalModel) : action.ker →* Multiplicative SelectedGeometry.Space :=
  M.coordinates.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center action.ker))

theorem kernelCoordinates_surjective (M : OrthogonalModel) :
    Function.Surjective M.kernelCoordinates :=
  M.coordinates.surjective.comp (QuotientGroup.mk'_surjective _)

theorem kernelCoordinates_conj (M : OrthogonalModel) (r : centralizer) (k : action.ker) :
    (M.kernelCoordinates (MulAut.conjNormal r k)).toAdd =
      (M.orthogonalAction r).val (M.kernelCoordinates k).toAdd := by
  exact congrArg Multiplicative.toAdd
    ((congrArg M.coordinates (kernelQuotientAction_mk r k)).symm.trans (M.equivariant r k))

/-- Restriction of the quotient coordinates to the literal ambient commutator. -/
def commutatorCoordinates (M : OrthogonalModel) (r : centralizer) :
    kernelCommutator r →* Multiplicative SelectedGeometry.Space :=
  M.kernelCoordinates.comp (Subgroup.inclusion (kernelCommutator_le r))

end OrthogonalModel

namespace SelectedGeometry

theorem pow_sub_mem_movedSpace (a : Orthogonal) (n : ℕ) (v : Space) :
    (a ^ n).val v - v ∈ movedSpace a := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hd : a.val ((a ^ n).val v) - (a ^ n).val v ∈ movedSpace a :=
      LinearMap.mem_range_self (a.val.toLinearMap - LinearMap.id) _
    have hh := (movedSpace a).add_mem hd ih
    simpa only [sub_add_sub_cancel, pow_succ', Subgroup.coe_mul, LinearEquiv.mul_apply] using hh

end SelectedGeometry

namespace OrthogonalModel

private theorem coordinate_commutator (M : OrthogonalModel) (r : centralizer)
    (k : action.ker) :
    M.kernelCoordinates (k * (MulAut.conjNormal r k)⁻¹) =
      Multiplicative.ofAdd ((M.kernelCoordinates k).toAdd -
        (M.orthogonalAction r).val (M.kernelCoordinates k).toAdd) := by
  apply Multiplicative.toAdd.injective
  simp only [map_mul, map_inv, toAdd_mul, toAdd_inv,
    kernelCoordinates_conj, toAdd_ofAdd, sub_eq_add_neg]

/-- Coordinates of the ambient commutator are exactly the moved space. -/
theorem mem_movedSpace_iff (M : OrthogonalModel) (r : centralizer)
    (v : SelectedGeometry.Space) :
    v ∈ SelectedGeometry.movedSpace (M.orthogonalAction r) ↔
      Multiplicative.ofAdd v ∈ (M.commutatorCoordinates r).range := by
  classical
  let U := SelectedGeometry.movedSpace (M.orthogonalAction r)
  let P := (U.toAddSubgroup.toSubgroup.comap M.kernelCoordinates).map action.ker.subtype
  have hcomm : kernelCommutator r ≤ P := by
    apply Subgroup.commutator_le.mpr
    intro k hk s hs
    obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp
      (((isOfFinOrder_of_finite r).mem_zpowers_iff_mem_range_orderOf).mp hs)
    let k' : action.ker := ⟨k, hk⟩
    refine Subgroup.mem_map.mpr ⟨k' * (MulAut.conjNormal (r ^ n) k')⁻¹, ?_, ?_⟩
    · change (M.kernelCoordinates (k' * (MulAut.conjNormal (r ^ n) k')⁻¹)).toAdd ∈ U
      rw [coordinate_commutator]
      change (M.kernelCoordinates k').toAdd -
        (M.orthogonalAction (r ^ n)).val (M.kernelCoordinates k').toAdd ∈ U
      rw [map_pow]
      simpa only [neg_sub] using U.neg_mem
        (SelectedGeometry.pow_sub_mem_movedSpace (M.orthogonalAction r) n (M.kernelCoordinates k').toAdd)
    · change k * (r ^ n * k * (r ^ n)⁻¹)⁻¹ = ⁅k, r ^ n⁆
      simp only [commutatorElement_def, mul_inv_rev, inv_inv]
      group
  constructor
  · rintro ⟨w, rfl⟩
    obtain ⟨k, hk⟩ := M.kernelCoordinates_surjective (Multiplicative.ofAdd w)
    let c : kernelCommutator r := ⟨⁅r, k.val⁆, by
      rw [kernelCommutator, Subgroup.commutator_comm]
      exact Subgroup.commutator_mem_commutator (Subgroup.mem_zpowers _) k.prop⟩
    refine ⟨c, ?_⟩
    have he : (Subgroup.inclusion (kernelCommutator_le r)) c =
        MulAut.conjNormal r k * k⁻¹ := by
      apply Subtype.ext
      rfl
    change M.kernelCoordinates ((Subgroup.inclusion (kernelCommutator_le r)) c) = _
    rw [he]
    apply Multiplicative.toAdd.injective
    simp only [map_mul, map_inv, toAdd_mul, toAdd_inv,
      kernelCoordinates_conj, hk, toAdd_ofAdd]
    exact (sub_eq_add_neg _ _).symm
  · rintro ⟨c, hc⟩
    obtain ⟨k, hk, he⟩ := Subgroup.mem_map.mp (hcomm c.prop)
    have he' : k = (Subgroup.inclusion (kernelCommutator_le r)) c := Subtype.ext he
    rw [he'] at hk
    change (M.commutatorCoordinates r c).toAdd ∈ U at hk
    simpa only [hc, toAdd_ofAdd] using hk

end OrthogonalModel
namespace OrthogonalModel

private theorem quaternion_square_roots :
    ∀ x : QuaternionGroup 2, x ^ 2 = 1 → ∃ y, x = y ^ 2 := by decide +kernel

private theorem coordinate_square (M : OrthogonalModel) (r : centralizer)
    (c : kernelCommutator r) : M.commutatorCoordinates r (c ^ 2) = 1 := by
  rw [map_pow, pow_two]
  apply Multiplicative.toAdd.injective
  exact ZModModule.add_self _

/-- The coordinate kernel on a quaternion commutator is its two square-one elements. -/
theorem commutatorCoordinates_eq_one_iff (M : OrthogonalModel) (r : centralizer)
    (hQ : QuaternionCubic r) (c : kernelCommutator r) :
    M.commutatorCoordinates r c = 1 ↔ c ^ 2 = 1 := by
  obtain ⟨e⟩ := hQ
  constructor
  · intro hc
    have hz : SelectedGeometry.form
        (M.kernelCoordinates ((Subgroup.inclusion (kernelCommutator_le r)) c)).toAdd = 0 := by
      change SelectedGeometry.form (M.commutatorCoordinates r c).toAdd = 0
      rw [hc]
      exact map_zero _
    have hs := (M.square_zero_iff ((Subgroup.inclusion (kernelCommutator_le r)) c)).mp hz
    apply Subtype.ext
    exact congrArg (fun x : action.ker => x.val) hs
  · intro hc
    obtain ⟨y, hy⟩ := quaternion_square_roots (e c) (by simpa only [map_pow, map_one] using congrArg e hc)
    have he : c = (e.symm y) ^ 2 := e.injective (by simpa only [map_pow, e.apply_symm_apply] using hy)
    rw [he]
    exact M.coordinate_square r _

/-- The actual ambient quaternion commutator has four vectors in its coordinate image. -/
theorem commutatorCoordinates_range_card (M : OrthogonalModel) (r : centralizer)
    (hQ : QuaternionCubic r) : Nat.card (M.commutatorCoordinates r).range = 4 := by
  obtain ⟨e⟩ := hQ
  have hker : Nat.card (M.commutatorCoordinates r).ker = 2 := by
    let ek : (M.commutatorCoordinates r).ker ≃ {x : QuaternionGroup 2 // x ^ 2 = 1} :=
      e.toEquiv.subtypeEquiv (fun x => by
        change M.commutatorCoordinates r x = 1 ↔ (e x) ^ 2 = 1
        rw [M.commutatorCoordinates_eq_one_iff r ⟨e⟩, ← map_pow, ← e.map_one, e.injective.eq_iff])
    rw [Nat.card_congr ek, Nat.card_eq_fintype_card]
    decide +kernel
  have hcard : Nat.card (kernelCommutator r) = 8 := by
    rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, QuaternionGroup.card]
  have hi := (M.commutatorCoordinates r).ker.card_mul_index
  rw [Subgroup.index_ker, hker, hcard] at hi
  omega

/-- The square form of a quaternion commutator makes its moved plane anisotropic. -/
theorem anisotropicPlane_of_quaternionCubic (M : OrthogonalModel) (r : centralizer)
    (hQ : QuaternionCubic r) : SelectedGeometry.AnisotropicPlane (M.orthogonalAction r) := by
  let U := SelectedGeometry.movedSpace (M.orthogonalAction r)
  let e : (M.commutatorCoordinates r).range ≃ U :=
    { toFun := fun x => ⟨x.val.toAdd, (M.mem_movedSpace_iff r _).mpr x.prop⟩
      invFun := fun v => ⟨Multiplicative.ofAdd v.val, (M.mem_movedSpace_iff r _).mp v.prop⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  refine ⟨?_, ?_⟩
  · have hc : Nat.card U = 4 := (Nat.card_congr e).symm.trans
      (M.commutatorCoordinates_range_card r hQ)
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod] at hc
    exact Nat.pow_right_injective (by decide : 2 ≤ 2) hc
  · intro v hv hv0 hq
    obtain ⟨c, hc⟩ := (M.mem_movedSpace_iff r v).mp hv
    have hs : c ^ 2 = 1 := by
      have hh := (M.square_zero_iff ((Subgroup.inclusion (kernelCommutator_le r)) c)).mp
        (by change SelectedGeometry.form (M.commutatorCoordinates r c).toAdd = 0; simpa only [hc, toAdd_ofAdd] using hq)
      apply Subtype.ext
      exact congrArg (fun x : action.ker => x.val) hh
    have hz := (M.commutatorCoordinates_eq_one_iff r hQ c).mpr hs
    rw [hc] at hz
    exact hv0 (congrArg Multiplicative.toAdd hz)

end OrthogonalModel

namespace SelectedGeometry

/-- Cyclic cubic fusion must take place in the actual Siegel-generated subgroup. -/
def AnisotropicCubicFusion : Prop :=
  ∀ a b : Orthogonal, a ∈ omega → b ∈ omega → orderOf a = 3 → orderOf b = 3 →
    AnisotropicPlane a → AnisotropicPlane b →
    ∃ c : omega, Subgroup.zpowers a =
      (Subgroup.zpowers b).map (MulAut.conj c.val).toMonoidHom

theorem ne_one_of_anisotropicPlane (a : Orthogonal) (ha : AnisotropicPlane a) : a ≠ 1 := by
  intro h
  have hd := ha.1
  subst a
  have he : movedSpace (1 : Orthogonal) = ⊥ := by
    change LinearMap.range (LinearMap.id - LinearMap.id : Space →ₗ[ZMod 2] Space) = ⊥
    rw [sub_self, LinearMap.range_zero]
  rw [he, finrank_bot] at hd
  contradiction

end SelectedGeometry

/-- The model and the geometric Omega-fusion theorem imply literal octad image fusion.
This separates the quotient and lifting argument from the geometric conjugacy proof. -/
theorem quaternionImageFusion_of_orthogonalModel_of_plane_fusion (M : OrthogonalModel)
    (hf : SelectedGeometry.AnisotropicCubicFusion) : QuaternionImageFusion := by
  apply quaternionImageFusion_of_orthogonalModel_image_fusion M
  intro r s hr hs hqr hqs
  have hpr := M.anisotropicPlane_of_quaternionCubic r hqr
  have hps := M.anisotropicPlane_of_quaternionCubic s hqs
  have ho (t : centralizer) (ht : orderOf t = 3)
      (hp : SelectedGeometry.AnisotropicPlane (M.orthogonalAction t)) :
      orderOf (M.orthogonalAction t) = 3 := by
    have hd : orderOf (M.orthogonalAction t) ∣ 3 := ht ▸ orderOf_map_dvd M.orthogonalAction t
    rcases (Nat.dvd_prime Nat.prime_three).mp hd with h | h
    · exact (SelectedGeometry.ne_one_of_anisotropicPlane _ hp (orderOf_eq_one_iff.mp h)).elim
    · exact h
  obtain ⟨c, hc⟩ := hf (M.orthogonalAction r) (M.orthogonalAction s)
    (by rw [← M.range_eq]; exact ⟨r, rfl⟩)
    (by rw [← M.range_eq]; exact ⟨s, rfl⟩) (ho r hr hpr) (ho s hs hps) hpr hps
  exact ⟨⟨c.val, M.range_eq.symm ▸ c.prop⟩, hc⟩

/-- The actual orthogonal quotient model fuses all quaternion cubics in the literal
octad action image. No separate extraspeciality or geometric fusion premise is needed. -/
theorem quaternionImageFusion_of_orthogonalModel (M : OrthogonalModel) :
    QuaternionImageFusion :=
  quaternionImageFusion_of_orthogonalModel_of_plane_fusion M
    SelectedGeometry.anisotropic_cyclic_fusion

end Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.LocalA5.SourceConstruction.CubicFusion.OctadRestriction
