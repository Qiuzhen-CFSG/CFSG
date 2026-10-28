module

public import Theory.AlgebraicGroup.Parabolic.RelativeRoot.sourceRelativeRootLayer_root_mem

/-!
# Source Chevalley torus action on relative-root fibers

This module turns the geometric and linear clauses of a
`RelativeRootRepresentationSource` and its `RelativeRootFiberModule` into the
public interface needed by the full-Levi orbit argument.  A Chevalley coroot
element belongs to the chosen torus and hence to the Levi.  Its ambient
Chevalley conjugation formula descends through the fiber quotient, while the
stored linear parameter coordinate identifies multiplication of the root
parameter with scalar multiplication in the fiber module.

Thus left conjugation by the Levi point represented by `C.h β u` acts on the
root vector for `γ` by the inverse Cartan scalar
`(u ^ D.pairing γ β)⁻¹`.  Equivalently, the inverse coroot point acts by the
positive Cartan scalar.  The same canonical-coordinate calculation identifies
each root vector with a coordinate basis vector.  Consequently every nonzero
Chevalley parameter gives a nonzero fiber generator, uniformly for every
`RelativeRootFiberModule`.  These are the precise source bridges used to vary
nonzero parameters in a fixed relative-root label; they do not use the
unresolved numbered Theorem 1.14.7.
-/

universe u v

namespace Theory.AlgebraicGroup

variable {k : Type u} [Field k] [IsAlgClosed k]
variable {K : Variety k} [AlgebraicGroup K]

public section

omit [IsAlgClosed k] in
/-- Every source Chevalley coroot element is a point of the selected Levi. -/
theorem RelativeRootRepresentationSource.chevalleyTorus_mem_levi
    (S : RelativeRootRepresentationSource K) (α : S.D.Root) (t : kˣ) :
    S.C.h α t ∈ S.L :=
  S.torus_le_levi (S.chevalleyTorus_mem α t)

end

/-- The Levi point whose ambient value is the source Chevalley coroot element. -/
public noncomputable def RelativeRootRepresentationSource.chevalleyTorusLeviPoint
    (S : RelativeRootRepresentationSource K) (α : S.D.Root) (t : kˣ) :
    Variety.Point S.L.carrierVariety :=
  S.L.pointEquiv.symm ⟨S.C.h α t, S.chevalleyTorus_mem_levi α t⟩

public section

omit [IsAlgClosed k] in
/-- Inclusion of the packaged Levi point recovers the original Chevalley
coroot element. -/
theorem RelativeRootRepresentationSource.chevalleyTorusLeviPoint_include
    (S : RelativeRootRepresentationSource K) (α : S.D.Root) (t : kˣ) :
    S.L.includePoint (S.chevalleyTorusLeviPoint α t) = S.C.h α t := by
  change (S.L.pointEquiv
    (S.L.pointEquiv.symm ⟨S.C.h α t, S.chevalleyTorus_mem_levi α t⟩)).1 = _
  rw [S.L.pointEquiv.apply_symm_apply]

end

/-- The root-vector coordinate agrees with the linear parameter map stored by
the fiber model. -/
public theorem RelativeRootFiberModule.rootVector_eq_rootParameterLinear
    {S : RelativeRootRepresentationSource K} (M : RelativeRootFiberModule S)
    (γ : { γ : S.D.Root // γ ∈ relativeRootFiberAtHeight
      S.D S.coeff S.J S.height S.root }) (t : k) :
    M.rootVector (γ, t) = M.rootParameterLinear γ t := by
  rw [RelativeRootFiberModule.rootVector_value,
    ← M.rootParameterLinear_value]

/-- In canonical fiber coordinates, a root vector is the corresponding
single-coordinate vector transported by the module's linear equivalence. -/
public theorem RelativeRootFiberModule.rootVector_coordinate
    {S : RelativeRootRepresentationSource K} (M : RelativeRootFiberModule S)
    (γ : { γ : S.D.Root // γ ∈ relativeRootFiberAtHeight
      S.D S.coeff S.J S.height S.root }) (t : k) :
    M.rootVector (γ, t) = M.coordinateLinearEquiv
      (@Pi.single _ (fun _ => k) (inferInstance) (Classical.decEq _) γ t) := by
  classical
  rw [RelativeRootFiberModule.rootVector_value, M.pointEquiv_coordinate]
  have hcoord : relativeRootFiberQuotientCoordinateEquiv S
      (relativeRootFiberQuotientGenerator S (γ, t)) =
      Multiplicative.ofAdd
        (@Pi.single _ (fun _ => k) (inferInstance) (Classical.decEq _) γ t) := by
    apply relativeRootFiberCoordinateHom_injective S
    rw [relativeRootFiberCoordinateHom_equiv_apply,
      relativeRootFiberCoordinateHom_single]
  rw [hcoord]
  rfl

/-- A nonzero Chevalley parameter gives a nonzero vector in every linear
realization of the canonical relative-root fiber. -/
public theorem RelativeRootFiberModule.rootVector_ne_zero
    {S : RelativeRootRepresentationSource K} (M : RelativeRootFiberModule S)
    (γ : { γ : S.D.Root // γ ∈ relativeRootFiberAtHeight
      S.D S.coeff S.J S.height S.root }) {t : k} (ht : t ≠ 0) :
    M.rootVector (γ, t) ≠ 0 := by
  classical
  rw [M.rootVector_coordinate]
  intro h
  have h0 : M.coordinateLinearEquiv
      (@Pi.single _ (fun _ => k) (inferInstance) (Classical.decEq _) γ t) =
      M.coordinateLinearEquiv 0 := by simpa using h
  have h' := congrArg (fun x => x γ) (M.coordinateLinearEquiv.injective h0)
  exact ht (by simpa [Pi.single_eq_same] using h')

/-- Root vectors depend additively on the Chevalley parameter. -/
public theorem RelativeRootFiberModule.rootVector_add
    {S : RelativeRootRepresentationSource K} (M : RelativeRootFiberModule S)
    (γ : { γ : S.D.Root // γ ∈ relativeRootFiberAtHeight
      S.D S.coeff S.J S.height S.root }) (a b : k) :
    M.rootVector (γ, a + b) = M.rootVector (γ, a) + M.rootVector (γ, b) := by
  rw [M.rootVector_eq_rootParameterLinear,
    M.rootVector_eq_rootParameterLinear,
    M.rootVector_eq_rootParameterLinear, map_add]

/-- Root vectors are homogeneous for the full ground-field scalar action. -/
public theorem RelativeRootFiberModule.rootVector_smul
    {S : RelativeRootRepresentationSource K} (M : RelativeRootFiberModule S)
    (γ : { γ : S.D.Root // γ ∈ relativeRootFiberAtHeight
      S.D S.coeff S.J S.height S.root }) (c t : k) :
    M.rootVector (γ, c * t) = c • M.rootVector (γ, t) := by
  rw [M.rootVector_eq_rootParameterLinear,
    M.rootVector_eq_rootParameterLinear,
    show c * t = c • t by rw [smul_eq_mul], map_smul]

/-- The zero Chevalley parameter gives the zero fiber vector. -/
public theorem RelativeRootFiberModule.rootVector_zero
    {S : RelativeRootRepresentationSource K} (M : RelativeRootFiberModule S)
    (γ : { γ : S.D.Root // γ ∈ relativeRootFiberAtHeight
      S.D S.coeff S.J S.height S.root }) :
    M.rootVector (γ, 0) = 0 := by
  simpa using M.rootVector_smul γ 0 0

/-- A source Chevalley coroot, viewed as a Levi point, acts by the inverse
Cartan scalar under the left-conjugation convention. -/
public theorem RelativeRootFiberModule.chevalleyTorus_action_rootVector
    (S : RelativeRootRepresentationSource K) (M : RelativeRootFiberModule S)
    (β : S.D.Root) (u : kˣ)
    (γ : { γ : S.D.Root // γ ∈ relativeRootFiberAtHeight
      S.D S.coeff S.J S.height S.root }) (t : k) :
    (M.representation.action (S.chevalleyTorusLeviPoint β u)).1
        (M.rootVector (γ, t)) =
      (((u : k) ^ S.D.pairing γ.1 β)⁻¹) • M.rootVector (γ, t) := by
  let l := S.chevalleyTorusLeviPoint β u
  let c : k := ((u : k) ^ S.D.pairing γ.1 β)⁻¹
  have hl : S.L.includePoint l = S.C.h β u :=
    S.chevalleyTorusLeviPoint_include β u
  have hmul := S.chevalleySystem.2.2.2.2.2.2.1
  have hone : S.C.h β 1 = 1 := by
    apply mul_left_cancel (a := S.C.h β 1)
    simpa only [mul_one] using hmul β 1 1
  have hinv : S.C.h β u⁻¹ = (S.C.h β u)⁻¹ := by
    apply eq_inv_iff_mul_eq_one.mpr
    rw [hmul]
    simp only [inv_mul_cancel, hone]
  have hconj : S.C.h β u * S.C.x γ.1 t * (S.C.h β u)⁻¹ =
      S.C.x γ.1 (c * t) := by
    rcases S.chevalleySystem with
      ⟨_, _, _, _, _, _, _, _, _, _, _, haction, _, _⟩
    have h := haction γ.1 β t u⁻¹
    rw [hinv, inv_inv] at h
    simpa only [c, Units.val_inv_eq_inv_val, inv_zpow] using h
  have hgenerator : M.conjugatedGenerator l (γ, t) =
      relativeRootFiberQuotientGenerator S (γ, c * t) := by
    apply Subtype.ext
    rcases M.conjugatedGenerator_value l (γ, t) with ⟨y, hy, hqy⟩
    rw [hqy, relativeRootFiberQuotientGenerator_coe]
    congr 1
    apply Subtype.ext
    rw [hy, hl, hconj]
    exact (relativeRootLayerElement_coe S γ.1 γ.2 (c * t)).symm
  have hagree := M.representation_agrees_with_conjugation l
    (relativeRootFiberQuotientGenerator S (γ, t))
  rw [M.conjugationAction_generator, hgenerator] at hagree
  have haction :
      (M.representation.action l).1 (M.rootVector (γ, t)) =
        M.rootVector (γ, c * t) := by
    have h := congrArg Multiplicative.toAdd hagree.symm
    rw [toAdd_ofAdd] at h
    simpa only [RelativeRootFiberModule.rootVector_value] using h
  rw [haction, M.rootVector_smul]

/-- Compatibility form with the positive Cartan scalar: the inverse coroot
parameter acts by `u ^ D.pairing γ β`. -/
public theorem RelativeRootFiberModule.chevalleyTorus_inv_action_rootVector
    (S : RelativeRootRepresentationSource K) (M : RelativeRootFiberModule S)
    (β : S.D.Root) (u : kˣ)
    (γ : { γ : S.D.Root // γ ∈ relativeRootFiberAtHeight
      S.D S.coeff S.J S.height S.root }) (t : k) :
    (M.representation.action (S.chevalleyTorusLeviPoint β u⁻¹)).1
        (M.rootVector (γ, t)) =
      ((u : k) ^ S.D.pairing γ.1 β) • M.rootVector (γ, t) := by
  simpa only [Units.val_inv_eq_inv_val, inv_zpow, inv_inv] using
    M.chevalleyTorus_action_rootVector S β u⁻¹ γ t

end Theory.AlgebraicGroup
