module

public import Theory.SpecificGroups.PSL3Four.CentralCover.GraphField
public import Theory.GroupAction.NormalizerFixedCentralizer
public import Theory.PPrimeCore
public import Mathlib.GroupTheory.Sylow

/-!
# The marked overgroup of the perfect four-cover

The overgroup acts by actual conjugation on its normal four-cover. Its
projective action has the full standard diagonal, graph and field image.
The normalizer data retain the selected Sylow three-subgroup and the selected
involutions, with coordinates in S₃ × S₃. Separate conjugacies identify the
graph and field representatives; simultaneous standard coordinates are not
assumed.

The intrinsic two-residual of C_L(τf) is embedded in C_I(τf), and its E₉ model
gives a normal odd subgroup there. Identifying the entire odd core and the
larger Sylow three-subgroup still requires the action on this residual.

Source: Aschbacher--Smith 15.3.38, printed pp.1136--1137, manuscript of
1 March 2004. The centralizer involving V₁ is a different group.
-/

public section

namespace Matrix.PSL3Four.ExtendedCentralizer
open Subgroup

abbrev ElementaryNine := Multiplicative (Fin 2 → ZMod 3)
abbrev SymmetricThree := Equiv.Perm (Fin 3)

@[expose] def rotation : SymmetricThree := Equiv.swap 0 1 * Equiv.swap 1 2
@[expose] def reflection : SymmetricThree := Equiv.swap 0 1

private theorem reflection_inverts_rotation (x : SymmetricThree) (hx : x ∈ zpowers rotation) :
    reflection * x * reflection⁻¹ = x⁻¹ := by
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hx
  change (MulAut.conj reflection) (rotation ^ k) = (rotation ^ k)⁻¹
  rw [map_zpow]
  have h : (MulAut.conj reflection) rotation = rotation⁻¹ := by decide
  rw [h, inv_zpow]

variable {I : Type*} [Group I] (L : Subgroup I) [L.Normal]

/-- Descent of actual overgroup conjugation through the specified cover. -/
@[expose] noncomputable def projectiveAction (c : FourCover L) : I →* MulAut PSL :=
  (c.toCover.autMap c.ker_eq_center).comp (MulAut.conjNormal : I →* MulAut L)

/-- The source overgroup, with its actual normal inclusion and full quotient action. -/
structure Overgroup where
  cover : FourCover L
  centralizer_eq : centralizer (L : Set I) = (center L).map L.subtype
  full_action : (projectiveAction L cover).range = PSL3.OuterSolvable.standard F

variable {L}

/-- The kernel of projective conjugation is exactly the relative centralizer. -/
theorem projectiveAction_ker (c : FourCover L) :
    (projectiveAction L c).ker = centralizer (L : Set I) := by
  ext x
  change c.toCover.autMap c.ker_eq_center (MulAut.conjNormal x) = 1 ↔ _
  rw [← map_one (c.toCover.autMap c.ker_eq_center),
    (c.toCover.autMap_injective c.ker_eq_center).eq_iff]
  constructor
  · intro h y hy
    have hh := congrArg (fun a : MulAut L => ((a ⟨y, hy⟩ : L) : I)) h
    change x * y * x⁻¹ = y at hh
    exact (mul_inv_eq_iff_eq_mul.mp hh).symm
  · intro h
    ext y
    change x * (y : I) * x⁻¹ = (y : I)
    rw [← h (y : I) y.property, mul_inv_cancel_right]

theorem Overgroup.projectiveAction_ker (d : Overgroup L) :
    (projectiveAction L d.cover).ker = (center L).map L.subtype :=
  (ExtendedCentralizer.projectiveAction_ker d.cover).trans d.centralizer_eq

/-- Marked coordinates on the actual common Sylow-three normalizer.
The first three-cycle is the linear factor and the second is the diagonal
factor. The graph involution fixes the first and inverts the second. -/
structure NormalizerGeometry (d : Overgroup L) where
  YS : Subgroup I
  X : Sylow 3 YS
  XD : Subgroup YS
  XD_le_three : XD ≤ (X : Subgroup YS)
  coordinates : normalizer (X : Set YS) ≃* (SymmetricThree × SymmetricThree)
  tau : normalizer (X : Set YS)
  field : normalizer (X : Set YS)
  tau_coordinates : coordinates tau = (1, reflection)
  field_coordinates : coordinates field = (reflection, reflection)
  three_coordinates :
    ((X : Subgroup YS).subgroupOf (normalizer (X : Set YS))).map
      coordinates.toMonoidHom = (zpowers rotation).prod (zpowers rotation)
  linear_coordinates :
    (((X : Subgroup YS) ⊓ L.comap YS.subtype).subgroupOf
      (normalizer (X : Set YS))).map coordinates.toMonoidHom =
        (zpowers rotation).prod ⊥
  diagonal_coordinates :
    (XD.subgroupOf (normalizer (X : Set YS))).map coordinates.toMonoidHom =
      (⊥ : Subgroup SymmetricThree).prod (zpowers rotation)
  tau_graph : IsConj (projectiveAction L d.cover ((tau : YS) : I))
    (PSL3.OuterSolvable.graph F)
  field_frobenius : IsConj (projectiveAction L d.cover ((field : YS) : I)) pslFrobenius
  graphField_centralizes_center :
    (((tau * field : normalizer (X : Set YS)) : YS) : I) ∈
      centralizer ((center L).map L.subtype : Set I)

namespace NormalizerGeometry
variable {d : Overgroup L} (n : NormalizerGeometry d)

/-- The normalizer inclusion keeps both ambient subgroup maps. -/
@[expose] def inclusion : normalizer (n.X : Set n.YS) →* I :=
  n.YS.subtype.comp (normalizer (n.X : Set n.YS)).subtype

@[expose] def tauI : I := n.inclusion n.tau
@[expose] def fieldI : I := n.inclusion n.field
@[expose] def graphFieldI : I := n.tauI * n.fieldI

/-- The selected diagonal three-element, in the actual overgroup. -/
@[expose] def diagonalElement : I := n.inclusion (n.coordinates.symm (1, rotation))

/-- The given diagonal factor is retained as a subgroup of I. -/
@[expose] def diagonalFactorIn : Subgroup I := n.XD.map n.YS.subtype

/-- The source linear factor X ∩ L, with its ambient inclusion. -/
@[expose] def linearFactorIn : Subgroup I :=
  ((n.X : Subgroup n.YS) ⊓ L.comap n.YS.subtype).map n.YS.subtype

theorem graphField_coordinates :
    n.coordinates (n.tau * n.field) = (reflection, 1) := by
  rw [map_mul, n.tau_coordinates, n.field_coordinates]
  decide

theorem tau_sq : n.tauI ^ 2 = 1 := by
  have h : n.tau ^ 2 = 1 := by
    apply n.coordinates.injective
    rw [map_pow, map_one, n.tau_coordinates]
    decide
  exact (map_pow n.inclusion n.tau 2).symm.trans (h ▸ map_one n.inclusion)

theorem field_sq : n.fieldI ^ 2 = 1 := by
  have h : n.field ^ 2 = 1 := by
    apply n.coordinates.injective
    rw [map_pow, map_one, n.field_coordinates]
    decide
  exact (map_pow n.inclusion n.field 2).symm.trans (h ▸ map_one n.inclusion)

theorem tau_commutes_field : Commute n.tauI n.fieldI := by
  apply Commute.map _ n.inclusion
  apply n.coordinates.injective
  rw [map_mul, map_mul, n.tau_coordinates, n.field_coordinates]
  decide

theorem graphField_sq : n.graphFieldI ^ 2 = 1 := by
  rw [graphFieldI, n.tau_commutes_field.mul_pow, n.tau_sq, n.field_sq, mul_one]

theorem diagonalElement_cube : n.diagonalElement ^ 3 = 1 := by
  have h : (n.coordinates.symm (1, rotation)) ^ 3 = 1 := by
    apply n.coordinates.injective
    rw [map_pow, map_one, MulEquiv.apply_symm_apply]
    decide
  exact (map_pow n.inclusion _ 3).symm.trans (h ▸ map_one n.inclusion)

theorem diagonalElement_mem_centralizer :
    n.diagonalElement ∈ centralizer ({n.graphFieldI} : Set I) := by
  apply mem_centralizer_singleton_iff.mpr
  have h : Commute (n.coordinates.symm (1, rotation)) (n.tau * n.field) := by
    apply n.coordinates.injective
    simp only [map_mul, MulEquiv.apply_symm_apply, n.tau_coordinates, n.field_coordinates]
    decide
  exact (h.map n.inclusion).eq.trans (by rw [map_mul]; rfl)

theorem diagonalElement_mem_three :
    (n.coordinates.symm (1, rotation) : n.YS) ∈ (n.X : Subgroup n.YS) := by
  have h : (1, rotation) ∈
      ((n.X : Subgroup n.YS).subgroupOf (normalizer (n.X : Set n.YS))).map
        n.coordinates.toMonoidHom := by
    rw [n.three_coordinates]
    exact ⟨one_mem _, mem_zpowers _⟩
  obtain ⟨x, hx, he⟩ := h
  have hx' : x = n.coordinates.symm (1, rotation) :=
    n.coordinates.injective (he.trans (n.coordinates.apply_symm_apply _).symm)
  exact hx' ▸ hx

theorem diagonalElement_mem_diagonal : n.diagonalElement ∈ n.diagonalFactorIn := by
  have h : (1, rotation) ∈
      (n.XD.subgroupOf (normalizer (n.X : Set n.YS))).map
        n.coordinates.toMonoidHom := by
    rw [n.diagonal_coordinates]
    exact ⟨one_mem _, mem_zpowers _⟩
  obtain ⟨x, hx, he⟩ := h
  have hx' : x = n.coordinates.symm (1, rotation) :=
    n.coordinates.injective (he.trans (n.coordinates.apply_symm_apply _).symm)
  exact mem_map_of_mem n.YS.subtype (hx' ▸ hx)

/-- The marked diagonal element is outside the linear cover. -/
theorem diagonalElement_notMem_linear : n.diagonalElement ∉ L := by
  intro hL
  have h : (1, rotation) ∈
      (((n.X : Subgroup n.YS) ⊓ L.comap n.YS.subtype).subgroupOf
        (normalizer (n.X : Set n.YS))).map n.coordinates.toMonoidHom := by
    refine ⟨n.coordinates.symm (1, rotation), ⟨n.diagonalElement_mem_three, hL⟩,
      n.coordinates.apply_symm_apply _⟩
  rw [n.linear_coordinates] at h
  have hr : rotation = 1 := h.2
  exact (by decide : rotation ≠ 1) hr

theorem diagonalElement_order : orderOf n.diagonalElement = 3 := by
  apply orderOf_eq_prime_iff.mpr
  exact ⟨n.diagonalElement_cube, fun h => n.diagonalElement_notMem_linear
    (h ▸ L.one_mem)⟩

/-- The field involution inverts the entire selected Sylow subgroup. -/
theorem field_inverts_three (x : normalizer (n.X : Set n.YS))
    (hx : (x : n.YS) ∈ (n.X : Subgroup n.YS)) :
    n.fieldI * n.inclusion x * n.fieldI⁻¹ = (n.inclusion x)⁻¹ := by
  have hm : n.coordinates x ∈ (zpowers rotation).prod (zpowers rotation) := by
    rw [← n.three_coordinates]
    exact mem_map_of_mem n.coordinates.toMonoidHom hx
  have h : n.field * x * n.field⁻¹ = x⁻¹ := by
    apply n.coordinates.injective
    simp only [map_mul, map_inv, n.field_coordinates]
    exact Prod.ext (reflection_inverts_rotation _ hm.1)
      (reflection_inverts_rotation _ hm.2)
  simpa only [map_mul, map_inv, fieldI] using congrArg n.inclusion h

end NormalizerGeometry

/-- The extended centralizer is relative to the actual overgroup I. -/
@[expose] def centralizerIn (w : I) : Subgroup I := centralizer ({w} : Set I)

/-- C_L(w), now a normal subgroup inside C_I(w). -/
@[expose] def linearCentralizer (w : I) : Subgroup (centralizerIn w) :=
  L.comap (centralizerIn w).subtype

instance linearCentralizer_normal (w : I) : (linearCentralizer (L := L) w).Normal :=
  inferInstanceAs (L.comap (centralizerIn w).subtype).Normal

/-- The intrinsic linear residual, embedded only in the extended centralizer. -/
@[expose] def residualIn (w : I) : Subgroup (centralizerIn w) :=
  (pResidual 2 (linearCentralizer (L := L) w)).map
    (linearCentralizer (L := L) w).subtype

instance residualIn_normal (w : I) : (residualIn (L := L) w).Normal :=
  inferInstanceAs ((pResidual 2 (linearCentralizer (L := L) w)).map
    (linearCentralizer (L := L) w).subtype).Normal

/-- No ambient element changes in the fixed-subgroup identification. -/
@[expose] def fixedEquivLinearCentralizer (w : I) :
    (MulAut.conjNormal w : MulAut L).fixedSubgroup ≃* linearCentralizer (L := L) w where
  toFun x := ⟨⟨(x.val : I), by
    apply mem_centralizer_singleton_iff.mpr
    have hx := congrArg Subtype.val ((MulAut.mem_fixedSubgroup _ _).mp x.property)
    change w * (x.val : I) * w⁻¹ = (x.val : I) at hx
    exact (mul_inv_eq_iff_eq_mul.mp hx).symm⟩, x.val.property⟩
  invFun x := ⟨⟨x.val.val, x.property⟩, by
    apply (MulAut.mem_fixedSubgroup _ _).mpr
    apply Subtype.ext
    change w * x.val.val * w⁻¹ = x.val.val
    rw [← mem_centralizer_singleton_iff.mp x.val.property, mul_inv_cancel_right]⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

/-- Transport the intrinsic fixed residual, preserving its overgroup inclusion. -/
noncomputable def fixedResidualEquiv (w : I) :
    pResidual 2 (MulAut.conjNormal w : MulAut L).fixedSubgroup ≃*
      residualIn (L := L) w := by
  let e := fixedEquivLinearCentralizer (L := L) w
  exact (((pResidual 2 _).equivMapOfInjective e.toMonoidHom e.injective).trans
    (MulEquiv.subgroupCongr (map_pResidual 2 e))).trans
      ((pResidual 2 _).equivMapOfInjective (linearCentralizer (L := L) w).subtype
        (linearCentralizer (L := L) w).subtype_injective)

omit [L.Normal] in
theorem residualIn_le_linear (w : I) :
    residualIn (L := L) w ≤ linearCentralizer (L := L) w := map_subtype_le _

theorem residualIn_card (w : I)
    (e : pResidual 2 (MulAut.conjNormal w : MulAut L).fixedSubgroup ≃* ElementaryNine) :
    Nat.card (residualIn (L := L) w) = 9 := by
  rw [Nat.card_congr ((fixedResidualEquiv (L := L) w).symm.trans e).toEquiv]
  simp [ElementaryNine, Nat.card_eq_fintype_card]

/-- The E₉ residual supplies a normal odd subgroup of the extended centralizer.
The reverse containment is a separate overgroup calculation. -/
theorem residualIn_le_oddCore (w : I)
    (e : pResidual 2 (MulAut.conjNormal w : MulAut L).fixedSubgroup ≃* ElementaryNine) :
    residualIn (L := L) w ≤ pPrimeCore 2 (centralizerIn w) := by
  exact le_sSup ⟨inferInstance, by norm_num [residualIn_card w e]⟩

/-- The cubic diagonal generator in the actual extended centralizer. -/
@[expose] def NormalizerGeometry.diagonalInCentralizer {d : Overgroup L}
    (n : NormalizerGeometry d) : centralizerIn n.graphFieldI :=
  ⟨n.diagonalElement, n.diagonalElement_mem_centralizer⟩

theorem NormalizerGeometry.diagonalInCentralizer_order {d : Overgroup L}
    (n : NormalizerGeometry d) : orderOf n.diagonalInCentralizer = 3 := by
  rw [← orderOf_injective (centralizerIn n.graphFieldI).subtype
    (centralizerIn n.graphFieldI).subtype_injective]
  exact n.diagonalElement_order

/-- The diagonal generator enlarges the linear residual and cannot be
mistaken for an element of the joint centralizer's E₉. -/
theorem NormalizerGeometry.diagonalInCentralizer_notMem_residual {d : Overgroup L}
    (n : NormalizerGeometry d) :
    n.diagonalInCentralizer ∉ residualIn (L := L) n.graphFieldI := by
  intro h
  exact n.diagonalElement_notMem_linear (residualIn_le_linear n.graphFieldI h)

/-- The actual conjugation action of C_I(w) on its normal linear residual. -/
@[expose] def residualAction (w : I) :
    centralizerIn w →* MulAut (residualIn (L := L) w) := MulAut.conjNormal

/-- The kernel contains the residual once it is elementary abelian. The
quotient below is formed in the relative centralizer, never in I. -/
abbrev residualActionKernelQuotient (w : I) :=
  (residualAction (L := L) w).ker ⧸
    (residualIn (L := L) w).subgroupOf (residualAction (L := L) w).ker

/-- The remaining intrinsic action calculation. These premises contain no
odd-core, Sylow, order-27, or extraspecial assertion. They must be proved
from the marked overgroup geometry before completing the source result. -/
structure ResidualActionCalculation (w : I) : Prop where
  surjective : Function.Surjective (residualAction (L := L) w)
  kernel_quotient_two : IsPGroup 2 (residualActionKernelQuotient (L := L) w)

end Matrix.PSL3Four.ExtendedCentralizer
