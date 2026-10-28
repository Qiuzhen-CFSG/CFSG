module
public import Theory.Combinatorics.ProjectivePlaneElationFixedPoints

/-!
# Affine coordinates supplied by an elation group

An axis-fixing group of order q² whose nonidentity elements are elations
acts regularly on the affine points of a finite plane of order q. A fixed
additive coordinate system on that group therefore gives affine coordinates,
with group multiplication acting by literal translations.

This is the elementary translation-plane step used in the centerfree branch
of DGS, Groups and Graphs, 10.5 and Theorem D, pp.156,224.
-/

@[expose] public noncomputable section
namespace Configuration
variable {H P L : Type*} [Group H] [Membership P L]
  [MulAction H P] [MulAction H L] [IsCollineationAction H P L]

/-- Conjugation transports both the center and the axis, including movement. -/
theorem IsElation.conjugate {g : H} {C : P} {l : L} (h : IsElation g C l) (a : H) :
    IsElation (a * g * a⁻¹) (a • C) (a • l) := by
  refine ⟨(IsCollineationAction.smul_mem_smul_iff a C l).mpr h.incident, ?_, ?_, ?_⟩
  · intro p hp
    have hp' : a⁻¹ • p ∈ l := by
      simpa only [inv_smul_smul] using
        (IsCollineationAction.smul_mem_smul_iff a⁻¹ p (a • l)).mpr hp
    simpa only [mul_smul, smul_inv_smul] using congrArg (a • ·) (h.fixes_axis_points _ hp')
  · intro m hm
    have hm' : C ∈ a⁻¹ • m := by
      simpa only [inv_smul_smul] using
        (IsCollineationAction.smul_mem_smul_iff a⁻¹ (a • C) m).mpr hm
    simpa only [mul_smul, smul_inv_smul] using congrArg (a • ·) (h.fixes_center_lines _ hm')
  · rcases h.moves with ⟨p,hp⟩ | ⟨m,hm⟩
    · left
      refine ⟨a • p,?_⟩
      simpa only [mul_smul, inv_smul_smul, ne_eq, (MulAction.injective a).eq_iff] using hp
    · right
      refine ⟨a • m,?_⟩
      simpa only [mul_smul, inv_smul_smul, ne_eq, (MulAction.injective a).eq_iff] using hm

variable [Finite P] [Finite L] [ProjectivePlane P L]

/-- The complement of any line has exactly q² points. -/
theorem card_affinePoints (l : L) :
    Nat.card {p : P // p ∉ l} = ProjectivePlane.order P L ^ 2 := by
  classical
  let : Fintype P := Fintype.ofFinite _
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype_compl,
    ProjectivePlane.card_points P L, ← Nat.card_eq_fintype_card]
  change _ - pointCount P l = _
  rw [ProjectivePlane.pointCount_eq]
  omega

/-- Deleting the unique point at infinity leaves q points on any other line. -/
theorem card_line_off_axis (l m : L) (C : P) (hCl : C ∈ l) (hCm : C ∈ m)
    (hml : m ≠ l) :
    Nat.card {p : P // p ∈ m ∧ p ∉ l} = ProjectivePlane.order P L := by
  classical
  let : Fintype P := Fintype.ofFinite _
  let e : {p : P // p ∈ m ∧ p ∉ l} ≃
      {p : {p : P // p ∈ m} // p ≠ ⟨C,hCm⟩} :=
    { toFun := fun p => ⟨⟨p,p.property.1⟩, fun he =>
        p.property.2 ((congrArg (fun t : {p : P // p ∈ m} => t.val) he).symm ▸ hCl)⟩
      invFun := fun p => ⟨p.val, p.val.property, fun hp => p.property (Subtype.ext
        ((Nondegenerate.eq_or_eq p.val.property hCm hp hCl).resolve_right hml))⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_subtype_compl,
    Fintype.card_subtype_eq, ← Nat.card_eq_fintype_card]
  change pointCount P m - 1 = _
  rw [ProjectivePlane.pointCount_eq]
  omega

variable (A : Subgroup H) (l : L)
  (haxis : ∀ a : A, (a : H) • l = l)
  (o : {p : P // p ∉ l})

/-- Evaluation at an affine origin, in the original point action. -/
def affineOrbit : A → {p : P // p ∉ l} := fun a => ⟨(a : H) • o.val, by
  intro hp
  have hp' : (a : H) • o.val ∈ (a : H) • l := (haxis a).symm ▸ hp
  exact o.property ((IsCollineationAction.smul_mem_smul_iff _ _ _).mp hp')⟩

variable (he : ∀ a : A, a ≠ 1 → ∃ C : P, IsElation (a : H) C l)

include he in
/-- Nonidentity translations fix no affine point, so evaluation is injective. -/
theorem affineOrbit_injective : Function.Injective (affineOrbit A l haxis o) := by
  intro a b hab
  by_contra hne
  have hd : b⁻¹ * a ≠ 1 := fun hh => hne (inv_mul_eq_one.mp hh).symm
  obtain ⟨C,hC⟩ := he (b⁻¹*a) hd
  apply hC.smul_ne_of_not_mem_axis o.property
  have hh := congrArg (fun p : {p : P // p ∉ l} => (b : H)⁻¹ • p.val) hab
  simpa only [affineOrbit, Subgroup.coe_mul, Subgroup.coe_inv, mul_smul, inv_smul_smul] using hh

variable (hcard : Nat.card A = ProjectivePlane.order P L ^ 2)

/-- Counting upgrades the free affine action to a regular action. -/
def affineOrbitEquiv : A ≃ {p : P // p ∉ l} :=
  Equiv.ofBijective (affineOrbit A l haxis o)
    ((Nat.bijective_iff_injective_and_card _).mpr
      ⟨affineOrbit_injective A l haxis o he, hcard.trans (card_affinePoints l).symm⟩)

@[simp] theorem affineOrbitEquiv_apply (a : A) :
    (affineOrbitEquiv A l haxis o he hcard a).val = (a : H) • o.val := rfl

variable {k : Type*} [Field k] (φ : A ≃* Multiplicative (Fin 2 → k))

/-- One field chart on all affine points, built from one group coordinate system. -/
def translationChart : (Fin 2 → k) ≃ {p : P // p ∉ l} :=
  Multiplicative.ofAdd.trans (φ.symm.toEquiv.trans (affineOrbitEquiv A l haxis o he hcard))

@[simp] theorem translationChart_apply (x : Fin 2 → k) :
    (translationChart A l haxis o he hcard φ x).val = (φ.symm (.ofAdd x) : H) • o.val := rfl

/-- The original group acts by addition in this same field chart. -/
theorem translationChart_add (a : A) (x : Fin 2 → k) :
    (translationChart A l haxis o he hcard φ ((φ a).toAdd + x)).val =
      (a : H) • (translationChart A l haxis o he hcard φ x).val := by
  change (φ.symm (φ a * .ofAdd x) : H) • o.val = _
  rw [map_mul, φ.symm_apply_apply, Subgroup.coe_mul, mul_smul]
  rfl
end Configuration
