module

public import Theory.AlgebraicGroup.RootSubgroups.CharacterRootGeometry
public import Theory.AlgebraicGroup.Reductive.Defs
public import Theory.AlgebraicGroup.Tori.Character.Duality
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Theory.AlgebraicGroup.RootSubgroups.IntegralCorootReflection

/-!
# Real geometry of the actual torus root lattice

The character lattice of a torus is free of finite rank. A basis of its root
sublattice embeds that lattice faithfully into a real coordinate space, which
the actual roots span. Normalized integral reflection functionals extend to
this real space. Finiteness of the roots forces injectivity of the coroot map
and the compatibility of root and coroot reflections. This constructs a
crystallographic root system without assuming a root pairing as input.

For reducedness it suffices to exclude an equality `2 α = m β` between distinct
roots other than opposites. The root-pairing identities reduce every real
linear dependence to an equality of this form in the actual character lattice.

The geometric premises remain explicit: reductivity has not yet supplied
opposite roots, proportional-root exclusion, or rank-one torus reflections.
The earlier centralizer and singular-torus geometry supplies the source route
for these premises; no differentiation of characters is used here.

Source: Borel, *Linear Algebraic Groups*, §13.18(3,4), §14.6, and §14.8
(printed pp.186--189); GLS3, Theorem 1.9.5(d). The companion `Realization`
module applies this construction to the existing complete root-data consumer.
-/

open Module
namespace Theory.AlgebraicGroup
universe u
variable {k : Type u} [Field k]
variable {G : Variety k} [AlgebraicGroup G] {T : ClosedSubgroup G}

private theorem rootLattice_basis [IsAlgClosed k] (hT : IsSubtorus T) :
    ∃ n, Nonempty (Basis (Fin n) ℤ (Additive (TorusRootLattice T))) := by
  obtain ⟨n, ⟨e⟩⟩ := hT
  let := torus_character_fg_of_iso n e
  let := torus_character_free_of_iso n e
  let f := (TorusRootLattice T).subtype.toAdditive.toIntLinearMap
  have hf : Function.Injective f := Subtype.val_injective
  let : Module.Finite ℤ (Additive (TorusRootLattice T)) := Module.Finite.of_injective f hf
  let : Module.IsTorsionFree ℤ (Additive (TorusRootLattice T)) :=
    hf.moduleIsTorsionFree f (fun r x => f.map_smul r x)
  obtain ⟨d, b⟩ := Module.basisOfFiniteTypeTorsionFree'
    (R := ℤ) (M := Additive (TorusRootLattice T))
  exact ⟨d, ⟨b⟩⟩

namespace RootLatticeCoordinates
variable {n : ℕ} (b : Basis (Fin n) ℤ (Additive (TorusRootLattice T)))

private noncomputable def realMap : Additive (TorusRootLattice T) →+ (Fin n → ℝ) where
  toFun x i := b.equivFun x i
  map_zero' := by ext i; simp
  map_add' x y := by ext i; simp

private theorem realMap_injective : Function.Injective (realMap b) := by
  intro x y h
  apply b.equivFun.injective
  ext i
  have hi : (b.equivFun x i : ℝ) = (b.equivFun y i : ℝ) := congrFun h i
  exact_mod_cast hi

private theorem realMap_basis (i : Fin n) : realMap b (b i) = Pi.basisFun ℝ (Fin n) i := by
  ext j
  simp [realMap, Pi.basisFun_apply, Pi.single_apply, Finsupp.single_apply, eq_comm]

private theorem closure_image_mem_span {A : Type*} [CommGroup A] (s : Set A)
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (f : Additive (Subgroup.closure s) →+ V) (x : Additive (Subgroup.closure s)) :
    f x ∈ Submodule.span ℝ
      (Set.range (fun α : s => f (Additive.ofMul ⟨α.val, Subgroup.subset_closure α.property⟩))) := by
  obtain ⟨x, hx⟩ := x
  induction hx using Subgroup.closure_induction with
  | mem x hx =>
    change f (Additive.ofMul ⟨x, Subgroup.subset_closure hx⟩) ∈ _
    exact Submodule.subset_span ⟨⟨x, hx⟩, rfl⟩
  | one =>
    change f 0 ∈ _
    rw [map_zero]
    exact Submodule.zero_mem _
  | mul x y hx hy ihx ihy =>
    change f (Additive.ofMul ⟨x, hx⟩ + Additive.ofMul ⟨y, hy⟩) ∈ _
    rw [map_add]
    exact Submodule.add_mem _ ihx ihy
  | inv x hx ih =>
    change f (-Additive.ofMul ⟨x, hx⟩) ∈ _
    rw [map_neg]
    exact Submodule.neg_mem _ ih

private theorem realMap_mem_span (x : Additive (TorusRootLattice T)) :
    realMap b x ∈ Submodule.span ℝ
      (Set.range (fun α : TorusRootIndex T => realMap b (Additive.ofMul α.latticeElement))) :=
  closure_image_mem_span (TorusRootSet T) (realMap b) x

private theorem span_realMap_root : Submodule.span ℝ
    (Set.range (fun α : TorusRootIndex T => realMap b (Additive.ofMul α.latticeElement))) = ⊤ := by
  apply top_unique
  rw [← (Pi.basisFun ℝ (Fin n)).span_eq]
  apply Submodule.span_le.mpr
  rintro _ ⟨i, rfl⟩
  rw [← realMap_basis b i]
  exact realMap_mem_span b (b i)

private noncomputable def extendFunctional (φ : Additive (TorusRootLattice T) →+ ℤ) :
    Module.Dual ℝ (Fin n → ℝ) :=
  (Pi.basisFun ℝ (Fin n)).constr ℝ (fun i => (φ (b i) : ℝ))

private theorem extendFunctional_realMap (φ : Additive (TorusRootLattice T) →+ ℤ)
    (x : Additive (TorusRootLattice T)) :
    extendFunctional b φ (realMap b x) = (φ x : ℝ) := by
  have h := congrArg (fun y => (φ y : ℝ)) (b.sum_repr x)
  simp only [map_sum, map_zsmul, zsmul_eq_mul, Int.cast_sum, Int.cast_mul] at h
  simpa [extendFunctional, Basis.constr_apply_fintype, realMap, Basis.equivFun_apply] using h

end RootLatticeCoordinates

open RootLatticeCoordinates

/-- Integral reflections preserving the actual roots, together with the
source proportional-root exclusion, construct every field of the real root
geometry. The real dimension is the rank of the root lattice, not the full
character lattice. These hypotheses still require geometric proof. -/
public theorem exists_torusCharacterRootGeometry_of_integral_reflections [IsAlgClosed k]
    (hT : IsSubtorus T)
    (φ : TorusRootIndex T → Additive (TorusRootLattice T) →+ ℤ)
    (htwo : ∀ α, φ α (Additive.ofMul α.latticeElement) = 2)
    (href : ∀ α β : TorusRootIndex T,
      IsTorusRoot T (α.val * β.val ^ (-φ β (Additive.ofMul α.latticeElement))))
    (hred : ∀ α β : TorusRootIndex T, ∀ m : ℤ,
      α.val ^ (2 : ℤ) = β.val ^ m → α.val = β.val ∨ α.val = β.val⁻¹) :
    Nonempty (TorusCharacterRootGeometry T) := by
  classical
  obtain ⟨n, ⟨b⟩⟩ := rootLattice_basis hT
  let r : TorusRootIndex T ↪ (Fin n → ℝ) :=
    ⟨fun α => realMap b (Additive.ofMul α.latticeElement), by
      intro α β h
      have he := realMap_injective b h
      exact Subtype.ext (congrArg (fun x => (Additive.toMul x).val) he)⟩
  let c : TorusRootIndex T → Module.Dual ℝ (Fin n → ℝ) := fun α =>
    extendFunctional b (φ α)
  have hc (α β : TorusRootIndex T) : c β (r α) = (φ β (Additive.ofMul α.latticeElement) : ℝ) :=
    extendFunctional_realMap b (φ β) _
  have hp (α : TorusRootIndex T) : c α (r α) = 2 := by rw [hc, htwo]; norm_num
  have hr (β : TorusRootIndex T) : Set.MapsTo (Module.preReflection (r β) (c β))
      (Set.range r) (Set.range r) := by
    rintro _ ⟨α, rfl⟩
    let γ : TorusRootIndex T := ⟨_, href α β⟩
    refine ⟨γ, ?_⟩
    rw [Module.preReflection_apply, hc]
    change realMap b (Additive.ofMul α.latticeElement +
      (-φ β (Additive.ofMul α.latticeElement)) • Additive.ofMul β.latticeElement) = _
    rw [map_add, map_zsmul, neg_smul, sub_eq_add_neg, Int.cast_smul_eq_zsmul]
    rfl
  have hcinj : Function.Injective c := by
    intro α β h
    apply r.injective
    apply Module.eq_of_mapsTo_reflection_of_mem (Set.finite_range r)
      (hp α) (hp β) _ _ (hr α) (hr β) (Set.mem_range_self β)
    · rw [← h]; exact hp α
    · rw [h]; exact hp β
  let ce : TorusRootIndex T ↪ Module.Dual ℝ (Fin n → ℝ) := ⟨c, hcinj⟩
  let p := Module.Dual.eval ℝ (Fin n → ℝ)
  have hsp : Submodule.span ℝ (Set.range r) = ⊤ := span_realMap_root b
  let P := RootPairing.mk'' p r ce hp hr hsp
  have hint (α β : TorusRootIndex T) : ∃ z : ℤ, (z : ℝ) = p (r α) (ce β) :=
    ⟨_, (hc α β).symm⟩
  let : P.IsRootSystem := RootPairing.isRootSystem_mk'' hint
  have hpair (α β : TorusRootIndex T) :
      P.pairing α β = (φ β (Additive.ofMul α.latticeElement) : ℝ) := hc α β
  have hPred : P.IsReduced := by
    constructor
    intro α β h
    have he := P.pairing_smul_root_eq_of_not_linearIndependent h
    rw [hpair] at he
    change (φ α (Additive.ofMul β.latticeElement) : ℝ) •
      realMap b (Additive.ofMul α.latticeElement) =
      (2 : ℝ) • realMap b (Additive.ofMul β.latticeElement) at he
    have he' : realMap b ((2 : ℤ) • Additive.ofMul β.latticeElement) =
        realMap b ((φ α (Additive.ofMul β.latticeElement)) • Additive.ofMul α.latticeElement) := by
      simpa only [map_zsmul, ← Int.cast_smul_eq_zsmul ℝ, Int.cast_ofNat] using he.symm
    have heq : β.val ^ (2 : ℤ) = α.val ^ (φ α (Additive.ofMul β.latticeElement)) :=
      congrArg (fun x => (Additive.toMul x).val) (realMap_injective b he')
    rcases hred β α _ heq with heq | heq
    · left
      change r α = r β
      exact congrArg r (Subtype.ext heq.symm)
    · right
      have hlat : Additive.ofMul β.latticeElement = -Additive.ofMul α.latticeElement :=
        congrArg Additive.ofMul (Subtype.ext heq)
      change realMap b (Additive.ofMul α.latticeElement) =
        -realMap b (Additive.ofMul β.latticeElement)
      rw [hlat, map_neg, neg_neg]
  let e : Module.Dual ℝ (Fin n → ℝ) ≃ₗ[ℝ] (Fin n → ℝ) :=
    (Pi.basisFun ℝ (Fin n)).dualBasis.equivFun
  let Q := P.map (Equiv.refl _) (LinearEquiv.refl ℝ _) e
  have hQpair (α β : TorusRootIndex T) : Q.pairing α β = P.pairing α β := by
    change P.toLinearMap (P.root α) (e.symm (e (P.coroot β))) = _
    rw [e.symm_apply_apply]
    rfl
  refine ⟨⟨n, realMap b, realMap_injective b, Q, fun _ => rfl,
    inferInstance, ?_, ?_⟩⟩
  · constructor
    intro α β
    exact ⟨_, (hQpair α β |>.trans (hpair α β)).symm⟩
  · constructor
    exact hPred.eq_or_eq_neg

/-- Actual rank-one conjugation and cocharacter equations supply the integral
reflection functionals in the preceding construction. Only their restriction
to the actual root lattice is needed for the real geometry. -/
public theorem exists_torusCharacterRootGeometry_of_rankOne_reflections [IsAlgClosed k]
    (hT : IsSubtorus T)
    (h : ∀ β : TorusRootIndex T, Nonempty (IntegralCorootReflection T β.val))
    (hred : ∀ α β : TorusRootIndex T, ∀ m : ℤ,
      α.val ^ (2 : ℤ) = β.val ^ m → α.val = β.val ∨ α.val = β.val⁻¹) :
    Nonempty (TorusCharacterRootGeometry T) := by
  classical
  let C : ∀ β : TorusRootIndex T, IntegralCorootReflection T β.val :=
    fun β => (h β).some
  let φ : TorusRootIndex T → Additive (TorusRootLattice T) →+ ℤ := fun β =>
    (characterCocharacterPairing T (C β).cocharacter).comp
      (TorusRootLattice T).subtype.toAdditive
  apply exists_torusCharacterRootGeometry_of_integral_reflections hT φ
  · intro β
    exact (C β).pairing_self
  · intro α β
    exact (C β).preserves_roots α.property
  · exact hred

/-- The exact rank-one existence interface also asks for a nontrivial root
and its opposite. This version records their required discharge separately
from proportional-root exclusion, all from Borel §13.18. -/
public theorem exists_torusCharacterRootGeometry_of_rankOne_reflections_of_root_support
    [IsAlgClosed k] (hT : IsMaximalTorus T)
    (hne : ∀ α : TorusRootIndex T, α.val ≠ 1)
    (hneg : ∀ α : TorusRootIndex T, IsTorusRoot T α.val⁻¹)
    (hred : ∀ α β : TorusRootIndex T, ∀ m : ℤ,
      α.val ^ (2 : ℤ) = β.val ^ m → α.val = β.val ∨ α.val = β.val⁻¹)
    (h : ∀ χ : TorusWeight T, χ ≠ 1 → IsTorusRoot T χ →
      IsTorusRoot T χ⁻¹ → Nonempty (IntegralCorootReflection T χ)) :
    Nonempty (TorusCharacterRootGeometry T) :=
  exists_torusCharacterRootGeometry_of_rankOne_reflections hT.1
    (fun α => h α.val (hne α) α.property (hneg α)) hred

end Theory.AlgebraicGroup
