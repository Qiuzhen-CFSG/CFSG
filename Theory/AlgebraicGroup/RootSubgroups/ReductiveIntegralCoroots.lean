module

public import Theory.AlgebraicGroup.RootSubgroups.CharacterRootGeometry
public import Theory.AlgebraicGroup.Reductive.Defs

public import Theory.AlgebraicGroup.RootSubgroups.IntegralCorootReflection

/-!
# Comparing integral reflections with actual character root geometry

A normalized integral functional whose reflection preserves the actual roots
has the Cartan values of every supplied `TorusCharacterRootGeometry`.
We identify the actual root lattice with the integral span of the real roots,
then use uniqueness of a reflection preserving a finite spanning set. This
avoids assuming that an arbitrary additive character embedding extends to a
real-linear map on the full character lattice.

Actual rank-one torus reflections supply such functionals by Laurent
evaluation on their cocharacters. The resulting conditional assembly retains
the geometric existence premise explicitly; reductivity has not yet supplied
that premise here. In particular crystallographic integrality on the root
lattice alone is never used as an extension theorem to all characters.

Source: Borel, *Linear Algebraic Groups*, §14.7, printed p.187 (reflection
uniqueness), and §§13.18, 14.6--14.8; GLS3, Theorem 1.9.5(d) and Remarks 1.9.6.
`ReductiveIntegralCoroots.Realization` applies the result to the actual
root-data constructor in `ReductiveRealization`.
-/

open Submodule
namespace Theory.AlgebraicGroup.TorusCharacterRootGeometry
universe u
variable {k : Type u} [Field k]
variable {G : Variety k} [AlgebraicGroup G] {T : ClosedSubgroup G}
variable (R : TorusCharacterRootGeometry T)

private theorem characterMap_mem_rootSpan (x : Additive (TorusRootLattice T)) :
    R.characterMap x ∈ R.pairing.rootSpan ℤ := by
  obtain ⟨x, hx⟩ := x
  induction hx using Subgroup.closure_induction with
  | mem x hx =>
    change R.characterMap (Additive.ofMul (TorusRootIndex.latticeElement ⟨x, hx⟩)) ∈ _
    rw [← R.root_eq ⟨x, hx⟩]
    exact Submodule.subset_span (Set.mem_range_self _)
  | one =>
    change R.characterMap 0 ∈ _
    rw [map_zero]
    exact zero_mem _
  | mul x y hx hy ihx ihy =>
    change R.characterMap (Additive.ofMul ⟨x, hx⟩ + Additive.ofMul ⟨y, hy⟩) ∈ _
    rw [map_add]
    exact add_mem ihx ihy
  | inv x hx ih =>
    change R.characterMap (-Additive.ofMul ⟨x, hx⟩) ∈ _
    rw [map_neg]
    exact neg_mem ih

private noncomputable def rootSpanMap :
    Additive (TorusRootLattice T) →ₗ[ℤ] R.pairing.rootSpan ℤ :=
  R.characterMap.toIntLinearMap.codRestrict _ R.characterMap_mem_rootSpan

private theorem rootSpanMap_root (α : TorusRootIndex T) :
    R.rootSpanMap (Additive.ofMul α.latticeElement) = R.pairing.rootSpanMem ℤ α :=
  Subtype.ext (R.root_eq α).symm

private theorem rootSpanMap_bijective : Function.Bijective R.rootSpanMap := by
  constructor
  · intro x y h
    exact R.characterMap_injective (congrArg Subtype.val h)
  · rw [← LinearMap.range_eq_top]
    apply top_unique
    have hs : Submodule.span ℤ (Set.range (R.pairing.rootSpanMem ℤ)) = ⊤ :=
      (Submodule.span_range_subtype_eq_top_iff _ _).mpr rfl
    rw [← hs]
    apply Submodule.span_le.mpr
    rintro _ ⟨α, rfl⟩
    exact ⟨Additive.ofMul α.latticeElement, R.rootSpanMap_root α⟩

private noncomputable def rootSpanEquiv :
    Additive (TorusRootLattice T) ≃ₗ[ℤ] R.pairing.rootSpan ℤ :=
  LinearEquiv.ofBijective R.rootSpanMap R.rootSpanMap_bijective

private theorem rootSpanEquiv_symm_root (α : TorusRootIndex T) :
    R.rootSpanEquiv.symm (R.pairing.rootSpanMem ℤ α) = Additive.ofMul α.latticeElement := by
  apply R.rootSpanEquiv.injective
  rw [LinearEquiv.apply_symm_apply]
  exact (R.rootSpanMap_root α).symm

private noncomputable def restrictFunctional (φ : Additive (TorusWeight T) →+ ℤ) :
    Module.Dual ℤ (R.pairing.rootSpan ℤ) :=
  (φ.comp (TorusRootLattice T).subtype.toAdditive).toIntLinearMap.comp
    R.rootSpanEquiv.symm.toLinearMap

private theorem restrictFunctional_root (φ : Additive (TorusWeight T) →+ ℤ)
    (α : TorusRootIndex T) :
    R.restrictFunctional φ (R.pairing.rootSpanMem ℤ α) = φ (Additive.ofMul α.val) := by
  change φ ((TorusRootLattice T).subtype.toAdditive
    (R.rootSpanEquiv.symm (R.pairing.rootSpanMem ℤ α))) = _
  rw [R.rootSpanEquiv_symm_root]
  rfl

variable [IsAlgClosed k]

/-- Finite-root reflection rigidity identifies a normalized integral reflection
functional with the Cartan functional on every actual root. -/
public theorem pairing_eq_of_integral_reflection
    (β : TorusRootIndex T) (φ : Additive (TorusWeight T) →+ ℤ)
    (htwo : φ (Additive.ofMul β.val) = 2)
    (href : ∀ α : TorusRootIndex T,
      IsTorusRoot T (α.val * β.val ^ (-φ (Additive.ofMul α.val))))
    (α : TorusRootIndex T) :
    (φ (Additive.ofMul α.val) : ℝ) = R.pairing.pairing α β := by
  let r := R.pairing.rootSpanMem ℤ
  have hs : Submodule.span ℤ (Set.range r) = ⊤ :=
    (Submodule.span_range_subtype_eq_top_iff _ _).mpr rfl
  have hf : Set.MapsTo (Module.preReflection (r β) (R.restrictFunctional φ))
      (Set.range r) (Set.range r) := by
    rintro _ ⟨γ, rfl⟩
    let δ : TorusRootIndex T := ⟨_, href γ⟩
    refine ⟨δ, ?_⟩
    apply Subtype.ext
    change R.pairing.root δ = R.pairing.root γ -
      R.restrictFunctional φ (R.pairing.rootSpanMem ℤ γ) • R.pairing.root β
    rw [R.restrictFunctional_root, R.root_eq, R.root_eq, R.root_eq]
    change R.characterMap (Additive.ofMul γ.latticeElement +
        (-φ (Additive.ofMul γ.val)) • Additive.ofMul β.latticeElement) = _
    rw [map_add, map_zsmul, neg_smul, sub_eq_add_neg]
  have hg : Set.MapsTo (Module.preReflection (r β) (R.pairing.coroot'In ℤ β))
      (Set.range r) (Set.range r) := by
    rintro _ ⟨γ, rfl⟩
    refine ⟨R.pairing.reflectionPerm β γ, ?_⟩
    apply Subtype.ext
    change R.pairing.root (R.pairing.reflectionPerm β γ) =
      R.pairing.root γ - R.pairing.coroot'In ℤ β (r γ) • R.pairing.root β
    rw [R.pairing.root_reflectionPerm, R.pairing.reflection_apply_root]
    rw [RootPairing.coroot'In_rootSpanMem_eq_pairingIn]
    rw [← Int.cast_smul_eq_zsmul ℝ]
    rw [← R.pairing.algebraMap_pairingIn ℤ]
    rfl
  have heq : R.restrictFunctional φ = R.pairing.coroot'In ℤ β := by
    apply Module.Dual.eq_of_preReflection_mapsTo (Set.finite_range r) hs
    · exact (R.restrictFunctional_root φ β).trans htwo
    · exact hf
    · simp
    · exact hg
  rw [← R.restrictFunctional_root φ α, heq,
    RootPairing.coroot'In_rootSpanMem_eq_pairingIn]
  exact R.pairing.algebraMap_pairingIn ℤ α β

omit [IsAlgClosed k] in
include R in
/-- Faithful root geometry excludes the trivial character from its roots. -/
public theorem root_ne_one (α : TorusRootIndex T) : α.val ≠ 1 := by
  intro h
  apply R.pairing.ne_zero α
  rw [R.root_eq]
  have hz : Additive.ofMul α.latticeElement = 0 := by
    exact congrArg Additive.ofMul (Subtype.ext h)
  rw [hz, map_zero]

/-- Rank-one conjugation geometry supplies integral coroots on the entire
character lattice, with Cartan values determined by finite reflection rigidity. -/
public theorem hasIntegralCoroots_of_reflections
    (h : ∀ β : TorusRootIndex T, Nonempty (IntegralCorootReflection T β.val)) :
    R.HasIntegralCoroots := by
  intro β
  obtain ⟨C⟩ := h β
  refine ⟨characterCocharacterPairing T C.cocharacter, ?_⟩
  exact R.pairing_eq_of_integral_reflection β _ C.pairing_self
    (fun α => C.preserves_roots α.property)

/-- Source assembly after the rank-one reflection theorem is supplied.
The supplied geometry itself proves the nontrivial and opposite-root premises;
no realized root datum or cocharacter is required of `R`. -/
public theorem hasIntegralCoroots_of_rankOne_reflections
    (h : ∀ χ : TorusWeight T, χ ≠ 1 → IsTorusRoot T χ →
      IsTorusRoot T χ⁻¹ → Nonempty (IntegralCorootReflection T χ)) :
    R.HasIntegralCoroots := by
  apply R.hasIntegralCoroots_of_reflections
  intro β
  apply h β.val (R.root_ne_one β) β.property
  have hneg := (R.pairing.reflectionPerm β β).property
  rwa [R.root_neg] at hneg

end Theory.AlgebraicGroup.TorusCharacterRootGeometry
