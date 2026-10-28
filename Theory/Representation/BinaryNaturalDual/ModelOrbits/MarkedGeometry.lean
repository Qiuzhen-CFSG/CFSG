module

public import Theory.Representation.BinaryNaturalDual.ModelOrbits.StandardSylow

/-!
# Quadratic forms and three orbits on marked natural-plus-dual modules

A fully equivariant group and linear comparison transports the evaluation form
and the coordinate orbit classification while retaining both marked summands.
The comparison is an explicit input to these transport helpers; the source
assembly constructs it from the natural action and the outer-image condition.

The polar form is transported by a linear equivalence. Pulling any competing
invariant quadratic form back to coordinates proves uniqueness. The orbit and
Sylow clauses are transported through actual group isomorphisms, including the
inner transitivity needed for the nonsingular adapted-pair argument.

Source: Aschbacher–Smith, H.9.1(1–2), printed pp.389–390.
-/

public section

open BinaryNaturalDual BinaryNaturalDual.ModelOrbits BinaryLinear.OuterCyclic
namespace BinaryNaturalDual.ModelOrbits.MarkedGeometry

variable {n : ℕ} {M V : Type*} [Group M] [AddCommGroup V] [Module (ZMod 2) V]

/-- The union of the two punctured marked summands. -/
@[expose] def Pure (U W : Submodule (ZMod 2) V) (v : V) : Prop :=
  v ≠ 0 ∧ (v ∈ U ∨ v ∈ W)

/-- A singular vector with both marked components nonzero. -/
@[expose] def SingularDiagonal (U W : Submodule (ZMod 2) V)
    (q : QuadraticForm (ZMod 2) V) (v : V) : Prop :=
  v ∉ U ∧ v ∉ W ∧ q v = 0

/-- A nondegenerate invariant quadratic form with totally singular first summand. -/
@[expose] def IsInvariantForm (ρ : Representation (ZMod 2) M V) (U : Submodule (ZMod 2) V)
    (q : QuadraticForm (ZMod 2) V) : Prop :=
  q.polarBilin.Nondegenerate ∧ (∀ v ∈ U, q v = 0) ∧ (∀ m v, q (ρ m v) = q v)

variable (A : CoordinateAction n) (ρ : Representation (ZMod 2) M V)
variable (eM : M ≃* MulAut (LinearGroup n)) (eV : V ≃ₗ[ZMod 2] CoordinateSpace n)
variable {U W : Submodule (ZMod 2) V}

/-- The natural marking detects membership by vanishing of the dual coordinate. -/
theorem mem_natural_iff_of_marking
    (eU : U ≃ₗ[ZMod 2] BinaryLinear.OuterCyclic.Space n)
    (hU : ∀ u : U, eV u = (eU u, 0)) (v : V) :
    v ∈ U ↔ (eV v).2 = 0 := by
  constructor
  · intro hv
    exact congrArg Prod.snd (hU ⟨v, hv⟩)
  · intro hv
    have he : (eU.symm (eV v).1 : V) = v := by
      apply eV.injective
      rw [hU, eU.apply_symm_apply]
      exact Prod.ext rfl hv.symm
    exact he ▸ (eU.symm (eV v).1).property

/-- The dual marking detects membership by vanishing of the natural coordinate. -/
theorem mem_dual_iff_of_marking
    (eW : W ≃ₗ[ZMod 2] Module.Dual (ZMod 2) (BinaryLinear.OuterCyclic.Space n))
    (hW : ∀ w : W, eV w = (0, eW w)) (v : V) :
    v ∈ W ↔ (eV v).1 = 0 := by
  constructor
  · intro hv
    exact congrArg Prod.fst (hW ⟨v, hv⟩)
  · intro hv
    have he : (eW.symm (eV v).2 : V) = v := by
      apply eV.injective
      rw [hW, eW.apply_symm_apply]
      exact Prod.ext hv.symm rfl
    exact he ▸ (eW.symm (eV v).2).property

/-- The evaluation form pulled back through the constructed linear comparison. -/
noncomputable def form : QuadraticForm (ZMod 2) V := quadratic.comp eV.toLinearMap

/-- The coordinate formula for the transported quadratic form. -/
@[simp] theorem form_apply (v : V) : form eV v = quadratic (eV v) := by rfl

/-- On a sum of marked vectors the quadratic form is their evaluation pairing. -/
theorem form_natural_add_dual
    (eU : U ≃ₗ[ZMod 2] BinaryLinear.OuterCyclic.Space n)
    (eW : W ≃ₗ[ZMod 2] Module.Dual (ZMod 2) (BinaryLinear.OuterCyclic.Space n))
    (hU : ∀ u : U, eV u = (eU u, 0)) (hW : ∀ w : W, eV w = (0, eW w))
    (u : U) (w : W) : form eV ((u : V) + w) = eW w (eU u) := by
  simp only [form_apply, map_add, hU, hW, Prod.mk_add_mk, add_zero, zero_add, quadratic_apply]

private theorem nondegenerate_comp {X Y : Type*} [AddCommGroup X] [AddCommGroup Y]
    [Module (ZMod 2) X] [Module (ZMod 2) Y]
    (Q : QuadraticForm (ZMod 2) Y) (e : X ≃ₗ[ZMod 2] Y)
    (hQ : Q.polarBilin.Nondegenerate) : (Q.comp e.toLinearMap).polarBilin.Nondegenerate := by
  rw [QuadraticMap.polarBilin_comp]
  constructor
  · intro x hx
    apply e.injective
    rw [map_zero]
    apply hQ.1
    intro y
    obtain ⟨z, rfl⟩ := e.surjective y
    exact hx z
  · intro x hx
    apply e.injective
    rw [map_zero]
    apply hQ.2
    intro y
    obtain ⟨z, rfl⟩ := e.surjective y
    exact hx z

variable (hact : ∀ m v, eV (ρ m v) = A.representation (eM m) (eV v))
variable (hU : ∀ v : V, v ∈ U ↔ (eV v).2 = 0)
variable (hW : ∀ v : V, v ∈ W ↔ (eV v).1 = 0)

include hact hU in
/-- The transported form is nondegenerate, invariant, and zero on the natural summand. -/
theorem form_invariant (hn : n = 4 ∨ n = 5) : IsInvariantForm ρ U (form eV) := by
  refine ⟨?_, ?_, ?_⟩
  · exact nondegenerate_comp (quadratic (V := BinaryLinear.OuterCyclic.Space n)) eV
      (polar_nondegenerate (V := BinaryLinear.OuterCyclic.Space n))
  · intro v hv
    simp only [form_apply, quadratic_apply, (hU v).mp hv, LinearMap.zero_apply]
  · intro m v
    rw [form_apply, form_apply, hact, coordinate_quadratic_invariant hn A]

include hact hU in
/-- Pullback to coordinates proves uniqueness without assuming any form classification. -/
theorem form_unique (Q : QuadraticForm (ZMod 2) V) (hQ : IsInvariantForm ρ U Q) :
    Q = form eV := by
  have hs (a : MulAut (LinearGroup n)) (v : CoordinateSpace n) :
      eV.symm (A.representation a v) = ρ (eM.symm a) (eV.symm v) := by
    apply eV.injective
    rw [eV.apply_symm_apply, hact, eM.apply_symm_apply, eV.apply_symm_apply]
  have he : Q.comp eV.symm.toLinearMap = quadratic := by
    apply coordinate_quadratic_unique A
    · intro x
      apply hQ.2.1
      rw [hU]
      change (eV (eV.symm (x, 0))).2 = 0
      rw [eV.apply_symm_apply]
    · intro a v
      change Q (eV.symm (A.representation a v)) = Q (eV.symm v)
      rw [hs, hQ.2.2]
    · exact nondegenerate_comp Q eV.symm hQ.1
  ext v
  have hh := congrArg (fun q : QuadraticForm (ZMod 2) (CoordinateSpace n) => q (eV v)) he
  simpa only [QuadraticMap.comp_apply, LinearEquiv.coe_coe,
    eV.symm_apply_apply, form_apply] using hh

include hU hW in
/-- The marked pure vectors are exactly the pure coordinate vectors. -/
theorem pure_iff (v : V) : Pure U W v ↔ IsPure (eV v) := by
  have hz : v = 0 ↔ (eV v).1 = 0 ∧ (eV v).2 = 0 := by
    rw [← eV.map_eq_zero_iff, Prod.ext_iff]
    rfl
  simp only [Pure, IsPure, hU, hW]
  tauto

include hU hW in
/-- The marked singular diagonal vectors are exactly their coordinate counterparts. -/
theorem singularDiagonal_iff (v : V) :
    SingularDiagonal U W (form eV) v ↔ IsSingularDiagonal (eV v) := by
  simp only [SingularDiagonal, IsSingularDiagonal, hU, hW, form_apply]
  tauto

include hact hU hW in
/-- Exact orbit classification on nonzero vectors of the marked module. -/
theorem orbit_iff (hn : n = 4 ∨ n = 5) {v w : V} (hv : v ≠ 0) (hw : w ≠ 0) :
    (∃ m : M, ρ m v = w) ↔
      (Pure U W v ∧ Pure U W w) ∨
      (SingularDiagonal U W (form eV) v ∧ SingularDiagonal U W (form eV) w) ∨
      (form eV v = 1 ∧ form eV w = 1) := by
  have ho : (∃ m : M, ρ m v = w) ↔
      ∃ a, A.representation a (eV v) = eV w := by
    constructor
    · rintro ⟨m, hm⟩
      exact ⟨eM m, (hact m v).symm.trans (congrArg eV hm)⟩
    · rintro ⟨a, ha⟩
      refine ⟨eM.symm a, eV.injective ?_⟩
      rw [hact, eM.apply_symm_apply, ha]
  rw [ho, coordinate_orbit_iff hn A (by simpa using hv) (by simpa using hw)]
  rw [pure_iff eV hU hW, pure_iff eV hU hW,
    singularDiagonal_iff eV hU hW, singularDiagonal_iff eV hU hW]
  rfl

include hU hW in
/-- All three orbit classes occur in the marked module. -/
theorem orbit_classes_nonempty (hn : 2 ≤ n) :
    (∃ v : V, Pure U W v) ∧
    (∃ v : V, SingularDiagonal U W (form eV) v) ∧
    (∃ v : V, form eV v = 1) := by
  obtain ⟨⟨x, hx⟩, ⟨y, hy⟩, ⟨z, hz⟩⟩ := coordinate_orbit_classes_nonempty hn
  refine ⟨⟨eV.symm x, ?_⟩, ⟨eV.symm y, ?_⟩, ⟨eV.symm z, ?_⟩⟩
  · rw [pure_iff eV hU hW, eV.apply_symm_apply]
    exact hx
  · rw [singularDiagonal_iff eV hU hW, eV.apply_symm_apply]
    exact hy
  · simpa using hz

include hU hW in
/-- The two punctured summands consist of singular vectors. -/
theorem pure_singular {v : V} (hv : Pure U W v) : form eV v = 0 :=
  quadratic_eq_zero_of_isPure ((pure_iff eV hU hW v).mp hv)

include hU hW in
/-- The three orbit classes are pairwise disjoint. -/
theorem orbit_classes_disjoint (v : V) :
    (Pure U W v → ¬ SingularDiagonal U W (form eV) v) ∧
    (Pure U W v → form eV v ≠ 1) ∧
    (SingularDiagonal U W (form eV) v → form eV v ≠ 1) := by
  simpa only [pure_iff eV hU hW, singularDiagonal_iff eV hU hW, form_apply] using
    BinaryNaturalDual.ModelOrbits.orbit_classes_disjoint (eV v)

include hU hW in
/-- A vector of pairing one has both marked components nonzero. -/
theorem nonsingular_diagonal {v : V} (hv : form eV v = 1) : v ∉ U ∧ v ∉ W := by
  constructor
  · intro hu
    have hz := (hU v).mp hu
    simp [form_apply, quadratic_apply, hz] at hv

  · intro hw
    have hz := (hW v).mp hw
    simp [form_apply, quadratic_apply, hz] at hv

include hact in
/-- The actual source layer is transitive on pairing-one vectors. -/
theorem exists_layer_eq_of_pairing_one
    (hL : ∀ m : M, eM m ∈ MulAut.innerSubgroup (LinearGroup n) ↔
      m ∈ Theory.GroupTheory.componentLayer M)
    {v w : V} (hv : form eV v = 1) (hw : form eV w = 1) :
    ∃ l ∈ Theory.GroupTheory.componentLayer M, ρ l v = w := by
  obtain ⟨g, hg⟩ := exists_inner_eq_of_pairing_one A hv hw
  refine ⟨eM.symm (MulAut.conj g), (hL _).mp ?_, eV.injective ?_⟩
  · rw [eM.apply_symm_apply]
    exact ⟨g, rfl⟩
  · rw [hact, eM.apply_symm_apply]
    exact hg

include hact hU hW in
/-- Singular diagonal vectors are precisely the nonzero vectors fixed by some actual Sylow. -/
theorem singularDiagonal_iff_exists_sylow_fixed (hn : n = 4 ∨ n = 5)
    {v : V} (hv : v ≠ 0) :
    SingularDiagonal U W (form eV) v ↔
      ∃ P : Sylow 2 M, ∀ m ∈ P, ρ m v = v := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let : Finite (LinearGroup n) := Finite.of_injective
    (fun g : LinearGroup n => (g : BinaryLinear.OuterCyclic.Space n → BinaryLinear.OuterCyclic.Space n))
    DFunLike.coe_injective
  let : Finite M := Finite.of_equiv (MulAut (LinearGroup n)) eM.toEquiv.symm
  rw [singularDiagonal_iff eV hU hW,
    BinaryNaturalDual.ModelOrbits.singularDiagonal_iff_exists_sylow_fixed hn A (by simpa using hv)]
  constructor
  · rintro ⟨P, hP⟩
    refine ⟨P.mapSurjective (f := eM.symm.toMonoidHom) eM.symm.surjective, ?_⟩
    rintro m ⟨a, ha, rfl⟩
    change ρ (eM.symm a) v = v
    apply eV.injective
    rw [hact, eM.apply_symm_apply, hP a ha]
  · rintro ⟨P, hP⟩
    refine ⟨P.mapSurjective (f := eM.toMonoidHom) eM.surjective, ?_⟩
    rintro a ⟨m, hm, rfl⟩
    change A.representation (eM m) (eV v) = eV v
    rw [← hact, hP m hm]

end BinaryNaturalDual.ModelOrbits.MarkedGeometry
