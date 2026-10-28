module

public import Theory.Representation.BinaryNaturalDual.VectorStabilizers.Pair
public import Theory.SpecificGroups.BinaryLinear.OuterCyclic
public import Theory.SpecificGroups.BinaryLinear.Perfect
public import Theory.GroupTheory.PResidual.Defs

/-!
# Inner vector stabilizers in the actual automorphism group

Under the specified coordinate action, a nonzero pure vector has only inner
stabilizers: graph-times-inner operators send it to the other summand. The
inner stabilizer of a pairing-one vector is the actual matrix pair stabilizer,
hence the full linear group in one lower dimension. Its perfectness implies
that it equals its two-residual. All residuals are embedded through their
actual subgroup inclusions.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), H.9.1(3–4),
printed pp.389–390. `CoordinateAction` is the explicit action input; these
results do not assume any stabilizer identification or residual equality.
-/

@[expose] public section

namespace BinaryNaturalDual.VectorStabilizers
open BinaryLinear.OuterCyclic

/-- The actual vector stabilizer of a representation, as a subgroup of its actor. -/
def representationStabilizer {G W : Type*} [Group G] [AddCommGroup W]
    [Module (ZMod 2) W] (ρ : Representation (ZMod 2) G W) (v : W) : Subgroup G where
  carrier := {g | ρ g v = v}
  one_mem' := by simp
  mul_mem' := by
    intro g k hg hk
    change ρ g v = v at hg
    change ρ k v = v at hk
    change ρ (g * k) v = v
    rw [map_mul, Module.End.mul_apply, hk, hg]
  inv_mem' := by
    intro g hg
    change ρ g v = v at hg
    change ρ g⁻¹ v = v
    calc
      ρ g⁻¹ v = ρ g⁻¹ (ρ g v) := congrArg (ρ g⁻¹) hg.symm
      _ = v := by rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one]; rfl

@[simp] theorem mem_representationStabilizer {G W : Type*} [Group G] [AddCommGroup W]
    [Module (ZMod 2) W] (ρ : Representation (ZMod 2) G W) (v : W) (g : G) :
    g ∈ representationStabilizer ρ v ↔ ρ g v = v := Iff.rfl

/-- `C_M(v)` in the specified action of the actual automorphism group. -/
def fullStabilizer {n : ℕ} (d : CoordinateAction n) (v : CoordinateSpace n) :
    Subgroup (MulAut (LinearGroup n)) := representationStabilizer d.representation v

/-- `C_L(v)`, embedded in `M`, with `L` the actual inner subgroup. -/
def innerStabilizer {n : ℕ} (d : CoordinateAction n) (v : CoordinateSpace n) :
    Subgroup (MulAut (LinearGroup n)) := MulAut.innerSubgroup _ ⊓ fullStabilizer d v

/-- The simultaneous fixer of the two pure components. -/
def componentStabilizer {n : ℕ} (d : CoordinateAction n) (x : BinaryLinear.OuterCyclic.Space n)
    (f : Module.Dual (ZMod 2) (BinaryLinear.OuterCyclic.Space n)) : Subgroup (MulAut (LinearGroup n)) :=
  fullStabilizer d (x, 0) ⊓ fullStabilizer d (0, f)

/-- The specified natural action detects the inner conjugating matrix. -/
theorem inner_injective {n : ℕ} (d : CoordinateAction n) :
    Function.Injective (MulAut.conj : LinearGroup n →* MulAut (LinearGroup n)) := by
  intro g k hg
  apply LinearEquiv.ext
  intro v
  have he := congrArg (fun a : MulAut (LinearGroup n) => (d.representation a (v, 0)).1) hg
  simpa only [d.on_inner, naturalDualRepresentation_apply] using he

/-- A graph-times-inner element carries the first pure summand into the second. -/
theorem graph_inner_pure {n : ℕ} (d : CoordinateAction n) (g : LinearGroup n) (x : BinaryLinear.OuterCyclic.Space n) :
    (d.representation (graphLinear n * MulAut.conj g) (x, 0)).1 = 0 := by
  rw [map_mul, Module.End.mul_apply, d.on_inner, d.on_graph,
    naturalDualRepresentation_apply, coordinateSwap_apply]
  simp

/-- A nonzero pure vector has no outer stabilizer. -/
theorem pure_fullStabilizer_le_inner {n : ℕ} (hn : n = 4 ∨ n = 5)
    (d : CoordinateAction n) {x : BinaryLinear.OuterCyclic.Space n} (hx : x ≠ 0) :
    fullStabilizer d (x, 0) ≤ MulAut.innerSubgroup _ := by
  intro a ha
  obtain ⟨g, rfl | rfl⟩ := inner_graph hn a
  · exact ⟨g, rfl⟩
  · have he := congrArg Prod.fst ha
    exact False.elim (hx ((graph_inner_pure d g x).symm.trans he).symm)

/-- `C_M(x)=C_L(x)` for every nonzero pure vector. -/
theorem pure_fullStabilizer_eq_innerStabilizer {n : ℕ} (hn : n = 4 ∨ n = 5)
    (d : CoordinateAction n) {x : BinaryLinear.OuterCyclic.Space n} (hx : x ≠ 0) :
    fullStabilizer d (x, 0) = innerStabilizer d (x, 0) :=
  (inf_eq_right.mpr (pure_fullStabilizer_le_inner hn d hx)).symm

/-- An inner automorphism fixes the sum precisely when its matrix fixes the pair. -/
theorem innerStabilizer_eq_map_pairStabilizer {n : ℕ} (d : CoordinateAction n)
    (x : BinaryLinear.OuterCyclic.Space n) (f : Module.Dual (ZMod 2) (BinaryLinear.OuterCyclic.Space n)) :
    innerStabilizer d (x, f) = (pairStabilizer x f).map MulAut.conj := by
  ext a
  constructor
  · rintro ⟨⟨g, rfl⟩, hg⟩
    refine ⟨g, (mem_pairStabilizer_iff_action x f g).mpr ?_, rfl⟩
    exact (d.on_inner g (x,f)).symm.trans hg
  · rintro ⟨g, hg, rfl⟩
    exact ⟨⟨g, rfl⟩, (d.on_inner g (x,f)).trans
      ((mem_pairStabilizer_iff_action x f g).mp hg)⟩

/-- Fixing the two pure components separately is the inner stabilizer of their sum. -/
theorem componentStabilizer_eq_innerStabilizer {n : ℕ} (hn : n = 4 ∨ n = 5)
    (d : CoordinateAction n) {x : BinaryLinear.OuterCyclic.Space n} (hx : x ≠ 0)
    (f : Module.Dual (ZMod 2) (BinaryLinear.OuterCyclic.Space n)) :
    componentStabilizer d x f = innerStabilizer d (x, f) := by
  apply le_antisymm
  · intro a ha
    refine ⟨pure_fullStabilizer_le_inner hn d hx ha.1, ?_⟩
    change d.representation a (x, f) = (x, f)
    have hadd : (x,f) = (x,0) + (0,f) := by simp
    rw [hadd, map_add, ha.1, ha.2]
  · rintro a ⟨⟨g, rfl⟩, hg⟩
    have hg' : naturalDualRepresentation g (x,f) = (x,f) :=
      (d.on_inner g (x,f)).symm.trans hg
    rw [naturalDualRepresentation_apply, Prod.mk.injEq] at hg'
    constructor
    · change d.representation (MulAut.conj g) (x,0) = (x,0)
      rw [d.on_inner, naturalDualRepresentation_apply, hg'.1, map_zero]
    · change d.representation (MulAut.conj g) (0,f) = (0,f)
      rw [d.on_inner, naturalDualRepresentation_apply, hg'.2, map_zero]

/-- The actual inner vector stabilizer is identified with the matrix pair stabilizer. -/
noncomputable def innerStabilizerEquivPair {n : ℕ} (d : CoordinateAction n)
    (x : BinaryLinear.OuterCyclic.Space n) (f : Module.Dual (ZMod 2) (BinaryLinear.OuterCyclic.Space n)) :
    innerStabilizer d (x, f) ≃* pairStabilizer x f :=
  (MulEquiv.subgroupCongr (innerStabilizer_eq_map_pairStabilizer d x f)).trans
    ((pairStabilizer x f).equivMapOfInjective MulAut.conj (inner_injective d)).symm

/-- Restriction identifies the actual inner stabilizer with the full kernel group. -/
noncomputable def innerStabilizerEquivKernel {n : ℕ} (d : CoordinateAction n)
    {x : BinaryLinear.OuterCyclic.Space n} {f : Module.Dual (ZMod 2) (BinaryLinear.OuterCyclic.Space n)} (h : f x = 1) :
    innerStabilizer d (x, f) ≃* BinaryLinear.GL f.ker :=
  (innerStabilizerEquivPair d x f).trans (pairStabilizerEquivKernel h)

end BinaryNaturalDual.VectorStabilizers

namespace BinaryNaturalDual.VectorStabilizers
open BinaryLinear.OuterCyclic

/-- Coordinates on the hyperplane, of the exact expected dimension. -/
noncomputable def kernelCoordinates {n : ℕ} {x : BinaryLinear.OuterCyclic.Space n}
    {f : Module.Dual (ZMod 2) (BinaryLinear.OuterCyclic.Space n)} (h : f x = 1) :
    f.ker ≃ₗ[ZMod 2] BinaryLinear.OuterCyclic.Space (n - 1) :=
  LinearEquiv.ofFinrankEq _ _ (by
    have hd := finrank_kernel h
    simp only [BinaryLinear.OuterCyclic.Space, Module.finrank_pi, Fintype.card_fin] at hd ⊢
    omega)

/-- Coordinate change on the full linear automorphism group of the kernel. -/
noncomputable def kernelGroupCoordinates {n : ℕ} {x : BinaryLinear.OuterCyclic.Space n}
    {f : Module.Dual (ZMod 2) (BinaryLinear.OuterCyclic.Space n)} (h : f x = 1) :
    BinaryLinear.GL f.ker ≃* LinearGroup (n - 1) :=
  (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) f.ker).symm.trans
    ((LinearMap.GeneralLinearGroup.congrLinearEquiv (kernelCoordinates h)).trans
      (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) (BinaryLinear.OuterCyclic.Space (n - 1))))

/-- The matrix pair stabilizer is a genuine linear group in one lower dimension. -/
noncomputable def pairStabilizerEquivLinear {n : ℕ} {x : BinaryLinear.OuterCyclic.Space n}
    {f : Module.Dual (ZMod 2) (BinaryLinear.OuterCyclic.Space n)} (h : f x = 1) :
    pairStabilizer x f ≃* LinearGroup (n - 1) :=
  (pairStabilizerEquivKernel h).trans (kernelGroupCoordinates h)

/-- The inner automorphism stabilizer is a genuine linear group, via its action. -/
noncomputable def innerStabilizerEquivLinear {n : ℕ} (d : CoordinateAction n)
    {x : BinaryLinear.OuterCyclic.Space n} {f : Module.Dual (ZMod 2) (BinaryLinear.OuterCyclic.Space n)} (h : f x = 1) :
    innerStabilizer d (x,f) ≃* LinearGroup (n - 1) :=
  (innerStabilizerEquivKernel d h).trans (kernelGroupCoordinates h)

/-- Comparison with the actual projective special linear quotient. -/
noncomputable def innerStabilizerEquivProjective {n : ℕ} (hn : n = 4 ∨ n = 5)
    (d : CoordinateAction n) {x : BinaryLinear.OuterCyclic.Space n} {f : Module.Dual (ZMod 2) (BinaryLinear.OuterCyclic.Space n)}
    (h : f x = 1) : innerStabilizer d (x,f) ≃*
      Matrix.ProjectiveSpecialLinearGroup (Fin (n - 1)) (ZMod 2) :=
  (innerStabilizerEquivLinear d h).trans (projectiveEquivLinear (by omega)).symm

theorem innerStabilizer_isPerfect {n : ℕ} (hn : n = 4 ∨ n = 5)
    (d : CoordinateAction n) {x : BinaryLinear.OuterCyclic.Space n} {f : Module.Dual (ZMod 2) (BinaryLinear.OuterCyclic.Space n)}
    (h : f x = 1) : Group.IsPerfect (innerStabilizer d (x,f)) := by
  let : Group.IsPerfect (LinearGroup (n - 1)) :=
    BinaryLinear.linearGroup_isPerfect (n - 1) (by omega)
  exact Group.IsPerfect.ofSurjective
    (f := (innerStabilizerEquivLinear d h).symm.toMonoidHom)
    (innerStabilizerEquivLinear d h).symm.surjective

private theorem perfect_twoResidual_eq_top {G : Type*} [Group G] [Finite G]
    [Group.IsPerfect G] : pResidual 2 G = ⊤ := by
  apply (pResidual_eq_top_iff 2 G).mpr
  intro N hN hp
  let := hN
  have hs : Subsingleton (G ⧸ N) := by
    by_contra! hn
    exact Group.IsPerfect.not_isNilpotent (G ⧸ N) hp.isNilpotent
  apply top_unique
  intro g _
  exact (QuotientGroup.eq_one_iff g).mp (Subsingleton.elim _ _)

/-- The two-residual of the actual inner nonsingular stabilizer is the entire stabilizer. -/
theorem innerStabilizer_twoResidual {n : ℕ} (hn : n = 4 ∨ n = 5)
    (d : CoordinateAction n) {x : BinaryLinear.OuterCyclic.Space n} {f : Module.Dual (ZMod 2) (BinaryLinear.OuterCyclic.Space n)}
    (h : f x = 1) : pResidual 2 (innerStabilizer d (x,f)) = ⊤ := by
  let : Finite (LinearGroup (n - 1)) := Finite.of_injective
    (fun g : LinearGroup (n - 1) => (g : BinaryLinear.OuterCyclic.Space (n - 1) → BinaryLinear.OuterCyclic.Space (n - 1)))
    DFunLike.coe_injective
  let : Finite (innerStabilizer d (x,f)) :=
    Finite.of_injective (innerStabilizerEquivLinear d h) (innerStabilizerEquivLinear d h).injective
  let := innerStabilizer_isPerfect hn d h
  exact perfect_twoResidual_eq_top

/-- `L_v` is the embedded two-residual, not the two-core. -/
def innerResidual {n : ℕ} (d : CoordinateAction n) (v : CoordinateSpace n) :
    Subgroup (MulAut (LinearGroup n)) :=
  (pResidual 2 (innerStabilizer d v)).map (innerStabilizer d v).subtype

/-- The source two-residual equals the inner stabilizer for every nonsingular pair. -/
theorem innerResidual_eq_innerStabilizer {n : ℕ} (hn : n = 4 ∨ n = 5)
    (d : CoordinateAction n) {x : BinaryLinear.OuterCyclic.Space n} {f : Module.Dual (ZMod 2) (BinaryLinear.OuterCyclic.Space n)}
    (h : f x = 1) : innerResidual d (x,f) = innerStabilizer d (x,f) := by
  rw [innerResidual, innerStabilizer_twoResidual hn d h, ← MonoidHom.range_eq_map,
    Subgroup.range_subtype]

/-- In particular, fixing the two pure components is exactly `L_v`. -/
theorem componentStabilizer_eq_innerResidual {n : ℕ} (hn : n = 4 ∨ n = 5)
    (d : CoordinateAction n) {x : BinaryLinear.OuterCyclic.Space n} {f : Module.Dual (ZMod 2) (BinaryLinear.OuterCyclic.Space n)}
    (h : f x = 1) : componentStabilizer d x f = innerResidual d (x,f) := by
  rw [componentStabilizer_eq_innerStabilizer hn d (vector_ne_zero h),
    innerResidual_eq_innerStabilizer hn d h]

end BinaryNaturalDual.VectorStabilizers
