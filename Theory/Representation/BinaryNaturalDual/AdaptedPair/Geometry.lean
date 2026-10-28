module

public import Theory.Representation.BinaryNaturalDual.Action
public import Mathlib.GroupTheory.Sylow

/-!
# Geometric spaces for adapted natural-plus-dual pairs

The moving space attached to (x,f) is geometrically ker(f) ⊕ ann(x).
It is defined independently of any identification with a commutator space.
Fixed spaces and point stabilizers use the actual linear action. The last
section fixes the standard binary coordinates, upper-flag subgroup, and
reversal-twisted graph automorphism used in dimensions four and five.

Source: Aschbacher–Smith, H.9.1, printed pp.389–390, and the corrected
adapted-pair argument recorded in the source audit of 6 October 2026.
-/

@[expose] public section

namespace BinaryNaturalDual.AdaptedPair

variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]

/-- Fixed vectors for the specified subgroup of the actual acting group. -/
def fixedVectors (ρ : G →* (V ≃ₗ[ZMod 2] V)) (H : Subgroup G) : Submodule (ZMod 2) V where
  carrier := {v | ∀ g ∈ H, ρ g v = v}
  zero_mem' := by simp
  add_mem' := by intro x y hx hy g hg; simp [map_add, hx g hg, hy g hg]
  smul_mem' := by intro c x hx g hg; simp [hx g hg]

@[simp] theorem mem_fixedVectors (ρ : G →* (V ≃ₗ[ZMod 2] V)) (H : Subgroup G) (v : V) :
    v ∈ fixedVectors ρ H ↔ ∀ g ∈ H, ρ g v = v := Iff.rfl

/-- The subgroup fixing a vector, without a globally installed action instance. -/
def pointStabilizer (ρ : G →* (V ≃ₗ[ZMod 2] V)) (v : V) : Subgroup G :=
  (MulAction.stabilizer (V ≃ₗ[ZMod 2] V) v).comap ρ

@[simp] theorem mem_pointStabilizer (ρ : G →* (V ≃ₗ[ZMod 2] V)) (v : V) (g : G) :
    g ∈ pointStabilizer ρ v ↔ ρ g v = v := Iff.rfl

/-- The geometric moving space: ker(f) in the natural summand and ann(x)
in the dual summand. The commutator-space identification is separate. -/
def movingSpace (v : Space V) : Submodule (ZMod 2) (Space V) :=
  v.2.ker.prod (Submodule.span (ZMod 2) {v.1}).dualAnnihilator

@[simp] theorem mem_movingSpace (v w : Space V) :
    w ∈ movingSpace v ↔ v.2 w.1 = 0 ∧ w.2 v.1 = 0 := by
  simp only [movingSpace, Submodule.mem_prod, LinearMap.mem_ker,
    Submodule.mem_dualAnnihilator]
  constructor
  · rintro ⟨hf, hx⟩
    exact ⟨hf, hx _ (Submodule.subset_span (Set.mem_singleton _))⟩
  · rintro ⟨hf, hx⟩
    refine ⟨hf, ?_⟩
    intro x hxs
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hxs
    simp [hx]

/-- Inner changes of coordinates carry the geometric moving space to the
moving space of the transported vector. -/
theorem movingSpace_map_inner (g : BinaryLinear.GL V) (v : Space V) :
    (movingSpace v).map (BinaryLinear.NaturalDualFlag.action g).toLinearMap =
      movingSpace (BinaryLinear.NaturalDualFlag.action g v) := by
  apply le_antisymm
  · rintro w ⟨u, hu, rfl⟩
    change u ∈ movingSpace v at hu
    change BinaryLinear.NaturalDualFlag.action g u ∈
      movingSpace (BinaryLinear.NaturalDualFlag.action g v)
    rw [mem_movingSpace] at hu ⊢
    simpa only [BinaryLinear.NaturalDualFlag.action_fst,
      BinaryLinear.NaturalDualFlag.action_snd, LinearEquiv.symm_apply_apply] using hu
  · intro w hw
    refine ⟨BinaryLinear.NaturalDualFlag.action g⁻¹ w, ?_, ?_⟩
    · change BinaryLinear.NaturalDualFlag.action g⁻¹ w ∈ movingSpace v
      rw [mem_movingSpace] at hw ⊢
      simp only [BinaryLinear.NaturalDualFlag.action_fst,
        BinaryLinear.NaturalDualFlag.action_snd] at hw ⊢
      exact hw
    · change (BinaryLinear.NaturalDualFlag.action g *
        BinaryLinear.NaturalDualFlag.action g⁻¹) w = w
      rw [← map_mul, mul_inv_cancel, map_one]
      rfl

/-- Convert the supplied representation into its group of linear equivalences. -/
def linearAction {n : ℕ} (d : CoordinateAction n) :
    MulAut (BinaryLinear.OuterCyclic.LinearGroup n) →*
      (CoordinateSpace n ≃ₗ[ZMod 2] CoordinateSpace n) :=
  (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) (CoordinateSpace n)).toMonoidHom.comp
    d.representation.asGroupHom

@[simp] theorem linearAction_apply {n : ℕ} (d : CoordinateAction n)
    (g : MulAut (BinaryLinear.OuterCyclic.LinearGroup n)) (v : CoordinateSpace n) :
    linearAction d g v = d.representation g v := rfl

@[simp] theorem linearAction_inner {n : ℕ} (d : CoordinateAction n)
    (g : BinaryLinear.OuterCyclic.LinearGroup n) (v : CoordinateSpace n) :
    linearAction d (MulAut.conj g) v = BinaryLinear.NaturalDualFlag.action g v :=
  d.on_inner g v

/-- The ith standard natural vector (indices in Lean are zero-based). -/
def axis {n : ℕ} (i : Fin n) : BinaryLinear.OuterCyclic.Space n := Pi.single i 1

/-- The ith coordinate covector. -/
def coordinateForm {n : ℕ} (i : Fin n) :
    Module.Dual (ZMod 2) (BinaryLinear.OuterCyclic.Space n) := LinearMap.proj i

@[simp] theorem coordinateForm_apply {n : ℕ} (i : Fin n)
    (x : BinaryLinear.OuterCyclic.Space n) : coordinateForm i x = x i := rfl

@[simp] theorem coordinateForm_axis {n : ℕ} (i j : Fin n) :
    coordinateForm i (axis j) = if i = j then 1 else 0 := by
  simp [axis, Pi.single_apply]

/-- Reversal of the ordered coordinate basis. -/
def reversal (n : ℕ) : BinaryLinear.OuterCyclic.LinearGroup n where
  toFun x i := x i.rev
  invFun x i := x i.rev
  left_inv x := by ext i; simp
  right_inv x := by ext i; simp
  map_add' x y := rfl
  map_smul' c x := rfl

@[simp] theorem reversal_apply (n : ℕ) (x : BinaryLinear.OuterCyclic.Space n) (i : Fin n) :
    reversal n x i = x i.rev := rfl

/-- The initial coordinate subspace of length k. -/
def initialSpace (n k : ℕ) : Submodule (ZMod 2) (BinaryLinear.OuterCyclic.Space n) :=
  Submodule.span (ZMod 2) {x | ∃ i : Fin n, i.val < k ∧ x = axis i}

/-- The actual full upper-flag stabilizer. Over F₂ its diagonal is one. -/
def upperGroup (n : ℕ) : Subgroup (BinaryLinear.OuterCyclic.LinearGroup n) :=
  ⨅ k : Fin n, BinaryLinear.parabolic (initialSpace n (k.val + 1))

/-- The actual subgroup of inner automorphisms. -/
def innerGroup (n : ℕ) : Subgroup (MulAut (BinaryLinear.OuterCyclic.LinearGroup n)) :=
  (MulAut.conj : BinaryLinear.OuterCyclic.LinearGroup n →*
    MulAut (BinaryLinear.OuterCyclic.LinearGroup n)).range

/-- Reversal followed by the graph automorphism, acting as (x,f) ↦ (Jf,Jx). -/
noncomputable def tau (n : ℕ) : MulAut (BinaryLinear.OuterCyclic.LinearGroup n) :=
  MulAut.conj (reversal n) * BinaryLinear.OuterCyclic.graphLinear n

/-- The concrete subgroup generated by upper unitriangular inner actors and tau. -/
noncomputable def standardGroup (n : ℕ) :
    Subgroup (MulAut (BinaryLinear.OuterCyclic.LinearGroup n)) :=
  (upperGroup n).map MulAut.conj ⊔ Subgroup.zpowers (tau n)

/-- Standard nonsingular pair in dimension four: (e₃,e₂*+e₃*). -/
def vectorFour : CoordinateSpace 4 := (axis 2, coordinateForm 1 + coordinateForm 2)

/-- Standard nonsingular pair in dimension five: (e₃,e₃*). -/
def vectorFive : CoordinateSpace 5 := (axis 2, coordinateForm 2)

/-- The standard fixed vector (e₁,eₙ*). -/
def fixedVector (n : ℕ) [NeZero n] : CoordinateSpace n :=
  (axis 0, coordinateForm (Fin.last (n - 1) |>.cast (Nat.sub_add_cancel (NeZero.pos n))))

@[simp] theorem quadratic_vectorFour : quadratic vectorFour = 1 := by
  simp [vectorFour, axis]

@[simp] theorem quadratic_vectorFive : quadratic vectorFive = 1 := by
  simp [vectorFive, axis]

/-- The outer actor fixing the chosen four-dimensional pair. Its fixing and
involution properties belong to the explicit standard-coordinate calculation. -/
noncomputable def outerFour : MulAut (BinaryLinear.OuterCyclic.LinearGroup 4) :=
  MulAut.conj (BinaryLinear.transvection (axis 1) (coordinateForm 2) (by simp [axis])) * tau 4

/-- The chosen five-dimensional outer actor. -/
noncomputable def outerFive : MulAut (BinaryLinear.OuterCyclic.LinearGroup 5) := tau 5

theorem fixedVector_ne_zero (n : ℕ) [NeZero n] : fixedVector n ≠ 0 := by
  intro h
  have hh := congrArg (fun v : CoordinateSpace n => v.1 0) h
  simp [fixedVector, axis] at hh

theorem finrank_fixedVector_span (n : ℕ) [NeZero n] :
    Module.finrank (ZMod 2) (Submodule.span (ZMod 2) {fixedVector n}) = 1 :=
  finrank_span_singleton (fixedVector_ne_zero n)

theorem fixedVector_mem_movingSpace_four : fixedVector 4 ∈ movingSpace vectorFour := by
  simp [mem_movingSpace, fixedVector, vectorFour, axis]

theorem fixedVector_mem_movingSpace_five : fixedVector 5 ∈ movingSpace vectorFive := by
  simp [mem_movingSpace, fixedVector, vectorFive, axis]

end BinaryNaturalDual.AdaptedPair
