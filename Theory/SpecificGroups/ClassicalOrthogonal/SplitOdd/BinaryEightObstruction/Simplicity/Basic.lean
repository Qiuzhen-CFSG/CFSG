/-
Copyright (c) 2026 Gerald Höhn and the ATLAS contributors. All rights reserved.
Covered by the ATLAS Research and Attribution License 1.0 (LICENSES/ATLAS.txt).
Adapted from Atlas/LinearGroups/Orthogonal/{ElementaryNormal,RootSubgroup,
RootNormalGeneration,RootPointStabilizer}.lean, revision
8eabb35afe2b5e45bf913a2d05c53e558d2e2917.
Changes: the existing CFSG carrier, binary singular vectors in place of lines,
and the exact-vector stabilizer argument.
-/
module

public import Theory.SpecificGroups.ClassicalOrthogonal.SplitOdd.BinaryEightObstruction.Rank
public import Mathlib.GroupTheory.GroupAction.Primitive
public import Mathlib.GroupTheory.IsPerfect

/-!
# The binary split-eight singular action and its root subgroups

The points are the nonzero singular vectors of the existing quadratic space.
Over the binary field these are the singular projective points. The natural
action is faithful because the coordinate basis consists of singular vectors.
The additive Siegel parameter map supplies an abelian subgroup, normal in the
stabilizer of its direction. Transitivity on singular vectors implies normal
generation by one such subgroup. These are the local inputs to the Iwasawa
proof of simplicity; neither primitivity nor perfectness is assumed here.
-/

@[expose] public noncomputable section
namespace ClassicalOrthogonal.BinaryEightObstruction.Simplicity
open Theory.AlgebraicGroup Quadratic

abbrev K := ZMod 2
abbrev V := VectorD 4 K
abbrev E := OmegaPlus 4 K
abbrev Q := formD 4 K

/-- Nonzero singular vectors, hence singular points over the binary field. -/
abbrev Point := {v : V // v ≠ 0 ∧ Q v = 0}

/-- The actual natural linear representation, restricted to the elementary group. -/
def linear (g : E) : V ≃ₗ[K] V := g.val.val

theorem linear_preserves (g : E) (v : V) : Q (linear g v) = Q v :=
  (mem_quadraticIsometrySubgroup Q _).mp g.val.prop v

theorem linear_polar (g : E) (v w : V) :
    Q.polarBilin (linear g v) (linear g w) = Q.polarBilin v w := by
  simp only [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar,
    ← map_add, linear_preserves]

instance : MulAction E Point where
  smul g p := ⟨linear g p.val,
    fun h => p.prop.1 ((linear g).injective (h.trans (map_zero _).symm)), (linear_preserves g p.val).trans p.prop.2⟩
  one_smul _ := rfl
  mul_smul _ _ _ := rfl

@[simp] theorem smul_val (g : E) (p : Point) : (g • p).val = linear g p.val := rfl

def pointE (i : Fin 4) : Point := ⟨e i, by
  constructor
  · intro h
    have := congrFun h (.inl i)
    simp [e] at this
  · exact formD_e i⟩

def pointF (i : Fin 4) : Point := ⟨f i, by
  constructor
  · intro h
    have := congrFun h (.inr i)
    simp [f] at this
  · exact formD_f i⟩

instance : Nonempty Point := ⟨pointE 0⟩

instance : FaithfulSMul E Point where
  eq_of_smul_eq_smul h := by
    apply Subtype.ext
    apply Subtype.ext
    apply LinearEquiv.toLinearMap_injective
    apply (Pi.basisFun K (Index 4)).ext
    intro i
    cases i with
    | inl i => simpa only [smul_val, pointE, linear, e, Pi.basisFun_apply, LinearEquiv.coe_coe] using
        congrArg Subtype.val (h (pointE i))
    | inr i => simpa only [smul_val, pointF, linear, f, Pi.basisFun_apply, LinearEquiv.coe_coe] using
        congrArg Subtype.val (h (pointF i))

/-- A Siegel generator as an element of the exact elementary carrier. -/
def root (u v : V) (hu : Q u = 0) (huv : Q.polarBilin u v = 0) : E :=
  ⟨siegelElement Q u v hu huv, siegelElement_mem Q u v hu huv⟩

@[simp] theorem linear_root (u v : V) (hu : Q u = 0)
    (huv : Q.polarBilin u v = 0) (x : V) :
    linear (root u v hu huv) x = siegel Q u v x := rfl

theorem root_zero (u : V) (hu : Q u = 0) : root u 0 hu (by simp) = 1 := by
  apply Subtype.ext
  apply Subtype.ext
  apply LinearEquiv.ext
  exact siegel_zero Q u

theorem root_add (u v w : V) (hu : Q u = 0)
    (hv : Q.polarBilin u v = 0) (hw : Q.polarBilin u w = 0) :
    root u (v + w) hu (by rw [map_add, hv, hw, add_zero]) =
      root u v hu hv * root u w hu hw := by
  apply Subtype.ext
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  exact (siegel_add Q u v w x hu hv hw).symm

theorem root_conj (g : E) (u v : V) (hu : Q u = 0)
    (hv : Q.polarBilin u v = 0) :
    g * root u v hu hv * g⁻¹ = root (linear g u) (linear g v)
      ((linear_preserves g u).trans hu) ((linear_polar g u v).trans hv) := by
  apply Subtype.ext
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  let gi : Q.IsometryEquiv Q := { linear g with map_app' := linear_preserves g }
  change gi (siegel Q u v ((linear g).symm x)) =
    siegel Q (linear g u) (linear g v) x
  rw [siegel_covariant]
  exact congrArg (siegel Q (linear g u) (linear g v)) ((linear g).apply_symm_apply x)

/-- The additive parameter space perpendicular to the singular direction. -/
abbrev Parameter (p : Point) := (Q.polarBilin p.val).ker

def rootHom (p : Point) : Multiplicative (Parameter p) →* E where
  toFun v := root p.val v.toAdd.val p.prop.2 v.toAdd.prop
  map_one' := root_zero p.val p.prop.2
  map_mul' v w := root_add p.val v.toAdd.val w.toAdd.val p.prop.2
    v.toAdd.prop w.toAdd.prop

/-- The actual abelian root subgroup in the elementary group. -/
def rootGroup (p : Point) : Subgroup E := (rootHom p).range

instance (p : Point) : IsMulCommutative (rootGroup p) :=
  inferInstanceAs (IsMulCommutative (rootHom p).range)

theorem rootGroup_le_stabilizer (p : Point) :
    rootGroup p ≤ MulAction.stabilizer E p := by
  rintro g ⟨v, rfl⟩
  apply Subtype.ext
  exact siegel_fix Q p.val v.toAdd.val p.prop.2 v.toAdd.prop

theorem rootGroup_normal_stabilizer (p : Point) :
    ((rootGroup p).subgroupOf (MulAction.stabilizer E p)).Normal := by
  apply (Subgroup.normal_subgroupOf_iff (rootGroup_le_stabilizer p)).mpr
  rintro r g ⟨v, rfl⟩ hg
  have hgp : linear g p.val = p.val := congrArg Subtype.val hg
  have hv : Q.polarBilin p.val (linear g v.toAdd.val) = 0 := by
    rw [← hgp, linear_polar]
    exact v.toAdd.prop
  refine ⟨Multiplicative.ofAdd ⟨linear g v.toAdd.val, hv⟩, ?_⟩
  change root p.val (linear g v.toAdd.val) _ _ = g * root _ _ _ _ * g⁻¹
  simpa only [hgp] using (root_conj g p.val v.toAdd.val p.prop.2 v.toAdd.prop).symm

/-- A normal subgroup containing one whole root subgroup contains every Siegel
generator, provided the singular-vector action is transitive. -/
theorem eq_top_of_rootGroup_le [MulAction.IsPretransitive E Point]
    (p : Point) (N : Subgroup E) [N.Normal] (hN : rootGroup p ≤ N) : N = ⊤ := by
  have hle : elementarySubgroup Q ≤ N.map (elementarySubgroup Q).subtype := by
    apply (Subgroup.closure_le _).mpr
    rintro _ ⟨u, v, hu, hv, rfl⟩
    by_cases hun : u = 0
    · subst u
      have hz : siegelElement Q 0 v hu hv = 1 := by
        apply Subtype.ext
        apply LinearEquiv.ext
        intro x
        change siegel Q 0 v x = x
        simp [siegel]
      rw [hz]
      exact Subgroup.one_mem _
    · obtain ⟨g, hg⟩ := MulAction.exists_smul_eq E p (⟨u, hun, hu⟩ : Point)
      have hgu : linear g p.val = u := congrArg Subtype.val hg
      have hp : Q.polarBilin p.val ((linear g).symm v) = 0 := by
        have h := linear_polar g p.val ((linear g).symm v)
        rw [hgu, (linear g).apply_symm_apply] at h
        exact h.symm.trans hv
      let r := root p.val ((linear g).symm v) p.prop.2 hp
      have hr : r ∈ N := hN ⟨Multiplicative.ofAdd ⟨(linear g).symm v, hp⟩, rfl⟩
      refine ⟨g * r * g⁻¹, (inferInstance : N.Normal).conj_mem r hr g, ?_⟩
      change (g * root _ _ _ _ * g⁻¹).val = _
      rw [root_conj]
      simp only [hgu, LinearEquiv.apply_symm_apply, root]
  apply top_unique
  intro g _
  obtain ⟨z, hz, he⟩ := hle g.prop
  exact (Subtype.ext he : z = g) ▸ hz

theorem rootGroup_normalClosure [MulAction.IsPretransitive E Point] (p : Point) :
    Subgroup.normalClosure (rootGroup p : Set E) = ⊤ :=
  eq_top_of_rootGroup_le p _ (fun _ h => Subgroup.subset_normalClosure h)

end ClassicalOrthogonal.BinaryEightObstruction.Simplicity
