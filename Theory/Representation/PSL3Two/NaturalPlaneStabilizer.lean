module

public import Theory.Representation.PSL3Two.SteinbergStructure.PointRadicalFixedSpace.NaturalParabolics
public import Theory.SpecificGroups.PSL3Two.Parabolics.Cores.Identification

/-!
# Stabilizers of arbitrary planes in the natural binary three-space

An adapted basis identifies any binary plane with v₂=0. Over F₂ every
invertible change of basis has determinant one, so this is the literal
SL₃(2) conjugation. This transports the plane stabilizer to the standard
line parabolic without changing the given natural action.

Source: Aschbacher–Smith,J.4,second-parabolic setup,printed p.440.
-/

public section
noncomputable section
open Subgroup Representation Matrix
open scoped Pointwise
namespace BinaryLinearThree.NaturalPlaneStabilizer
open Matrix.PSL3Two

/-- The coordinate plane used by the standard line parabolic. -/
def standard : Submodule (ZMod 2) Vector :=
  (LinearMap.proj (2 : Fin 3) : Vector →ₗ[ZMod 2] ZMod 2).ker

/-- Membership in the coordinate plane, without exposing its definition body. -/
theorem mem_standard (v : Vector) : v ∈ standard ↔ v 2 = 0 := Iff.rfl

private theorem standard_card : Nat.card standard = 4 := by
  change Nat.card {v : Vector // v 2 = 0} = 4
  rw [Nat.card_eq_fintype_card]
  decide +kernel

theorem standard_finrank : Module.finrank (ZMod 2) standard = 2 := by
  apply Nat.pow_right_injective (by decide : 1 < 2)
  have h := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := standard)
  rw [Nat.card_zmod,standard_card] at h
  exact h.symm

/-- An actual determinant-one matrix sends the coordinate plane to the given plane. -/
theorem exists_matrix (A : Submodule (ZMod 2) Vector)
    (hA : Module.finrank (ZMod 2) A = 2) :
    ∃ g : Group, ∀ v : Vector, W g v ∈ A ↔ v ∈ standard := by
  let e : standard ≃ₗ[ZMod 2] A := LinearEquiv.ofFinrankEq _ _ (standard_finrank.trans hA.symm)
  obtain ⟨f,hf⟩ := Submodule.exists_linearEquiv_restrict_eq e
  have hm (v : Vector) : f v ∈ A ↔ v ∈ standard := by
    constructor
    · intro hv
      let w := e.symm ⟨f v,hv⟩
      have hw : f w = f v := (hf w).symm.trans (congrArg Subtype.val (e.apply_symm_apply _))
      exact (f.injective hw) ▸ w.property
    · intro hv
      rw [← hf ⟨v,hv⟩]
      exact (e ⟨v,hv⟩).property
  let g : Group := ⟨LinearMap.toMatrix' f.toLinearMap, by
    rw [LinearMap.det_toMatrix']
    exact (by decide : ∀ x : ZMod 2, x ≠ 0 → x = 1) _ f.isUnit_det'.ne_zero⟩
  refine ⟨g,fun v => ?_⟩
  change Matrix.toLin' (LinearMap.toMatrix' f.toLinearMap) v ∈ A ↔ _
  rw [Matrix.toLin'_toMatrix']
  exact hm v

/-- Plane stabilization in the literal natural representation. -/
def stabilizer (A : Submodule (ZMod 2) Vector) : Subgroup Group :=
  MulAction.stabilizer Group (A : Set Vector)

/-- The natural stabilizer is the literal set stabilizer. -/
theorem stabilizer_eq (A : Submodule (ZMod 2) Vector) :
    stabilizer A = MulAction.stabilizer Group (A : Set Vector) := by rfl

/-- The coordinate plane has the standard line parabolic as stabilizer. -/
theorem stabilizer_standard : stabilizer standard = lineParabolicSL := by rfl

/-- Membership retains the literal natural matrix action. -/
theorem mem_stabilizer (A : Submodule (ZMod 2) Vector) (g : Group) :
    g ∈ stabilizer A ↔ ∀ v : Vector, W g v ∈ A ↔ v ∈ A :=
  MulAction.mem_stabilizer_set

/-- Every natural plane stabilizer is the actual conjugate line parabolic. -/
theorem exists_stabilizer_eq (A : Submodule (ZMod 2) Vector)
    (hA : Module.finrank (ZMod 2) A = 2) :
    ∃ g : Group, stabilizer A = lineParabolicSL.map (MulAut.conj g).toMonoidHom := by
  obtain ⟨g,hg⟩ := exists_matrix A hA
  have hset : (A : Set Vector) = g • (standard : Set Vector) := by
    ext v
    rw [Set.mem_smul_set_iff_inv_smul_mem]
    change v ∈ A ↔ W g⁻¹ v ∈ standard
    have h := hg (W g⁻¹ v)
    rwa [Representation.self_inv_apply] at h
  refine ⟨g, ?_⟩
  rw [stabilizer,hset,MulAction.stabilizer_smul_eq_stabilizer_map_conj]
  rfl

private def planeCubic : Group :=
  ⟨!![0,1,0; 1,1,0; 0,0,1], by decide +kernel⟩

private theorem planeCubic_cube : planeCubic ^ 3 = 1 := by decide +kernel
private theorem planeCubic_stable : ∀ v : Vector,
    W planeCubic v ∈ standard ↔ v ∈ standard := by
  change ∀ v : Vector, (W planeCubic v) 2 = 0 ↔ v 2 = 0
  decide +kernel
private theorem planeCubic_moves : ∀ v : Vector,
    v ∈ standard → v ≠ 0 → W planeCubic v ≠ v := by
  change ∀ v : Vector, v 2 = 0 → v ≠ 0 → W planeCubic v ≠ v
  decide +kernel

/-- A genuine cubic in each plane stabilizer moves every given nonzero point
of that plane. Its order divides three, which puts it in the two-residual. -/
theorem exists_cubic_moving (A : Submodule (ZMod 2) Vector)
    (hA : Module.finrank (ZMod 2) A = 2) (v : Vector) (hv : v ∈ A) (hv0 : v ≠ 0) :
    ∃ a : stabilizer A, a ^ 3 = 1 ∧ W (a : Group) v ≠ v := by
  obtain ⟨g,hg⟩ := exists_matrix A hA
  have hm (u : Vector) : W g⁻¹ u ∈ standard ↔ u ∈ A := by
    have h := hg (W g⁻¹ u)
    rw [Representation.self_inv_apply] at h
    exact h.symm
  let a := MulAut.conj g planeCubic
  have hstable : a ∈ stabilizer A := by
    rw [mem_stabilizer]
    intro u
    change W (g * planeCubic * g⁻¹) u ∈ A ↔ u ∈ A
    rw [map_mul,map_mul]
    change W g (W planeCubic (W g⁻¹ u)) ∈ A ↔ u ∈ A
    rw [hg,planeCubic_stable,hm]
  refine ⟨⟨a,hstable⟩,?_,?_⟩
  · apply Subtype.ext
    change (MulAut.conj g planeCubic) ^ 3 = 1
    rw [← map_pow,planeCubic_cube,map_one]
  · have hw0 : W g⁻¹ v ≠ 0 := by
      intro h
      have hh := congrArg (W g) h
      rw [Representation.self_inv_apply,map_zero] at hh
      exact hv0 hh
    have hn := planeCubic_moves (W g⁻¹ v) ((hm v).mpr hv) hw0
    intro he
    have hh := congrArg (W g⁻¹) he
    change W g⁻¹ (W (g * planeCubic * g⁻¹) v) = W g⁻¹ v at hh
    rw [map_mul,map_mul] at hh
    change W g⁻¹ (W g (W planeCubic (W g⁻¹ v))) = W g⁻¹ v at hh
    rw [Representation.inv_self_apply] at hh
    exact hn hh

end BinaryLinearThree.NaturalPlaneStabilizer
