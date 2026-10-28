module
public import Theory.Representation.PSL3Two.FanoTransvectionTensors
public import Theory.SpecificGroups.PSp4Three.Transvections
public import Theory.SpecificGroups.SymplecticSix.FixedRadical

/-!
# The Fano-core subgroup of binary symplectic six-space

The tensor of an even Fano word is a square-zero displacement on any
embedded isotropic three-space. Adding the identity gives an injective
homomorphism from the six-dimensional permutation core to Sp₆(2).
The map retains the embedding and therefore its seven original directions.
It is used to identify the actual plane two-core in 13.4.9, printed p.906.
The transvection carrier is the existing attributed ATLAS port in
PSp4Three.Transvections; see LICENSES/ATLAS.txt.
-/

@[expose] public section
namespace BinaryLinearThree.FanoTransvection
open Matrix
open Theory.SpecificGroups.SymplecticSix
open Theory.SpecificGroups.SymplecticSix.TwoLocalCover
local notation "F" => ZMod 2
local notation "V₆" => Theory.SpecificGroups.SymplecticSix.Vector F
variable (b : BinaryLinearThree.Vector →ₗ[F] V₆)
    (hb : ∀ v w, form F (b v) (b w) = 0)

noncomputable def shearElement (a : Core) : Sp F :=
  ⟨LinearMap.toMatrix' (LinearMap.id + displacement (form F) b a),
    Matrix.PSp4Three.mem_iff_preserves.mpr (by
      intro x y
      simpa only [LinearMap.toMatrix'_mulVec, LinearMap.add_apply, LinearMap.id_apply,
        form, Matrix.PSp4Three.form]
        using displacement_preserves (form F) b hb form_alternating a x y)⟩

theorem shearElement_apply (a : Core) (x : V₆) :
    shearElement b hb a • x = x + displacement (form F) b a x := by
  change LinearMap.toMatrix' _ *ᵥ x = _
  rw [LinearMap.toMatrix'_mulVec]
  rfl

theorem shearElement_zero : shearElement b hb 0 = 1 := by
  apply Matrix.PSp4Three.ext_action
  intro x
  rw [shearElement_apply,displacement_zero]
  simp

theorem shearElement_add (a c : Core) :
    shearElement b hb (a + c) = shearElement b hb a * shearElement b hb c := by
  apply Matrix.PSp4Three.ext_action
  intro x
  simp only [mul_smul,shearElement_apply,displacement_add,LinearMap.add_apply,map_add,
    displacement_composite (form F) b hb,add_zero]
  abel

noncomputable def shear : Multiplicative Core →* Sp F where
  toFun a := shearElement b hb a.toAdd
  map_one' := shearElement_zero b hb
  map_mul' a c := shearElement_add b hb a.toAdd c.toAdd

theorem shear_injective (hi : Function.Injective b) : Function.Injective (shear b hb) := by
  intro a c hac
  change a.toAdd = c.toAdd
  apply displacement_injective (form F) form_nondegenerate b hi
  apply LinearMap.ext
  intro x
  have hh := congrArg (fun g : Sp F => g • x) hac
  change shearElement b hb a.toAdd • x = shearElement b hb c.toAdd • x at hh
  simpa only [shearElement_apply,add_right_inj] using hh

/-- The point complement is exactly the transvection in its marked direction. -/
theorem shear_pointSpike (p : BinaryLinearThree.Point) :
    shear b hb (Multiplicative.ofAdd (BinaryLinearThree.FanoDecomposition.pointSpike p)) =
      Matrix.PSp4Three.transvection (b p.val) 1 := by
  apply Matrix.PSp4Three.ext_action
  intro x
  change shearElement b hb (BinaryLinearThree.FanoDecomposition.pointSpike p) • x = _
  rw [shearElement_apply,displacement_pointSpike,Matrix.PSp4Three.transvection_apply,one_mul]
  rfl

/-- Conjugation agrees with the actual seven-point permutation representation. -/
theorem shear_equivariant (g : Sp F) (k : BinaryLinearThree.Group)
    (hk : ∀ v : BinaryLinearThree.Vector, g • b v = b (k • v)) (a : Core) :
    shear b hb (Multiplicative.ofAdd (U₂ k a)) =
      g * shear b hb (Multiplicative.ofAdd a) * g⁻¹ := by
  apply Matrix.PSp4Three.ext_action
  intro x
  obtain ⟨y,rfl⟩ := (toLinear g).surjective x
  change shearElement b hb (U₂ k a) • (g • y) =
    (g * shearElement b hb a * g⁻¹) • (g • y)
  rw [shearElement_apply,mul_smul,mul_smul,inv_smul_smul,shearElement_apply]
  change _ = toLinear g (y + displacement (form F) b a y)
  rw [map_add,displacement_equivariant (form F) b (toLinear g) k
    (fun x y => preserves_form g x y) hk]
  rfl

end BinaryLinearThree.FanoTransvection
