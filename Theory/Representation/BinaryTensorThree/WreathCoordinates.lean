module
public import Theory.Representation.BinaryTensorThree.PointParabolic
public import Theory.SpecificGroups.PSL3Two.Parabolics.MarkedAutomorphisms.NaturalFlag.FixedSpaces

/-!
# Wreath coordinates and the Sylow-fixed tensor point

The binary tensor action of GL₃(2) wr C₂ is faithful: contraction of a pure
tensor forces identity factors, and a factor exchange cannot be the identity.
The canonical SL₃(2) = GL₃(2) identification therefore gives an equivalence
from the literal matrix wreath actor onto the tensor group. Two upper
triangular roots in each factor show that its Sylow-fixed space consists
of zero and the marked pure tensor.

The original-action consumer uses this equivalence and Sylow conjugacy to
construct coordinates at every prescribed nonidentity Sylow-fixed point,
retaining the original module and its action kernel.
Source: Aschbacher--Smith H.4.4 and §8.3, pp.383--385,724.
-/

public noncomputable section
open scoped TensorProduct
open Subgroup
open BinaryPermutation.FiveTensorSquare
namespace BinaryTensorThree

private theorem binary_nonzero_eq_one (a : ZMod 2) (ha : a ≠ 0) : a = 1 :=
  (by decide : ∀ a : ZMod 2, a ≠ 0 → a = 1) a ha

private theorem tensor_identity (a b : Factor)
    (h : ∀ x y : Natural, coordinates (a x ⊗ₜ[ZMod 2] b y) = coordinates (x ⊗ₜ[ZMod 2] y)) :
    a = 1 ∧ b = 1 := by
  have h0 : basisVector 0 ≠ 0 := by
    intro hz
    have hh := congrFun hz 0
    simp [basisVector] at hh
  have hb : b (basisVector 0) ≠ 0 := fun hz =>
    h0 (b.injective (hz.trans b.map_zero.symm))
  obtain ⟨j,hj⟩ : ∃ j, b (basisVector 0) j ≠ 0 := by
    by_contra hn
    apply hb
    funext j
    simpa using not_exists.mp hn j
  have hj1 := binary_nonzero_eq_one _ hj
  have ha (x : Natural) (i : Fin 3) : a x i = x i * basisVector 0 j := by
    have he := congrArg (fun X : Space => X i j) (h x (basisVector 0))
    simpa only [coordinates_tmul,hj1,mul_one] using he
  have hj0 : basisVector 0 j = 1 := by
    apply binary_nonzero_eq_one
    intro hz
    apply h0
    apply a.injective
    ext i
    simp only [ha,hz,mul_zero,Pi.zero_apply]
  have ha1 : a = 1 := by ext x i; rw [ha,hj0,mul_one]; rfl
  refine ⟨ha1,?_⟩
  ext y j
  have he := congrArg (fun X : Space => X 0 j) (h (basisVector 0) y)
  simpa [coordinates_tmul,ha1,basisVector] using he

private theorem tensor_exchange_ne_identity (a b : Factor) :
    ¬ (∀ x y : Natural,
      coordinates (a y ⊗ₜ[ZMod 2] b x) = coordinates (x ⊗ₜ[ZMod 2] y)) := by
  intro h
  have h0 : basisVector 0 ≠ 0 := by
    intro hz
    have hh := congrFun hz 0
    simp [basisVector] at hh
  have hb : b (basisVector 0) ≠ 0 := fun hz =>
    h0 (b.injective (hz.trans b.map_zero.symm))
  obtain ⟨j,hj⟩ : ∃ j, b (basisVector 0) j ≠ 0 := by
    by_contra hn
    apply hb
    funext j
    simpa using not_exists.mp hn j
  have hj1 := binary_nonzero_eq_one _ hj
  obtain ⟨k,hkj⟩ := exists_ne j
  have hk : a (basisVector k) = 0 := by
    ext i
    have he := congrArg (fun X : Space => X i j) (h (basisVector 0) (basisVector k))
    simp only [coordinates_tmul] at he
    rw [hj1,mul_one] at he
    simpa [basisVector,Ne.symm hkj] using he
  have he := congrFun (a.injective (hk.trans a.map_zero.symm)) k
  simp [basisVector] at he

theorem wreathHom_injective : Function.Injective wreathHom := by
  apply (injective_iff_map_eq_one wreathHom).mpr
  intro w hw
  have hh (x y : Natural) : action (wreathMap w) (coordinates (x ⊗ₜ[ZMod 2] y)) =
      coordinates (x ⊗ₜ[ZMod 2] y) := by
    change action (wreathHom w) _ = _
    rw [hw,map_one]
    rfl
  rcases index_cases w.right with hr | hr
  · have hi := tensor_identity (w.left 1) (w.left swapIndex) (fun x y => by
      have he := hh x y
      simpa only [wreathMap,hr,ite_true,action_baseEmbedding,baseAction_tmul] using he)
    apply RegularWreathProduct.ext
    · funext i
      rcases index_cases i with rfl | rfl
      · exact hi.1
      · exact hi.2
    · exact hr
  · apply False.elim
    apply tensor_exchange_ne_identity (w.left 1) (w.left swapIndex)
    intro x y
    have he := hh x y
    simp only [wreathMap,hr,swapIndex_ne_one,ite_false,map_mul,Module.End.mul_apply,
      action_swap,action_baseEmbedding,←coordinates_swap,TensorProduct.comm_tmul,
      baseAction_tmul] at he
    exact he

noncomputable def wreathEquiv : Wreath ≃* Group :=
  MulEquiv.ofBijective wreathHom ⟨wreathHom_injective,wreathHom_surjective⟩

namespace PointParabolic
private def naturalEquiv : Matrix.PSL3Two.SL ≃* Factor :=
  Matrix.PSL3Two.equivGL.trans ((Matrix.GeneralLinearGroup.toLin (n := Fin 3) (R := ZMod 2)).trans
    (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) Natural))

private theorem naturalEquiv_apply (g : Matrix.PSL3Two.SL) :
    naturalEquiv g = Matrix.SpecialLinearGroup.toLin' g := by
  rw [naturalEquiv, MulEquiv.trans_apply, Matrix.PSL3Two.equivGL_apply]
  rfl

noncomputable def actorEquiv : Actor ≃* Group :=
  (RegularWreathProduct.congr naturalEquiv (MulEquiv.refl _)).trans wreathEquiv

theorem actorEquiv_apply (g : Actor) : actorEquiv g = tensorHom g := by
  rw [tensorHom_eq_wreathHom]
  apply congrArg wreathHom
  apply RegularWreathProduct.ext
  · funext i
    exact naturalEquiv_apply (g.left i)
  · rfl
end PointParabolic

private theorem baseAction_left (g : Factor) (X : Space) (i j : Fin 3) :
    baseAction (g,1) X i j = g (fun k => X k j) i := by
  obtain ⟨x,rfl⟩ := coordinates.surjective X
  induction x using TensorProduct.induction_on with
  | zero =>
    simp only [map_zero]
    exact (congrArg (fun x : Natural => x _) g.map_zero).symm
  | tmul x y =>
    rw [baseAction_tmul]
    simp only [coordinates_tmul]
    change g x i * y j = g (fun k => x k * y j) i
    simp only [mul_comm (x _) (y j)]
    change g x i * y j = g (y j • x) i
    rw [map_smul]
    exact mul_comm _ _
  | add x y hx hy =>
    simp only [map_add,Matrix.add_apply]
    change _ = g ((fun k => coordinates x k j) + (fun k => coordinates y k j)) i
    rw [map_add]
    exact congrArg₂ (· + ·) hx hy

private theorem baseAction_right (g : Factor) (X : Space) (i j : Fin 3) :
    baseAction (1,g) X i j = g (X i) j := by
  obtain ⟨x,rfl⟩ := coordinates.surjective X
  induction x using TensorProduct.induction_on with
  | zero =>
    simp only [map_zero]
    exact (congrArg (fun x : Natural => x _) g.map_zero).symm
  | tmul x y =>
    rw [baseAction_tmul]
    simp only [coordinates_tmul]
    change x i * g y j = g (x i • y) j
    rw [map_smul]
    rfl
  | add x y hx hy =>
    simp only [map_add,Matrix.add_apply]
    change _ = g (coordinates x i + coordinates y i) j
    rw [map_add]
    exact congrArg₂ (· + ·) hx hy

namespace PointParabolic
open Matrix.PSL3Two

private def baseActor (a b : SL) : Actor :=
  ⟨fun i => if i = 1 then a else b,1⟩

private theorem tensorHom_base (a b : SL) :
    tensorHom (baseActor a b) =
      baseEmbedding (Matrix.SpecialLinearGroup.toLin' a,Matrix.SpecialLinearGroup.toLin' b) := by
  rw [tensorHom_eq_wreathHom]
  simp [wreathHom,wreathMap,baseActor]

private theorem baseActor_mem (a b : SL) (ha : a ∈ borelSL) (hb : b ∈ borelSL) :
    baseActor a b ∈ WreathPair.borel := by
  intro i
  change (if i = 1 then a else b) ∈ borelSL
  split <;> assumption

/-- Every fixed vector of the actual tensor Sylow is zero or the marked pure tensor. -/
theorem sylow_fixed_eq_zero_or_point (X : Space)
    (hX : ∀ a ∈ WreathPair.borel, action (tensorHom a) X = X) : X = 0 ∨ X = point := by
  have hcol (j : Fin 3) : X 1 j = 0 ∧ X 2 j = 0 := by
    apply MarkedAutomorphisms.NaturalFlag.borel_fixed_mem_point
      (Multiplicative.ofAdd (fun i => X i j))
    intro a ha
    have he := hX (baseActor a 1) (baseActor_mem a 1 ha (Subgroup.one_mem _))
    rw [tensorHom_base,action_baseEmbedding,map_one] at he
    apply Multiplicative.toAdd.injective
    rw [MarkedAutomorphisms.NaturalFlag.slAut_apply]
    ext i
    have hi := congrArg (fun Y : Space => Y i j) he
    rw [baseAction_left] at hi
    exact hi
  have hrow (i : Fin 3) : X i 1 = 0 ∧ X i 2 = 0 := by
    apply MarkedAutomorphisms.NaturalFlag.borel_fixed_mem_point
      (Multiplicative.ofAdd (X i))
    intro a ha
    have he := hX (baseActor 1 a) (baseActor_mem 1 a (Subgroup.one_mem _) ha)
    rw [tensorHom_base,action_baseEmbedding,map_one] at he
    apply Multiplicative.toAdd.injective
    rw [MarkedAutomorphisms.NaturalFlag.slAut_apply]
    ext j
    have hi := congrArg (fun Y : Space => Y i j) he
    rw [baseAction_right] at hi
    exact hi
  have he : X = X 0 0 • point := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [point,coordinates_tmul,basisVector,hcol,hrow]
  rcases (by decide : ∀ c : ZMod 2, c = 0 ∨ c = 1) (X 0 0) with hz | ho
  · exact Or.inl (by simpa [hz] using he)
  · exact Or.inr (by simpa [ho] using he)

/-- The marked pure tensor is fixed by the original paired flag subgroup. -/
theorem sylow_fixes_point (a : Actor) (ha : a ∈ WreathPair.borel) :
    action (tensorHom a) point = point :=
  (fixes_point_iff a).mpr (WreathPair.borel_le_point ha)

end PointParabolic
end BinaryTensorThree
