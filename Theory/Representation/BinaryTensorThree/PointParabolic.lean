module
public import Theory.Representation.BinaryTensorThree.SylowMarking
public import Theory.Representation.BinaryTensorThree.ParabolicRadicals
public import Theory.SpecificGroups.PSL3Two.Parabolics.WreathPair
public import Theory.SpecificGroups.PSL3Two.Parabolics.MarkedProduct
public import Theory.SpecificGroups.PSL3Two.Parabolics.Cores.ModelAction
public import Theory.SpecificGroups.PSL3Two.Parabolics.Actions

/-!
# The point parabolic of the binary tensor action

The stabilizer of the marked pure tensor is the paired point parabolic.
Its quotient by the two coordinate cores is S₃ wr C₂, whose two-core is
trivial. Hence its two-core acts through the two literal translation radicals.
The radical embedding is injective, so an action with image in these radicals
has a canonical lift to their product, allowing the original action kernel.

The source adapter applies this to the actual S = O₂(XT), retaining the
original point and tensor coordinates. No ambient centralizer classification
or point-core containment follows from this model calculation alone.
Source: Aschbacher--Smith H.4.4 and 8.3, printed pp.383--385,724--727.
-/

public noncomputable section
open Subgroup
open scoped TensorProduct
namespace BinaryTensorThree.PointParabolic
open Matrix.PSL3Two
abbrev Actor := WreathPair.Actor
private abbrev Bit := WreathPair.Bit
private abbrev P := pointParabolicSL
abbrev PairP := WreathPair.point
private abbrev Q := P ⧸ pCore 2 P
private abbrev WQ := RegularWreathProduct Q Bit

private def pairQuotient : PairP →* WQ where
  toFun x := ⟨fun i => QuotientGroup.mk' _ ⟨x.val.left i,x.property i⟩,x.val.right⟩
  map_one' := by
    apply RegularWreathProduct.ext
    · funext i
      exact (QuotientGroup.mk' (pCore 2 P)).map_one
    · rfl
  map_mul' x y := by
    apply RegularWreathProduct.ext
    · funext i
      exact (QuotientGroup.mk' (pCore 2 P)).map_mul
        ⟨x.val.left i,x.property i⟩
        ⟨y.val.left (x.val.right⁻¹*i),y.property (x.val.right⁻¹*i)⟩
    · rfl

private theorem pairQuotient_surjective : Function.Surjective pairQuotient := by
  intro x
  choose a ha using fun i => QuotientGroup.mk'_surjective (pCore 2 P) (x.left i)
  refine ⟨⟨⟨fun i => (a i).val,x.right⟩,fun i => (a i).property⟩,?_⟩
  exact RegularWreathProduct.ext (funext ha) rfl

private theorem quotient_twoCore : pCore 2 WQ = ⊥ := by
  let eQ := (ParabolicCoreModel.coreQuotientEquiv MarkedAutomorphisms.pointEquivSymmetric).trans
    (Classical.choice SLTwoPermThree.sl2Two_equiv_perm_three).symm
  let e := RegularWreathProduct.congr eQ (MulEquiv.refl Bit)
  apply (map_injective (f := e.toMonoidHom) e.injective)
  rw [pCore_map_iso,Theory.GroupTheory.WreathTwoResidual.twoCore_eq_bot,Subgroup.map_bot]

private theorem core_coordinates {w : Actor} (hw : w ∈ PairP.pCoreIn 2) :
    w.right = 1 ∧ ∀ i, w.left i ∈ MarkedAutomorphisms.pointV := by
  obtain ⟨x,hx,rfl⟩ := hw
  have hm : ((pCore 2 PairP).map pairQuotient).Normal :=
    (inferInstance : (pCore 2 PairP).Normal).map _ pairQuotient_surjective
  have hl : (pCore 2 PairP).map pairQuotient ≤ pCore 2 WQ :=
    le_sSup ⟨hm,pCore_isPGroup.map pairQuotient⟩
  have he := hl (mem_map_of_mem pairQuotient hx)
  rw [quotient_twoCore,mem_bot] at he
  refine ⟨congrArg RegularWreathProduct.right he,fun i => ?_⟩
  have hi : QuotientGroup.mk' (pCore 2 P) ⟨x.val.left i,x.property i⟩ = 1 :=
    congrArg (fun a : WQ => a.left i) he
  have hc := (QuotientGroup.eq_one_iff _).mp hi
  rw [← MarkedProduct.pointParabolic_core]
  exact ⟨⟨x.val.left i,x.property i⟩,hc,rfl⟩

private def linearWreath : Actor →* Wreath where
  toFun w := ⟨fun i => Matrix.SpecialLinearGroup.toLin' (w.left i),w.right⟩
  map_one' := by ext <;> simp
  map_mul' a b := by ext <;> simp

def tensorHom : Actor →* BinaryTensorThree.Group := wreathHom.comp linearWreath

/-- The matrix wreath action uses the literal natural linear maps on both factors. -/
theorem tensorHom_eq_wreathHom (w : Actor) :
    tensorHom w = wreathHom
      ⟨fun i => Matrix.SpecialLinearGroup.toLin' (w.left i),w.right⟩ := by rfl

private theorem linear_radical {g : SL} (hg : g ∈ MarkedAutomorphisms.pointV) :
    Matrix.SpecialLinearGroup.toLin' g = radical (Multiplicative.ofAdd ![g.val 0 1,g.val 0 2]) := by
  obtain ⟨h00,h10,h20,h11,h12,h21,h22⟩ := hg
  ext x i
  change g.val.mulVec x i = radicalEquiv ![g.val 0 1,g.val 0 2] x i
  fin_cases i <;>
    simp [Matrix.mulVec,dotProduct,Fin.sum_univ_three,radicalEquiv,
      h00,h10,h20,h11,h12,h21,h22]

theorem core_tensor_mem_radical {w : Actor} (hw : w ∈ PairP.pCoreIn 2) :
    tensorHom w ∈ radicalPair.range := by
  obtain ⟨hr,hl⟩ := core_coordinates hw
  refine ⟨(Multiplicative.ofAdd ![(w.left 1).val 0 1,(w.left 1).val 0 2],
    Multiplicative.ofAdd ![(w.left BinaryPermutation.FiveTensorSquare.swapIndex).val 0 1,
      (w.left BinaryPermutation.FiveTensorSquare.swapIndex).val 0 2]),?_⟩
  change baseEmbedding _ = wreathMap (linearWreath w)
  change baseEmbedding _ = if w.right = 1 then
    baseEmbedding (Matrix.SpecialLinearGroup.toLin' (w.left 1),
      Matrix.SpecialLinearGroup.toLin' (w.left BinaryPermutation.FiveTensorSquare.swapIndex))
    else _
  rw [if_pos hr]
  rw [linear_radical (hl 1),linear_radical (hl _)]
  rfl

private theorem tensorHom_point (w : Actor) :
    action (tensorHom w) point =
      coordinates (Matrix.SpecialLinearGroup.toLin' (w.left 1) (basisVector 0) ⊗ₜ[ZMod 2]
        Matrix.SpecialLinearGroup.toLin'
          (w.left BinaryPermutation.FiveTensorSquare.swapIndex) (basisVector 0)) := by
  have hf : flip point = point := by
    ext i j
    simp only [flip_apply,point,coordinates_tmul,mul_comm]
  change action (wreathMap (linearWreath w)) point = _
  unfold wreathMap
  split
  · exact baseAction_tmul _ _ _
  · rw [map_mul,Module.End.mul_apply,action_swap,hf,action_baseEmbedding]
    exact baseAction_tmul _ _ _

private theorem point_column (g : SL) :
    Matrix.SpecialLinearGroup.toLin' g (basisVector 0) = basisVector 0 ↔ g ∈ P := by
  change _ ↔ g ∈ pointParabolicSL
  rw [← Fano.stabilizer_flagPoint_SL]
  change _ ↔ g • flagPoint = flagPoint
  rw [Subtype.ext_iff]
  change g.val.mulVec (basisVector 0) = basisVector 0 ↔
    g.val.mulVec ![1,0,0] = ![1,0,0]
  have h0 : basisVector 0 = ![1,0,0] := by
    ext i
    fin_cases i <;> simp [basisVector]
  rw [h0]

private theorem pure_point_iff (x y : Natural) :
    coordinates (x ⊗ₜ[ZMod 2] y) = point ↔ x = basisVector 0 ∧ y = basisVector 0 := by
  constructor
  · intro h
    have h00 : x 0 * y 0 = 1 := by
      have he := congrArg (fun X : Space => X 0 0) h
      simpa [point,coordinates_tmul,basisVector] using he
    have hone : ∀ a b : ZMod 2, a*b=1 → a=1 ∧ b=1 := by decide
    obtain ⟨hx,hy⟩ := hone _ _ h00
    constructor
    · ext i
      have he := congrArg (fun X : Space => X i 0) h
      simpa [point,coordinates_tmul,basisVector,hy] using he
    · ext j
      have he := congrArg (fun X : Space => X 0 j) h
      simpa [point,coordinates_tmul,basisVector,hx] using he
  · rintro ⟨rfl,rfl⟩
    rfl

theorem fixes_point_iff (w : Actor) : action (tensorHom w) point = point ↔ w ∈ PairP := by
  rw [tensorHom_point,pure_point_iff,point_column,point_column]
  constructor
  · rintro ⟨h1,h2⟩ i
    rcases BinaryPermutation.FiveTensorSquare.index_cases i with rfl|rfl
    · exact h1
    · exact h2
  · intro h
    exact ⟨h 1,h _⟩

end BinaryTensorThree.PointParabolic

namespace BinaryTensorThree

theorem radicalPair_injective : Function.Injective radicalPair := by
  intro a b hab
  have hleft (j : Fin 2) : a.1.toAdd j = b.1.toAdd j := by
    have h := congrArg (fun g : Group => action g (leftProbe j) 0 0) hab
    rw [radicalPair_leftProbe,radicalPair_leftProbe] at h
    change leftProbe j 0 0 + a.1.toAdd j * point 0 0 =
      leftProbe j 0 0 + b.1.toAdd j * point 0 0 at h
    have hp : point 0 0 = 1 := by simp [point,coordinates_tmul,basisVector]
    simpa only [hp,mul_one,add_left_cancel_iff] using h
  have hright (j : Fin 2) : a.2.toAdd j = b.2.toAdd j := by
    have h := congrArg (fun g : Group => action g (rightProbe j) 0 0) hab
    rw [radicalPair_rightProbe,radicalPair_rightProbe] at h
    change rightProbe j 0 0 + a.2.toAdd j * point 0 0 =
      rightProbe j 0 0 + b.2.toAdd j * point 0 0 at h
    have hp : point 0 0 = 1 := by simp [point,coordinates_tmul,basisVector]
    simpa only [hp,mul_one,add_left_cancel_iff] using h
  exact Prod.ext (congrArg Multiplicative.ofAdd (funext hleft))
    (congrArg Multiplicative.ofAdd (funext hright))

end BinaryTensorThree

