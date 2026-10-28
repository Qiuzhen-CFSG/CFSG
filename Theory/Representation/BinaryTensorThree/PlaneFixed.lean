module
public import Theory.Representation.BinaryTensorThree.WreathCoordinates
public import Theory.GroupTheory.CoprimeQuotientSubgroups
public import Theory.ElementaryAbelian.Quotient

/-!
# The four-space fixed by the paired plane radicals

The two plane radicals in the binary tensor wreath action fix precisely the
upper two-by-two block. The plane parabolic wreath subgroup preserves this
space. Its two cubic Levi factors form an elementary nine and act faithfully
on the block. All groups and actions retain the original matrix coordinates;
the radical here is distinct from the point radical used in the weak-closure
argument. The transport companion applies these facts to an original ambient
module with a two-group action kernel.

Source: Aschbacher--Smith, H.4.4 and clauses (a)--(c) in the proof of 8.3.8,
printed pp.383--385,725 (refs/quasithin.pdf).
-/

@[expose] public noncomputable section
open Subgroup
open scoped TensorProduct
namespace BinaryTensorThree.PlaneFixed
open Matrix.PSL3Two

abbrev Two := Multiplicative (Fin 2 → ZMod 2)
abbrev Three := Multiplicative (ZMod 3)
abbrev Actor := PointParabolic.Actor

def square : Submodule (ZMod 2) Space where
  carrier := {X | (∀ j, X 2 j = 0) ∧ (∀ i, X i 2 = 0)}
  zero_mem' := by simp
  add_mem' := by rintro X Y ⟨hX,hX'⟩ ⟨hY,hY'⟩; exact ⟨by simp_all,by simp_all⟩
  smul_mem' := by rintro c X ⟨hX,hX'⟩; exact ⟨by simp_all,by simp_all⟩

def radicalMatrix (a : Two) : SL := ⟨!![1,0,a.toAdd 0;0,1,a.toAdd 1;0,0,1], by
  simp [Matrix.det_fin_three]⟩

def radical : Two →* SL where
  toFun := radicalMatrix
  map_one' := by decide +kernel
  map_mul' := by decide +kernel

def cubicMatrix : SL := ⟨!![0,1,0;1,1,0;0,0,1],by decide +kernel⟩

def cubic : Three →* SL where
  toFun a := cubicMatrix ^ a.toAdd.val
  map_one' := by decide +kernel
  map_mul' := by decide +kernel

def pair : SL × SL →* Actor where
  toFun a := ⟨fun i => if i = 1 then a.1 else a.2,1⟩
  map_one' := by ext i <;> simp
  map_mul' a b := by
    apply RegularWreathProduct.ext
    · funext i
      change (if i = 1 then a.1*b.1 else a.2*b.2) =
        (if i = 1 then a.1 else a.2) * (if (1 : WreathPair.Bit)⁻¹*i = 1 then b.1 else b.2)
      simp only [inv_one,one_mul]
      split <;> rfl
    · rfl

def radicalPair : Two × Two →* Actor := pair.comp (radical.prodMap radical)
def cubicPair : Three × Three →* Actor := pair.comp (cubic.prodMap cubic)

theorem tensor_pair (a b : SL) :
    PointParabolic.tensorHom (pair (a,b)) =
      baseEmbedding (Matrix.SpecialLinearGroup.toLin' a,Matrix.SpecialLinearGroup.toLin' b) := by
  rw [PointParabolic.tensorHom_eq_wreathHom]
  simp [wreathHom,wreathMap,pair]

private theorem matrix_action (a b : SL) (X : Space) :
    baseAction (Matrix.SpecialLinearGroup.toLin' a,Matrix.SpecialLinearGroup.toLin' b) X =
      a.val * X * b.val.transpose := by
  obtain ⟨x,rfl⟩ := coordinates.surjective X
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul x y =>
    rw [baseAction_tmul]
    ext i j
    change (a.val.mulVec x) i * (b.val.mulVec y) j = _
    simp only [Matrix.mul_apply,Matrix.transpose_apply,coordinates_tmul,
      Matrix.mulVec,dotProduct,Finset.mul_sum,Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro k hk
    apply Finset.sum_congr rfl
    intro l hl
    ring
  | add x y hx hy => simp [map_add,Matrix.mul_add,Matrix.add_mul,hx,hy]

/-- Matrix formula for the literal paired plane-radical action. -/
theorem radical_action (a b : Two) (X : Space) :
    action (PointParabolic.tensorHom (radicalPair (a,b))) X =
      (radical a).val * X * (radical b).val.transpose := by
  rw [show radicalPair (a,b) = pair (radical a,radical b) from rfl,
    tensor_pair,action_baseEmbedding]
  exact matrix_action _ _ _

theorem radical_fixed_iff (X : Space) :
    (∀ a, action (PointParabolic.tensorHom (radicalPair a)) X = X) ↔ X ∈ square := by
  have hf (a b : Two) : action (PointParabolic.tensorHom (radicalPair (a,b))) X =
      (radical a).val * X * (radical b).val.transpose := by
    rw [show radicalPair (a,b) = pair (radical a,radical b) from rfl,tensor_pair,action_baseEmbedding]
    exact matrix_action _ _ _
  constructor
  · intro h
    constructor
    · intro j
      have he := congrArg (fun Y : Space => Y 0 j) (h (Multiplicative.ofAdd ![1,0],1))
      rw [hf] at he
      fin_cases j <;>
        simpa [radical,radicalMatrix,Matrix.mul_apply,Matrix.vecMul,dotProduct,
          Fin.sum_univ_three,Matrix.transpose_apply] using he
    · intro i
      have he := congrArg (fun Y : Space => Y i 0) (h (1,Multiplicative.ofAdd ![1,0]))
      rw [hf] at he
      fin_cases i <;>
        simpa [radical,radicalMatrix,Matrix.mul_apply,Matrix.vecMul,dotProduct,
          Fin.sum_univ_three,Matrix.transpose_apply] using he
  · rintro ⟨hr,hc⟩ ⟨a,b⟩
    rw [hf]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [radical,radicalMatrix,Matrix.mul_apply,Matrix.vecMul,dotProduct,Fin.sum_univ_three,Matrix.transpose_apply,hr,hc]

theorem point_mem_square : point ∈ square := by
  constructor <;> intro i <;> simp [point,coordinates_tmul,basisVector]

private theorem base_preserves_square (a b : SL)
    (ha : a ∈ lineParabolicSL) (hb : b ∈ lineParabolicSL)
    (X : Space) (hX : X ∈ square) :
    baseAction (Matrix.SpecialLinearGroup.toLin' a,Matrix.SpecialLinearGroup.toLin' b) X ∈ square := by
  obtain ⟨ha0,ha1⟩ := (mem_lineParabolicSL_iff a).mp ha
  obtain ⟨hb0,hb1⟩ := (mem_lineParabolicSL_iff b).mp hb
  obtain ⟨hr,hc⟩ := hX
  rw [matrix_action]
  constructor <;> intro i <;>
    simp [Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_three,ha0,ha1,hb0,hb1,hr,hc]

theorem line_preserves_square (a : Actor) (ha : a ∈ WreathPair.line)
    (X : Space) (hX : X ∈ square) :
    action (PointParabolic.tensorHom a) X ∈ square := by
  rw [PointParabolic.tensorHom_eq_wreathHom]
  change action (wreathMap _) X ∈ square
  unfold wreathMap
  split
  · exact base_preserves_square _ _ (ha 1) (ha _) X hX
  · rw [map_mul,Module.End.mul_apply,action_swap,action_baseEmbedding]
    exact base_preserves_square _ _ (ha 1) (ha _) (flip X) ⟨hX.2,hX.1⟩

private def unit (i j : Fin 2) : Space :=
  fun k l => if k = i.castSucc ∧ l = j.castSucc then 1 else 0

private theorem unit_mem (i j : Fin 2) : unit i j ∈ square := by
  constructor <;> intro k <;> fin_cases i <;> fin_cases j <;> simp [unit]

private theorem cubic_test : ∀ a b : Three,
    (∀ i j : Fin 2, (cubic a).val * unit i j * (cubic b).val.transpose = unit i j) →
    a = 1 ∧ b = 1 := by decide +kernel

/-- The two cubic Levi factors act faithfully on the actual radical fixed space. -/
theorem cubic_faithful (a : Three × Three)
    (ha : ∀ X ∈ square, action (PointParabolic.tensorHom (cubicPair a)) X = X) : a = 1 := by
  have hh := cubic_test a.1 a.2 (fun i j => by
    have h := ha (unit i j) (unit_mem i j)
    rw [show cubicPair a = pair (cubic a.1,cubic a.2) from rfl,
      tensor_pair,action_baseEmbedding,matrix_action] at h
    exact h)
  exact Prod.ext hh.1 hh.2

theorem cubicPair_injective : Function.Injective cubicPair := by
  apply (injective_iff_map_eq_one cubicPair).mpr
  intro a ha
  apply cubic_faithful a
  intro X _
  rw [ha,map_one,map_one]
  rfl

theorem cubic_mem_line (a : Three × Three) : cubicPair a ∈ WreathPair.line := by
  have hc : ∀ b : Three, cubic b ∈ lineParabolicSL := by decide +kernel
  intro i
  change (if i = 1 then cubic a.1 else cubic a.2) ∈ lineParabolicSL
  split <;> exact hc _

theorem radical_mem_borel (a : Two × Two) : radicalPair a ∈ WreathPair.borel := by
  have hc : ∀ b : Two, radical b ∈ borelSL := by decide +kernel
  intro i
  change (if i = 1 then radical a.1 else radical a.2) ∈ borelSL
  split <;> exact hc _

instance : IsElementaryAbelian 3 (Three × Three) where
  toIsMulCommutative := inferInstance
  exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr (by decide +kernel)

instance : IsElementaryAbelian 3 cubicPair.range :=
  IsElementaryAbelian.of_surjective cubicPair.rangeRestrict cubicPair.rangeRestrict_surjective

theorem card_cubic_range : Nat.card cubicPair.range = 9 := by
  rw [Nat.card_congr (MonoidHom.ofInjective cubicPair_injective).toEquiv.symm,
    Nat.card_prod]
  simp [Nat.card_eq_fintype_card,Three]

end BinaryTensorThree.PlaneFixed
