module
public import Theory.Representation.BinaryTensorThree.Group
public import Theory.Representation.BinaryPermutation.FiveTensorSquare.SylowAction

/-!
# A concrete Sylow action on the binary three-by-three tensor

The dihedral group of order eight acts on the three independent coordinates
of the binary augmentation module on four points. Its wreath square acts
on the literal tensor matrices by the two factors and their interchange.
The computable coordinate formulas agree with `BinaryTensorThree.action`.
This model is used to exclude FF-offenders in the quiet tensor branch.

Source: Aschbacher--Smith H.4.4, H.4.8 and H.4.10, printed pp.383--384.
-/

@[expose] public section
open scoped TensorProduct
namespace BinaryTensorThree.Small
open BinaryPermutation.FiveTensorSquare
abbrev P := BinaryPermutation.FiveTensorSquare.Small.P
abbrev D8 := BinaryPermutation.FiveTensorSquare.Small.D8

/-- The three independent coordinates of the binary augmentation module on four points. -/
def extend (x : Natural) (i : ZMod 4) : ZMod 2 :=
  if hi : i.val < 3 then x ⟨i.val,hi⟩ else x 0+x 1+x 2

def natural (g : D8) (x : Natural) (i : Fin 3) : ZMod 2 :=
  extend x (BinaryPermutation.FiveTensorSquare.Small.dihedralPoint g⁻¹ i.val)

theorem natural_one : ∀ x, natural 1 x=x := by decide +kernel
theorem natural_mul : ∀ g h x, natural (g*h) x=natural g (natural h x) := by decide +kernel

def naturalLinear (g : D8) : Natural →ₗ[ZMod 2] Natural where
  toFun := natural g
  map_add' := (by decide +kernel : ∀ g x y,natural g (x+y)=natural g x+natural g y) g
  map_smul' := (by decide +kernel : ∀ g c x,natural g (c • x)=c • natural g x) g

def naturalEquiv (g : D8) : Factor where
  __ := naturalLinear g
  invFun := natural g⁻¹
  left_inv x := by
    change natural g⁻¹ (natural g x)=x
    rw [←natural_mul,inv_mul_cancel,natural_one]
  right_inv x := by
    change natural g (natural g⁻¹ x)=x
    rw [←natural_mul,mul_inv_cancel,natural_one]

@[simp] theorem naturalEquiv_one : naturalEquiv 1 = 1 := by
  apply LinearEquiv.ext
  intro x
  exact natural_one x
@[simp] theorem naturalEquiv_mul (g h : D8) : naturalEquiv (g*h) = naturalEquiv g * naturalEquiv h := by
  apply LinearEquiv.ext
  intro x
  exact natural_mul g h x

/-- The row and column actions in tensor coordinates. -/
def base (a b : D8) (X : Space) : Space :=
  fun i j => natural a (fun k => natural b (X k) j) i

def baseLinear (a b : D8) : Space →ₗ[ZMod 2] Space where
  toFun := base a b
  map_add' X Y := by
    ext i j
    change naturalLinear a (fun k => naturalLinear b (X k+Y k) j) i = _
    simp only [map_add,Pi.add_apply]
    change naturalLinear a ((fun k => naturalLinear b (X k) j) +
      (fun k => naturalLinear b (Y k) j)) i = _
    rw [map_add]
    rfl
  map_smul' c X := by
    ext i j
    change naturalLinear a (fun k => naturalLinear b (c • X k) j) i = _
    simp only [map_smul,Pi.smul_apply]
    change naturalLinear a (c • (fun k => naturalLinear b (X k) j)) i = _
    rw [map_smul]
    rfl

theorem base_tmul (a b : D8) (x y : Natural) :
    base a b (coordinates (x ⊗ₜ[ZMod 2] y)) =
      coordinates (natural a x ⊗ₜ[ZMod 2] natural b y) := by
  ext i j
  simp only [base,coordinates_tmul]
  change naturalLinear a (fun k => naturalLinear b (x k • y) j) i = _
  simp only [map_smul,Pi.smul_apply,smul_eq_mul]
  rw [mul_comm (natural a x i)]
  simp only [mul_comm (x _)]
  change naturalLinear a (natural b y j • x) i = _
  simp only [map_smul,Pi.smul_apply,smul_eq_mul]
  rfl

theorem base_eq (a b : D8) (X : Space) :
    base a b X = baseAction (naturalEquiv a,naturalEquiv b) X := by
  obtain ⟨v,rfl⟩ := coordinates.surjective X
  induction v using TensorProduct.induction_on with
  | zero =>
    rw [map_zero,map_zero]
    exact (baseLinear a b).map_zero
  | tmul x y => rw [base_tmul,baseAction_tmul]; rfl
  | add x y hx hy =>
    change baseLinear a b (coordinates (x+y)) = _
    simp only [map_add]
    exact congrArg₂ (· + ·) hx hy

def act (g : P) (X : Space) : Space :=
  if g.right=1 then base (g.left 1) (g.left swapIndex) X
  else base (g.left 1) (g.left swapIndex) (flip X)

noncomputable def toTensor (g : P) : BinaryTensorThree.Group :=
  if g.right=1 then baseEmbedding (naturalEquiv (g.left 1),naturalEquiv (g.left swapIndex))
  else baseEmbedding (naturalEquiv (g.left 1),naturalEquiv (g.left swapIndex)) * swap

theorem act_eq (g : P) (X : Space) : act g X = action (toTensor g) X := by
  by_cases h : g.right=1 <;>
    simp [act,toTensor,h,base_eq,Module.End.mul_apply]

theorem baseAction_mul_apply (a b : Factor × Factor) (X : Space) :
    baseAction a (baseAction b X) = baseAction (a*b) X := by
  rw [map_mul]
  rfl

@[simp] theorem flip_flip (X : Space) : flip (flip X) = X := rfl

noncomputable def actionSmall : Representation (ZMod 2) P Space where
  toFun g := action (toTensor g)
  map_one' := by
    apply LinearMap.ext
    intro X
    rw [←act_eq]
    simp only [act,RegularWreathProduct.one_right,ite_true,RegularWreathProduct.one_left]
    rw [base_eq]
    simp only [Pi.one_apply,naturalEquiv_one]
    change baseAction 1 X = X
    rw [map_one]
    rfl
  map_mul' a b := by
    apply LinearMap.ext
    intro X
    change action (toTensor (a*b)) X = action (toTensor a) (action (toTensor b) X)
    simp only [←act_eq]
    rcases index_cases a.right with ha|ha <;> rcases index_cases b.right with hb|hb <;>
      simp [act,base_eq,RegularWreathProduct.mul_left,RegularWreathProduct.mul_right,
        ha,hb,flip_baseAction,baseAction_mul_apply]

end BinaryTensorThree.Small
