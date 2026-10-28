module
public import Theory.Representation.BinaryFifteenPoint.SingerCoordinates

/-!
# Exact coordinates on every invariant fifteen-point quotient

The complementary coordinates retain all eight kernels from InvariantLattice.
Their projections have exactly those original-coordinate kernels and carry
the same literal Singer action, including the zero quotient.
-/
@[expose] public section
namespace BinaryFifteenPoint
open Matrix Thompson.BinaryMatrix

/-- Dimensions of the eight quotient rows, in the frozen kernel order. -/
def quotientDimension : Fin 8 → ℕ := ![15,14,11,10,5,4,1,0]

/-- Every kernel and its displayed quotient have total dimension fifteen. -/
theorem quotientDimension_add_rowDimension : ∀ r : Fin 8,
    quotientDimension r+rowDimension r=15 := by decide +kernel

def quotientIndexData : Array (Array ℕ) := #[#[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14], #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14], #[0, 1, 2, 7, 8, 9, 10, 11, 12, 13, 14], #[1, 2, 7, 8, 9, 10, 11, 12, 13, 14], #[0, 7, 8, 9, 10], #[7, 8, 9, 10], #[0], #[]]

/-- The primary coordinates complementary to the exact invariant kernel. -/
def quotientIndex (r : Fin 8) (j : Fin (quotientDimension r)) : Fin 15 :=
  ⟨(quotientIndexData[r.val]!)[j.val]! % 15,Nat.mod_lt _ (by decide)⟩

private theorem quotientIndex_injective : ∀ r : Fin 8,
    Function.Injective (quotientIndex r) := by decide +kernel

private theorem quotientIndex_unselected : ∀ (r : Fin 8) (j : Fin (quotientDimension r)),
    (invariantMask r).val.testBit (coordinateBlock (quotientIndex r j)).val=false := by decide +kernel

private theorem quotientIndex_covers : ∀ (r : Fin 8) (i : Fin 15),
    (invariantMask r).val.testBit (coordinateBlock i).val=false →
      ∃ j : Fin (quotientDimension r), quotientIndex r j=i := by decide +kernel

/-- Projection from primary coordinates onto the complementary coordinates. -/
def quotientSelect (r : Fin 8) :
    (Fin 15 → ZMod 2) →ₗ[ZMod 2] (Fin (quotientDimension r) → ZMod 2) where
  toFun x j := x (quotientIndex r j)
  map_add' := by intros; rfl
  map_smul' := by intros; rfl

private theorem quotientSelect_surjective (r : Fin 8) : Function.Surjective (quotientSelect r) := by
  intro y
  refine ⟨fun i => ∑ j, if quotientIndex r j=i then y j else 0,?_⟩
  ext j
  change (∑ k : Fin (quotientDimension r),
    if quotientIndex r k=quotientIndex r j then y k else 0)=y j
  simp only [(quotientIndex_injective r).eq_iff,Finset.sum_ite_eq',Finset.mem_univ,ite_true]

private theorem quotientSelect_ker (r : Fin 8) :
    (quotientSelect r).ker=maskSubspace (invariantMask r) := by
  ext x
  constructor
  · intro hx i hi
    obtain ⟨j,rfl⟩ := quotientIndex_covers r i hi
    exact congrFun (LinearMap.mem_ker.mp hx) j
  · intro hx
    apply LinearMap.mem_ker.mpr
    funext j
    exact hx (quotientIndex r j) (quotientIndex_unselected r j)

/-- Projection from the original right-coset coordinates onto a quotient row. -/
def quotientProjection (r : Fin 8) :
    (Fin 15 → ZMod 2) →ₗ[ZMod 2] (Fin (quotientDimension r) → ZMod 2) :=
  (quotientSelect r).comp inverseChangeMatrix.vecMulLinear

/-- Every displayed quotient projection is onto, including the zero quotient. -/
theorem quotientProjection_surjective (r : Fin 8) : Function.Surjective (quotientProjection r) := by
  intro y
  obtain ⟨x,hx⟩ := quotientSelect_surjective r y
  refine ⟨x ᵥ* changeMatrix,?_⟩
  change quotientSelect r ((x ᵥ* changeMatrix) ᵥ* inverseChangeMatrix)=y
  rw [vecMul_vecMul,change_inverse.1,vecMul_one,hx]

/-- The original-coordinate projection has precisely the frozen invariant kernel. -/
theorem quotientProjection_ker (r : Fin 8) :
    (quotientProjection r).ker=invariantSubspace r := by
  ext x
  constructor
  · intro hx
    have hy : x ᵥ* inverseChangeMatrix ∈ maskSubspace (invariantMask r) := by
      rw [←quotientSelect_ker]
      simpa only [LinearMap.mem_ker,quotientProjection,LinearMap.comp_apply,
        Matrix.vecMulLinear_apply] using hx
    change x ∈ (maskSubspace (invariantMask r)).map changeMatrix.vecMulLinear
    refine ⟨x ᵥ* inverseChangeMatrix,hy,?_⟩
    change (x ᵥ* inverseChangeMatrix) ᵥ* changeMatrix=x
    rw [vecMul_vecMul,change_inverse.2,vecMul_one]
  · rintro ⟨y,hy,rfl⟩
    change quotientSelect r ((y ᵥ* changeMatrix) ᵥ* inverseChangeMatrix)=0
    rw [vecMul_vecMul,change_inverse.1,vecMul_one]
    exact LinearMap.mem_ker.mp ((quotientSelect_ker r).symm ▸ hy)

def singerQuotientRows : Array (Array ℕ) := #[#[1, 10338, 24624, 40, 104, 112, 16, 3470, 7288, 17978, 7832, 20532, 74, 22630, 12384], #[5169, 12312, 20, 52, 56, 8, 1735, 3644, 8989, 3916, 10266, 37, 11315, 6192], #[1, 642, 1536, 222, 448, 1122, 488, 1284, 2, 1414, 768], #[321, 768, 111, 224, 561, 244, 642, 1, 707, 384], #[1, 22, 16, 24, 26], #[11, 8, 12, 13], #[1], #[]]

/-- Literal Singer matrices on all eight quotient rows. -/
def singerQuotientMatrix (r : Fin 8) :
    Matrix (Fin (quotientDimension r)) (Fin (quotientDimension r)) (ZMod 2) :=
  decode (quotientDimension r) singerQuotientRows[r.val]!

private theorem select_singer_intertwine (r : Fin 8) :
    (quotientSelect r).comp singerAdapted.vecMulLinear=
      (singerQuotientMatrix r).vecMulLinear.comp (quotientSelect r) := by
  apply (Pi.basisFun (ZMod 2) (Fin 15)).ext
  intro i
  simp only [Pi.basisFun_apply]
  exact (by decide +kernel : ∀ (r : Fin 8) (i : Fin 15),
    (quotientSelect r).comp singerAdapted.vecMulLinear (Pi.single i 1)=
      (singerQuotientMatrix r).vecMulLinear.comp (quotientSelect r) (Pi.single i 1)) r i

private theorem inverse_singer_intertwine :
    singerMatrix*inverseChangeMatrix=inverseChangeMatrix*singerAdapted := by
  calc
    singerMatrix*inverseChangeMatrix =
        (inverseChangeMatrix*changeMatrix)*singerMatrix*inverseChangeMatrix := by
      rw [change_inverse.2,Matrix.one_mul]
    _ = inverseChangeMatrix*(changeMatrix*singerMatrix)*inverseChangeMatrix := by
      rw [Matrix.mul_assoc inverseChangeMatrix changeMatrix singerMatrix]
    _ = inverseChangeMatrix*(singerAdapted*changeMatrix)*inverseChangeMatrix := by
      rw [singer_intertwine]
    _ = inverseChangeMatrix*singerAdapted*(changeMatrix*inverseChangeMatrix) := by
      simp only [Matrix.mul_assoc]
    _ = inverseChangeMatrix*singerAdapted := by rw [change_inverse.1,Matrix.mul_one]

/-- The quotient projection retains the same marked right Singer action. -/
theorem quotientProjection_singer_intertwine (r : Fin 8) (x : Fin 15 → ZMod 2) :
    quotientProjection r (x ᵥ* singerMatrix)=
      quotientProjection r x ᵥ* singerQuotientMatrix r := by
  change quotientSelect r ((x ᵥ* singerMatrix) ᵥ* inverseChangeMatrix)=
    quotientSelect r (x ᵥ* inverseChangeMatrix) ᵥ* singerQuotientMatrix r
  rw [vecMul_vecMul,inverse_singer_intertwine,←vecMul_vecMul]
  simpa only [LinearMap.comp_apply,Matrix.vecMulLinear_apply] using
    LinearMap.congr_fun (select_singer_intertwine r) (x ᵥ* inverseChangeMatrix)

/-- No invariant row is discarded by the Singer transition. -/
theorem invariantSubspace_singer_stable (r : Fin 8) (x : Fin 15 → ZMod 2)
    (hx : x ∈ invariantSubspace r) : x ᵥ* singerMatrix ∈ invariantSubspace r := by
  rw [←quotientProjection_ker] at hx ⊢
  apply LinearMap.mem_ker.mpr
  rw [quotientProjection_singer_intertwine,LinearMap.mem_ker.mp hx,zero_vecMul]

end BinaryFifteenPoint
