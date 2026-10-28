module

public import Theory.Representation.G2BinaryNondegeneratePlane.Basic

/-!
# The second rank-one factor on a nondegenerate G₂ plane

The conjugation action on a split quaternion algebra, together with its natural
action on the four remaining coordinates, gives a second genuine SL₂(2) subgroup
of the octonion automorphism group. The finite identities check only the eight
basis vectors and their products, then extend by linearity and bilinearity.

Source: Aschbacher–Smith, Lemma 13.3.12, printed p.889.
-/

@[expose] public noncomputable section
open Atlas.SplitOctonion Module Submodule Matrix
open scoped MatrixGroups
namespace Atlas.G2.Natural.BinaryNondegeneratePlane
open Atlas.G2.Restricted.NaturalCoordinates
/-- The second rank-one factor, acting on the quaternion subalgebra and its complement. -/
def secondLinear (M : Matrix (Fin 2) (Fin 2) K) : Carrier K →ₗ[K] Carrier K where
  toFun x := ![
    M 0 0*x 0+M 0 0*M 0 1*(x 3+x 4)+M 0 1*x 7,
    M 0 0*x 1+M 0 1*x 5,
    M 0 0*x 2+M 0 1*x 6,
    M 0 0*M 1 0*x 0+M 0 0*M 1 1*x 3+M 0 1*M 1 0*x 4+M 0 1*M 1 1*x 7,
    M 0 0*M 1 0*x 0+M 0 1*M 1 0*x 3+M 0 0*M 1 1*x 4+M 0 1*M 1 1*x 7,
    M 1 0*x 1+M 1 1*x 5,
    M 1 0*x 2+M 1 1*x 6,
    M 1 0*x 0+M 1 0*M 1 1*(x 3+x 4)+M 1 1*x 7]
  map_add' x y := by ext i;fin_cases i <;> simp <;> ring
  map_smul' r x := by ext i;fin_cases i <;> simp <;> ring
theorem secondLinear_mul_basis : ∀ (M N : SL(2,K)) (i : Fin 8),
    secondLinear (M*N).val (basisVector i)=
      secondLinear M.val (secondLinear N.val (basisVector i)) := by decide +kernel
theorem secondLinear_mul (M N : SL(2,K)) :
    secondLinear (M*N).val=(secondLinear M.val).comp (secondLinear N.val) := by
  apply (Pi.basisFun K (Fin 8)).ext
  intro i
  simpa only [Pi.basisFun_apply, basisVector, LinearMap.comp_apply] using secondLinear_mul_basis M N i
theorem secondLinear_one : secondLinear (1 : SL(2,K)).val=1 := by
  ext x i
  fin_cases i <;> simp [secondLinear]
def secondEquiv (M : SL(2,K)) : Carrier K ≃ₗ[K] Carrier K :=
  LinearEquiv.ofLinearMap (secondLinear M.val) (secondLinear M⁻¹.val)
    (by rw [←secondLinear_mul,mul_inv_cancel,secondLinear_one];rfl)
    (by rw [←secondLinear_mul,inv_mul_cancel,secondLinear_one];rfl)
theorem second_preserves_mul_basis : ∀ (M : SL(2,K)) (i j : Fin 8),
    secondLinear M.val (mul (basisVector i) (basisVector j))=
      mul (secondLinear M.val (basisVector i)) (secondLinear M.val (basisVector j)) := by
  decide +kernel
theorem second_preserves_mul (M : SL(2,K)) (x y : Carrier K) :
    secondEquiv M (mul x y)=mul (secondEquiv M x) (secondEquiv M y) :=
  Atlas.SplitOctonion.map_mul_of_basis (secondLinear M.val) (second_preserves_mul_basis M) x y

def secondHom : SL(2,K) →* Model K where
  toFun M := ⟨secondEquiv M,second_preserves_mul M⟩
  map_one' := by apply Subtype.ext;apply LinearEquiv.toLinearMap_injective;exact secondLinear_one
  map_mul' M N := by
    apply Subtype.ext
    apply LinearEquiv.toLinearMap_injective
    exact secondLinear_mul M N

theorem secondHom_action (M : SL(2,K)) (v : W) :
    rho (secondHom M) v=![M.val 0 0*v 0+M.val 0 1*v 5,
      M.val 0 0*v 1+M.val 0 1*v 3,M.val 0 0*v 2+M.val 0 1*v 4,
      M.val 1 0*v 1+M.val 1 1*v 3,M.val 1 0*v 2+M.val 1 1*v 4,
      M.val 1 0*v 0+M.val 1 1*v 5] := by
  ext i
  fin_cases i <;> simp [action_apply,secondHom,secondEquiv,secondLinear,
    Atlas.G2.Restricted.NaturalCoordinates.projection,representative,traceZeroAction_val]
end Atlas.G2.Natural.BinaryNondegeneratePlane
