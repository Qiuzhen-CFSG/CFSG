module

public import Theory.SpecificGroups.G2.MultiplierOrdinary.OddCyclotomicSylow.TwistedCubicTorus.UnitaryModel
public import Theory.SpecificGroups.G2.PRegularClasses.RationalFusion.CentralizerLang.ConnectedNoFixedWeight.BlockRealization.Algebra

/-!
# The faithful special unitary action on a quadratic octonion algebra

For the genuine quadratic conjugation σ, the coordinates `(a,u)` embed as
`pack a (σ a) u (σ ∘ u)` in split octonions over the quadratic field.
The multiplication below is exactly the restriction of the published table.
The determinant-one unitary identity identifies the cofactor matrix with
coefficient conjugation, so the Peirce block action restricts to `(a,u) ↦ (a,Au)`.
This gives a faithful multiplication-preserving F-linear action of the full
SU₃, including its center. Identification with split octonions over F is a
separate obligation; it is not asserted by the action construction.

Source application: Aschbacher–Smith I.1.2–I.1.4, printed pp.407–408,
and GLS III §6.1. The octonion multiplication and block realization use the
licensed ATLAS port; see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/

@[expose] public section

open Matrix Atlas.SplitOctonion
open scoped MatrixGroups
namespace Atlas.G2.MultiplierOrdinary.OddCyclotomicSylow.TwistedCubicTorus.UnitaryEmbedding
open Atlas.G2.PRegularClasses.RationalFusion.CentralizerLang.NoFixedWeight.BlockRealization
noncomputable section
variable (F : Type*) [Field F] [Finite F] (p : ℕ) [Fact p.Prime] [CharP F p]

@[simp] theorem conj_conj (x : Quadratic F p) :
    quadraticConj F p (quadraticConj F p x) = x := quadraticConj_involutive F p x

abbrev Octonion := Quadratic F p × (Fin 3 → Quadratic F p)

def embed (x : Octonion F p) : Carrier (Quadratic F p) :=
  pack x.1 (quadraticConj F p x.1) x.2 (fun i => quadraticConj F p (x.2 i))

theorem embed_injective : Function.Injective (embed F p) := by
  intro x y h
  apply Prod.ext
  · exact congrFun h 3
  · funext i
    fin_cases i
    · exact congrFun h 0
    · exact congrFun h 5
    · exact congrFun h 6

def octonionMul (x y : Octonion F p) : Octonion F p :=
  (x.1 * y.1 - x.2 ⬝ᵥ (fun i => quadraticConj F p (y.2 i)),
    x.1 • y.2 + quadraticConj F p y.1 • x.2 +
      crossProduct (fun i => quadraticConj F p (x.2 i))
        (fun i => quadraticConj F p (y.2 i)))

theorem embed_mul (x y : Octonion F p) :
    embed F p (octonionMul F p x y) = mul (embed F p x) (embed F p y) := by
  simp only [embed]
  rw [pack_mul]
  ext i
  fin_cases i <;>
    simp [octonionMul, pack, cross_apply, dotProduct, Fin.sum_univ_three,
      Matrix.vecHead, Matrix.vecTail]

def toSL : (standardForm F p).specialSubgroup →* SL(3, Quadratic F p) where
  toFun A := ⟨A.val.val, by
    have h := ((standardForm F p).mem_specialSubgroup_iff A.val).mp A.property
    exact congrArg Units.val h.2⟩
  map_one' := Subtype.ext rfl
  map_mul' _ _ := Subtype.ext rfl

theorem cofactor_toSL (A : (standardForm F p).specialSubgroup) :
    cofactor (toSL F p A).val = (A.val.val).map (quadraticConj F p) := by
  have hu := (((standardForm F p).mem_specialSubgroup_iff A.val).mp A.property).1
  change (standardForm F p).conjTranspose A.val.val * 1 * A.val.val = 1 at hu
  rw [mul_one] at hu
  have hdet : A.val.val.det = 1 := (toSL F p A).property
  have hadj : (standardForm F p).conjTranspose A.val.val = A.val.val.adjugate := by
    calc
      _ = (standardForm F p).conjTranspose A.val.val *
          (A.val.val * A.val.val.adjugate) := by
        rw [Matrix.mul_adjugate, hdet, one_smul, mul_one]
      _ = A.val.val.adjugate := by rw [← mul_assoc, hu, one_mul]
  change A.val.val.adjugate.transpose = _
  rw [← hadj]
  rfl

theorem embed_action (A : (standardForm F p).specialSubgroup) (x : Octonion F p) :
    embed F p (x.1, A.val.val *ᵥ x.2) = blockLinear (toSL F p A).val (embed F p x) := by
  rw [embed, embed, blockLinear_pack, cofactor_toSL]
  congr 1
  ext i
  simp [Matrix.mulVec, dotProduct]

theorem action_preserves_mul (A : (standardForm F p).specialSubgroup) (x y : Octonion F p) :
    ((octonionMul F p x y).1, A.val.val *ᵥ (octonionMul F p x y).2) =
      octonionMul F p (x.1, A.val.val *ᵥ x.2) (y.1, A.val.val *ᵥ y.2) := by
  apply embed_injective F p
  rw [embed_action, embed_mul, block_preserves_mul, ← embed_action, ← embed_action,
    ← embed_mul]

def actionLinear (A : (standardForm F p).specialSubgroup) :
    Octonion F p →ₗ[F] Octonion F p where
  toFun x := (x.1, A.val.val *ᵥ x.2)
  map_add' x y := by
    apply Prod.ext
    · rfl
    · change A.val.val *ᵥ (x.2 + y.2) = _
      exact Matrix.mulVec_add _ _ _
  map_smul' r x := by
    apply Prod.ext
    · rfl
    · change A.val.val *ᵥ (r • x.2) = r • (A.val.val *ᵥ x.2)
      exact Matrix.mulVec_smul _ _ _

theorem actionLinear_one (x : Octonion F p) : actionLinear F p 1 x = x := by
  change (x.1, (1 : Matrix (Fin 3) (Fin 3) (Quadratic F p)) *ᵥ x.2) = x
  simp

theorem actionLinear_mul (A B : (standardForm F p).specialSubgroup) (x : Octonion F p) :
    actionLinear F p (A * B) x = actionLinear F p A (actionLinear F p B x) := by
  apply Prod.ext
  · rfl
  · change (A.val.val * B.val.val) *ᵥ x.2 = A.val.val *ᵥ (B.val.val *ᵥ x.2)
    exact (Matrix.mulVec_mulVec _ _ _).symm

def actionEquiv (A : (standardForm F p).specialSubgroup) :
    Octonion F p ≃ₗ[F] Octonion F p where
  toLinearMap := actionLinear F p A
  invFun := actionLinear F p A⁻¹
  left_inv x := by
    change actionLinear F p A⁻¹ (actionLinear F p A x) = x
    rw [← actionLinear_mul, inv_mul_cancel, actionLinear_one]
  right_inv x := by
    change actionLinear F p A (actionLinear F p A⁻¹ x) = x
    rw [← actionLinear_mul, mul_inv_cancel, actionLinear_one]

def actionHom : (standardForm F p).specialSubgroup →*
    Atlas.Algebra.multiplicativeLinearAut (R := F) (octonionMul F p) where
  toFun A := ⟨actionEquiv F p A, action_preserves_mul F p A⟩
  map_one' := by
    apply Subtype.ext
    apply LinearEquiv.ext
    exact actionLinear_one F p
  map_mul' A B := by
    apply Subtype.ext
    apply LinearEquiv.ext
    exact actionLinear_mul F p A B

theorem actionHom_injective : Function.Injective (actionHom F p) := by
  intro A B h
  apply Subtype.ext
  apply Units.ext
  apply Matrix.mulVec_injective
  funext u
  exact congrArg (fun g => (g.val (0, u)).2) h


end
end Atlas.G2.MultiplierOrdinary.OddCyclotomicSylow.TwistedCubicTorus.UnitaryEmbedding
