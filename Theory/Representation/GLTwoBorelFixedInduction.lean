module

public import Theory.Representation.GLTwoBorel
public import Theory.Representation.Induction
public import Mathlib.RepresentationTheory.Irreducible
public import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring

/-!
# Principal-series maps from upper-unipotent fixed vectors

A finite-dimensional complex representation of finite-field GL₂ with a nonzero
upper-unipotent fixed vector receives a nonzero map from a one-dimensional
Borel induction. The inducing representation is trivial on the actual bundled
upper unipotents of `GLTwo.borelSubgroup`. The public interface retains the
irreducibility hypothesis used in the character-degree application, although
this construction itself does not require irreducibility.

The fixed space is Borel invariant by an explicit triangular-matrix identity.
The Borel operators commute on it: reversing two triangular factors introduces
only an upper unipotent. A finite commuting family over the complex numbers has
a common eigenvector, obtained by successively intersecting invariant nonzero
subspaces with eigenspaces. Its eigenvalues define the one-dimensional Borel
representation. Inverse Frobenius reciprocity extends the eigenline inclusion
to induction, and evaluation at the identity tensor proves nonvanishing.

The last construction uses the coinvariant formula of `Rep.indResHomEquiv`
directly, avoiding the bundled category's equal-universe restriction. There is
no restriction on the finite field's cardinality, including the two-element
field. This supplies the principal-series containment step of the ordinary
GL₂ character-degree argument cited in Brauer, Desarguesian planes II,
printed p. 128; it does not assume a constituent-degree classification.
-/

open scoped MatrixGroups

private theorem common_eigenvector
    {Index V : Type*} [Finite Index] [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] [Nontrivial V]
    (operators : Index → Module.End ℂ V)
    (hcomm : ∀ left right, Commute (operators left) (operators right)) :
    ∃ vector : V, vector ≠ 0 ∧ ∀ index, ∃ scalar : ℂ,
      operators index vector = scalar • vector := by
  classical
  let := Fintype.ofFinite Index
  have step (indices : Finset Index) :
      ∃ space : Submodule ℂ V, space ≠ ⊥ ∧
        (∀ index vector, vector ∈ space → operators index vector ∈ space) ∧
        ∀ index ∈ indices, ∃ scalar : ℂ,
          ∀ vector ∈ space, operators index vector = scalar • vector := by
    induction indices using Finset.induction_on with
    | empty => exact ⟨⊤, top_ne_bot, by simp, by simp⟩
    | @insert index indices hnot ih =>
      obtain ⟨space, hspace, hinv, hscalar⟩ := ih
      let : Nontrivial space := Submodule.nontrivial_iff_ne_bot.mpr hspace
      let restricted := (operators index).restrict (hinv index)
      obtain ⟨scalar, heigen⟩ := Module.End.exists_eigenvalue restricted
      obtain ⟨vector, hvector⟩ := heigen.exists_hasEigenvector
      refine ⟨space ⊓ (operators index).eigenspace scalar, ?_, ?_, ?_⟩
      · refine (Submodule.ne_bot_iff _).mpr ⟨(vector : V), ?_, ?_⟩
        · refine ⟨vector.property, Module.End.mem_eigenspace_iff.mpr ?_⟩
          exact congrArg Subtype.val hvector.apply_eq_smul
        · exact fun hzero => hvector.2 (Subtype.ext hzero)
      · intro other value hvalue
        refine ⟨hinv other value hvalue.1, Module.End.mem_eigenspace_iff.mpr ?_⟩
        have hscalarvalue := Module.End.mem_eigenspace_iff.mp hvalue.2
        calc
          operators index (operators other value) =
              operators other (operators index value) :=
            congrArg (fun operator : Module.End ℂ V => operator value) (hcomm index other)
          _ = scalar • operators other value := by rw [hscalarvalue, map_smul]
      · intro other hother
        rcases Finset.mem_insert.mp hother with rfl | hother
        · exact ⟨scalar, fun value hvalue => Module.End.mem_eigenspace_iff.mp hvalue.2⟩
        · obtain ⟨otherScalar, hotherScalar⟩ := hscalar other hother
          exact ⟨otherScalar, fun value hvalue => hotherScalar value hvalue.1⟩
  obtain ⟨space, hspace, _, hscalar⟩ := step Finset.univ
  obtain ⟨vector, hmem, hne⟩ := space.ne_bot_iff.mp hspace
  exact ⟨vector, hne, fun index =>
    (hscalar index (Finset.mem_univ index)).imp fun scalar hscalar => hscalar vector hmem⟩

private theorem borel_diagonal_ne_zero {F : Type*} [Field F]
    (matrix : GLTwo.borelSubgroup F) : matrix.val 0 0 ≠ 0 ∧ matrix.val 1 1 ≠ 0 := by
  have hdet := matrix.val.det_ne_zero
  have hlower : matrix.val 1 0 = 0 := matrix.property
  simpa [Matrix.det_fin_two, hlower] using hdet

private theorem unipotent_mul_borel {F : Type*} [Field F]
    (matrix : GLTwo.borelSubgroup F) (parameter : F) :
    Matrix.GeneralLinearGroup.upperRightHom parameter * matrix.val =
      matrix.val * Matrix.GeneralLinearGroup.upperRightHom
        (parameter * matrix.val 1 1 / matrix.val 0 0) := by
  have hlower : matrix.val 1 0 = 0 := matrix.property
  have hdiag := (borel_diagonal_ne_zero matrix).1
  apply Units.ext
  ext row column
  fin_cases row <;> fin_cases column <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.GeneralLinearGroup.upperRightHom, hlower]
  field_simp
  ring

private theorem borel_mul_swap {F : Type*} [Field F]
    (left right : GLTwo.borelSubgroup F) :
    ∃ parameter : F, left.val * right.val =
      right.val * left.val * Matrix.GeneralLinearGroup.upperRightHom parameter := by
  have hleft : left.val 1 0 = 0 := left.property
  have hright : right.val 1 0 = 0 := right.property
  have hleftdiag := (borel_diagonal_ne_zero left).1
  have hrightdiag := (borel_diagonal_ne_zero right).1
  refine ⟨(left.val 0 0 * right.val 0 1 + left.val 0 1 * right.val 1 1 -
    (right.val 0 0 * left.val 0 1 + right.val 0 1 * left.val 1 1)) /
    (right.val 0 0 * left.val 0 0), ?_⟩
  apply Units.ext
  ext row column
  fin_cases row <;> fin_cases column <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.GeneralLinearGroup.upperRightHom, hleft, hright]
  all_goals field_simp
  all_goals ring

private theorem borel_eigenvector {F : Type*} [Field F] [Finite F]
    (size : ℕ) (rho : Representation ℂ (GL (Fin 2) F) (Fin size → ℂ))
    (hfixed : ∃ vector, vector ≠ 0 ∧ ∀ parameter : F,
      rho (Matrix.GeneralLinearGroup.upperRightHom parameter) vector = vector) :
    ∃ vector : Fin size → ℂ, vector ≠ 0 ∧
      (∀ parameter : F,
        rho (Matrix.GeneralLinearGroup.upperRightHom parameter) vector = vector) ∧
      ∀ matrix : GLTwo.borelSubgroup F, ∃ scalar : ℂ,
        rho matrix.val vector = scalar • vector := by
  let fixed := Representation.invariants
    (rho.comp Matrix.GeneralLinearGroup.upperRightHom.toMonoidHom)
  have hmem (vector : Fin size → ℂ) : vector ∈ fixed ↔
      ∀ parameter : F,
        rho (Matrix.GeneralLinearGroup.upperRightHom parameter) vector = vector := Iff.rfl
  have hinv (matrix : GLTwo.borelSubgroup F) (vector : Fin size → ℂ)
      (hvector : vector ∈ fixed) : rho matrix.val vector ∈ fixed := by
    apply (hmem _).mpr
    intro parameter
    calc
      rho (Matrix.GeneralLinearGroup.upperRightHom parameter) (rho matrix.val vector) =
          rho (Matrix.GeneralLinearGroup.upperRightHom parameter * matrix.val) vector := by
        rw [map_mul, Module.End.mul_apply]
      _ = rho matrix.val (rho (Matrix.GeneralLinearGroup.upperRightHom
          (parameter * matrix.val 1 1 / matrix.val 0 0)) vector) := by
        rw [unipotent_mul_borel, map_mul, Module.End.mul_apply]
      _ = rho matrix.val vector := by rw [(hmem _).mp hvector]
  let operators (matrix : GLTwo.borelSubgroup F) := (rho matrix.val).restrict (hinv matrix)
  have hcomm (left right : GLTwo.borelSubgroup F) :
      Commute (operators left) (operators right) := by
    obtain ⟨parameter, hproduct⟩ := borel_mul_swap left right
    apply LinearMap.ext
    intro vector
    apply Subtype.ext
    change rho left.val (rho right.val vector.val) = rho right.val (rho left.val vector.val)
    calc
      rho left.val (rho right.val vector.val) = rho (left.val * right.val) vector.val := by
        rw [map_mul, Module.End.mul_apply]
      _ = rho right.val (rho left.val
          (rho (Matrix.GeneralLinearGroup.upperRightHom parameter) vector.val)) := by
        rw [hproduct, map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply]
      _ = rho right.val (rho left.val vector.val) := by rw [(hmem _).mp vector.property]
  obtain ⟨initial, hinitial, hfix⟩ := hfixed
  have hnonzero : fixed ≠ ⊥ :=
    fixed.ne_bot_iff.mpr ⟨initial, (hmem initial).mpr hfix, hinitial⟩
  let : Nontrivial fixed := Submodule.nontrivial_iff_ne_bot.mpr hnonzero
  obtain ⟨vector, hvector, hscalar⟩ := common_eigenvector operators hcomm
  refine ⟨vector.val, fun hzero => hvector (Subtype.ext hzero),
    (hmem _).mp vector.property, ?_⟩
  intro matrix
  obtain ⟨scalar, hscalar⟩ := hscalar matrix
  exact ⟨scalar, congrArg Subtype.val hscalar⟩

set_option linter.unusedVariables false in
public theorem gl2_exists_principal_series_map_of_unipotent_fixed
    {F : Type*} [Field F] [Finite F]
    (size : ℕ) (rho : Representation ℂ (GL (Fin 2) F) (Fin size → ℂ))
    (hirred : Representation.IsIrreducible rho)
    (hfixed : ∃ vector, vector ≠ 0 ∧ ∀ parameter : F,
      rho (Matrix.GeneralLinearGroup.upperRightHom parameter) vector = vector) :
    ∃ tau : Representation ℂ (GLTwo.borelSubgroup F) ℂ,
      (∀ parameter : F, tau (GLTwo.upperUnipotent F parameter) = 1) ∧
      ∃ morphism : Representation.IntertwiningMap
        (Representation.ind (GLTwo.borelSubgroup F).subtype tau) rho,
        morphism ≠ 0 := by
  classical
  obtain ⟨vector, hvector, hfixedVector, hscalar⟩ := borel_eigenvector size rho hfixed
  choose scalar hscalar using hscalar
  have hone : scalar 1 = 1 := by
    apply smul_left_injective ℂ hvector
    change scalar 1 • vector = (1 : ℂ) • vector
    rw [← hscalar]
    simp
  have hmul (left right : GLTwo.borelSubgroup F) :
      scalar (left * right) = scalar left * scalar right := by
    apply smul_left_injective ℂ hvector
    change scalar (left * right) • vector = (scalar left * scalar right) • vector
    rw [← hscalar, Subgroup.coe_mul, map_mul, Module.End.mul_apply,
      hscalar, map_smul, hscalar, smul_smul, mul_comm]
  let tau : Representation ℂ (GLTwo.borelSubgroup F) ℂ :=
    { toFun matrix := scalar matrix • (1 : Module.End ℂ ℂ)
      map_one' := by simp [hone]
      map_mul' left right := by
        apply LinearMap.ext
        intro value
        simp [hmul, mul_left_comm, mul_assoc] }
  have htrivial (parameter : F) : tau (GLTwo.upperUnipotent F parameter) = 1 := by
    have hscalarOne : scalar (GLTwo.upperUnipotent F parameter) = 1 := by
      apply smul_left_injective ℂ hvector
      change scalar (GLTwo.upperUnipotent F parameter) • vector = (1 : ℂ) • vector
      rw [← hscalar, GLTwo.coe_upperUnipotent, hfixedVector, one_smul]
    simp [tau, hscalarOne]
  let inclusion : Representation.IntertwiningMap tau
      (rho.comp (GLTwo.borelSubgroup F).subtype) :=
    { toLinearMap := LinearMap.toSpanSingleton ℂ _ vector
      isIntertwining' matrix := by
        apply LinearMap.ext
        intro value
        change (scalar matrix * value) • vector = rho matrix.val (value • vector)
        rw [map_smul, hscalar, smul_smul, mul_comm] }
  have hinclusion : inclusion ≠ 0 := by
    intro hzero
    have hvalue := congrArg (fun morphism => morphism (1 : ℂ)) hzero
    exact hvector (by simpa [inclusion] using hvalue)
  let induced : Representation.IntertwiningMap
      (Representation.ind (GLTwo.borelSubgroup F).subtype tau) rho :=
    { toLinearMap := Representation.Coinvariants.lift _
        (TensorProduct.lift <| (Finsupp.lift _ _ _ fun matrix =>
          rho matrix⁻¹ ∘ₗ inclusion.toLinearMap) ∘ₗ
          (MonoidAlgebra.coeffLinearEquiv ℂ).toLinearMap)
        (fun matrix => by
          ext groupElement value
          simp only [LinearMap.coe_comp, Function.comp_apply, MonoidAlgebra.lsingle_apply]
          simp [Representation.ofMulAction_single, mul_inv_rev,
            Representation.IntertwiningMap.isIntertwining tau
              (rho.comp (GLTwo.borelSubgroup F).subtype) inclusion matrix])
      isIntertwining' matrix := by ext; simp }
  refine ⟨tau, htrivial, induced, ?_⟩
  intro hzero
  apply hinclusion
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro value
  have hvalue := congrArg (fun morphism => morphism
    (Representation.IndV.mk (GLTwo.borelSubgroup F).subtype tau 1 value)) hzero
  simpa [induced] using hvalue
