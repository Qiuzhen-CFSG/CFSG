module

public import Theory.Representation.FiniteIndecomposableSummands
public import Theory.Representation.NilpotentIndecomposable
public import Theory.Representation.PermutationBasisOrbits
public import Mathlib.LinearAlgebra.Matrix.Permutation
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.Algebra.CharP.Lemmas
public import Mathlib.Algebra.CharP.Algebra

/-!
# Summands of cyclic permutation modules in characteristic `p`

A transitive cyclic permutation module of prime-power period is indecomposable
in characteristic `p`. Indeed, the permutation operator minus one is nilpotent
and its kernel consists of constant functions, so commuting idempotents are
trivial. Finite Krull--Schmidt summand selection then assigns complementary
families of whole orbits to the image and kernel of any commuting idempotent.
The resulting module equivalence gives a matrix unit commuting with the
permutation and conjugating the selected diagonal projector to the idempotent.

The main result is `CyclicPermutation.exists_unit_conj_diagonal_of_prime`; its linear-map
form is `CyclicPermutation.exists_linearEquiv_idempotent_of_prime`.

The matrix convention is Mathlib's row permutation: `σ.permMatrix k` acts on a
column vector by precomposition with `σ`.

Source application: Fong, *Some Sylow subgroups of order 32 and a
characterization of U(3,3)*, J. Algebra 6 (1967), p. 71, equation (6),
citing Brauer--Suzuki, Section I.
-/

public section
noncomputable section

namespace Matrix

variable {k ι : Type*} [Field k] [Fintype ι] [DecidableEq ι]

/-- Powers of a single permutation matrix respect powers despite the reversed
product convention for distinct permutations. -/
theorem permMatrix_pow_eq (σ : Equiv.Perm ι) (m : ℕ) :
    (σ.permMatrix k) ^ m = (σ ^ m).permMatrix k := by
  induction m with
  | zero => simp
  | succ m ih => rw [pow_succ', pow_succ, permMatrix_mul, ih]

/-- A prime-power-period permutation is unipotent in characteristic `p`. -/
theorem isNilpotent_permMatrix_sub_one_of_prime {p : ℕ} [Fact p.Prime] [CharP k p]
    (σ : Equiv.Perm ι) {n : ℕ} (hσ : σ ^ (p ^ n) = 1) :
    IsNilpotent (σ.permMatrix k - 1) := by
  cases isEmpty_or_nonempty ι
  · exact ⟨1, Subsingleton.elim _ _⟩
  let : CharP (Matrix ι ι k) p :=
    charP_of_injective_ringHom (algebraMap k (Matrix ι ι k)).injective p
  refine ⟨p ^ n, ?_⟩
  rw [sub_pow_char_pow_of_commute p n (Commute.one_right _),
    permMatrix_pow_eq, hσ, permMatrix_one, one_pow, sub_self]

/-- The diagonal projector of an invariant set commutes with the permutation. -/
theorem permMatrix_commute_diagonal_indicator (σ : Equiv.Perm ι) (s : Set ι)
    [DecidablePred (· ∈ s)] (hs : ∀ i, σ i ∈ s ↔ i ∈ s) :
    Commute (σ.permMatrix k) (diagonal (fun i => if i ∈ s then 1 else 0)) := by
  change _ * _ = _ * _
  rw [PEquiv.toMatrix_toPEquiv_mul, PEquiv.mul_toMatrix_toPEquiv]
  ext i j
  simp only [submatrix_apply, id_eq, diagonal_apply]
  by_cases hij : σ i = j
  · subst j
    simp [hs]
  · have hij' : i ≠ σ.symm j := fun h => hij (by simp [h])
    simp [hij, hij']

/-- Characteristic-two specialization, retaining the original API. -/
theorem isNilpotent_permMatrix_sub_one [CharP k 2]
    (σ : Equiv.Perm ι) {n : ℕ} (hσ : σ ^ (2 ^ n) = 1) :
    IsNilpotent (σ.permMatrix k - 1) := by
  exact isNilpotent_permMatrix_sub_one_of_prime (p := 2) σ hσ

end Matrix

namespace CyclicPermutation

variable {k ι : Type*} [Field k] [Fintype ι] [DecidableEq ι]

/-- The polynomial module whose variable acts by the row-permutation matrix. -/
abbrev moduleOf (k : Type*) [Field k] (σ : Equiv.Perm ι) :=
  Module.AEval' (σ.permMatrix k).mulVecLin

/-- The linear operator underlying the polynomial module is unipotent. -/
theorem isNilpotent_operator_sub_one_of_prime {p : ℕ} [Fact p.Prime] [CharP k p]
    (σ : Equiv.Perm ι) {n : ℕ} (hσ : σ ^ (p ^ n) = 1) :
    IsNilpotent ((σ.permMatrix k).mulVecLin - 1) := by
  have hnil := (Matrix.isNilpotent_permMatrix_sub_one_of_prime (k := k) σ hσ).map
    (Matrix.toLinAlgEquiv' : Matrix ι ι k ≃ₐ[k] Module.End k (ι → k))
  have hmap : Matrix.toLinAlgEquiv' (σ.permMatrix k) =
      (σ.permMatrix k).mulVecLin := by ext w i; rfl
  simpa only [map_sub, map_one, hmap] using hnil

/-- In a transitive cyclic permutation module, fixed vectors are constant. -/
theorem fixed_eq_const_of_isPretransitive (σ : Equiv.Perm ι)
    [MulAction.IsPretransitive (Subgroup.zpowers σ) ι]
    (i₀ : ι) (v : ι → k) (hv : (σ.permMatrix k).mulVecLin v = v) :
    v = v i₀ • (fun _ : ι => (1 : k)) := by
  have hstep (i : ι) : v (σ i) = v i := by
    exact congrFun (show v ∘ σ = v by simpa [Matrix.mulVecLin_apply,
      Matrix.permMatrix_mulVec] using hv) i
  ext i
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (Subgroup.zpowers σ) i₀ i
  have hinv := Representation.perm_invariant_zpowers σ v hstep g i₀
  change g.val i₀ = i at hg
  simpa [hg] using hinv

/-- A transitive cyclic `p`-group permutation module in characteristic `p`
is indecomposable as a polynomial module. -/
theorem isIndecomposable_moduleOf_of_prime {p : ℕ} [Fact p.Prime] [CharP k p] [Nonempty ι]
    (σ : Equiv.Perm ι) [MulAction.IsPretransitive (Subgroup.zpowers σ) ι]
    {n : ℕ} (hσ : σ ^ (p ^ n) = 1) :
    Module.IsIndecomposable (Polynomial k) (moduleOf k σ) := by
  let i₀ : ι := Classical.choice inferInstance
  apply Module.isIndecomposable_aeval_of_nilpotent_sub_one_ker_line
    (σ.permMatrix k).mulVecLin
    (v := fun _ : ι => (1 : k))
  · exact isNilpotent_operator_sub_one_of_prime σ hσ
  · intro h
    exact one_ne_zero (congrFun h i₀)
  · simp [Matrix.permMatrix_mulVec, Function.comp_def]
  · intro w hw
    exact ⟨w i₀, fixed_eq_const_of_isPretransitive σ i₀ w hw⟩

/-- On a transitive orbit, an idempotent commuting with a prime-power permutation
matrix in characteristic `p` is zero or one. -/
theorem idempotent_eq_zero_or_one_of_prime {p : ℕ} [Fact p.Prime] [CharP k p]
    (σ : Equiv.Perm ι) [MulAction.IsPretransitive (Subgroup.zpowers σ) ι]
    {n : ℕ} (hσ : σ ^ (p ^ n) = 1)
    (P : Matrix ι ι k) (hP : IsIdempotentElem P)
    (hcomm : Commute (σ.permMatrix k) P) : P = 0 ∨ P = 1 := by
  cases isEmpty_or_nonempty ι
  · exact Or.inl (Subsingleton.elim _ _)
  let i₀ : ι := Classical.choice inferInstance
  let f : Matrix ι ι k ≃ₐ[k] Module.End k (ι → k) := Matrix.toLinAlgEquiv'
  have hmap (M : Matrix ι ι k) : f M = M.mulVecLin := by ext w i; rfl
  have hnil : IsNilpotent (f (σ.permMatrix k) - 1) := by
    rw [hmap]
    exact isNilpotent_operator_sub_one_of_prime σ hσ
  have hc : Commute (f (σ.permMatrix k) - 1) (f P) :=
    (hcomm.map f).sub_left (Commute.one_left _)
  have hfixed (w : ι → k) (hw : (f (σ.permMatrix k) - 1) w = 0) :
      ∃ a : k, w = a • (fun _ : ι => (1 : k)) := by
    refine ⟨w i₀, fixed_eq_const_of_isPretransitive σ i₀ w ?_⟩
    exact sub_eq_zero.mp (by simpa only [LinearMap.sub_apply, Module.End.one_apply,
      hmap] using hw)
  rcases LinearMap.idempotent_eq_zero_or_one_of_nilpotent_ker_line
    _ (f P) hnil (hP.map f) hc (fun _ : ι => (1 : k))
    (fun h => one_ne_zero (congrFun h i₀))
    (by simp [hmap, Matrix.permMatrix_mulVec, Function.comp_def]) hfixed with hz | ho
  · exact Or.inl (f.injective (hz.trans f.map_zero.symm))
  · exact Or.inr (f.injective (ho.trans f.map_one.symm))

section OrbitDecomposition

attribute [local instance] Fintype.ofFinite Classical.propDecidable
open MulAction Matrix

private abbrev orbitPerm (σ : Equiv.Perm ι)
    (q : orbitRel.Quotient (Subgroup.zpowers σ) ι) : Equiv.Perm q.orbit :=
  MulAction.toPerm (⟨σ, Subgroup.mem_zpowers σ⟩ : Subgroup.zpowers σ)

omit [Fintype ι] [DecidableEq ι] in
private theorem orbitPerm_pow (σ : Equiv.Perm ι)
    (q : orbitRel.Quotient (Subgroup.zpowers σ) ι) {p n : ℕ} (hσ : σ ^ (p ^ n) = 1) :
    orbitPerm σ q ^ (p ^ n) = 1 := by
  change (MulAction.toPermHom (Subgroup.zpowers σ) q.orbit) _ ^ _ = _
  rw [← map_pow]
  have h : (⟨σ, Subgroup.mem_zpowers σ⟩ : Subgroup.zpowers σ) ^ (p ^ n) = 1 :=
    Subtype.ext hσ
  rw [h, map_one]

omit [Fintype ι] [DecidableEq ι] in
private theorem orbitPerm_pretransitive (σ : Equiv.Perm ι)
    (q : orbitRel.Quotient (Subgroup.zpowers σ) ι) :
    MulAction.IsPretransitive (Subgroup.zpowers (orbitPerm σ q)) q.orbit := by
  constructor
  intro x y
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (Subgroup.zpowers σ) x y
  obtain ⟨z, hz⟩ := g.property
  let a : Subgroup.zpowers σ := ⟨σ, Subgroup.mem_zpowers σ⟩
  have ha : a ^ z = g := Subtype.ext hz
  refine ⟨⟨(orbitPerm σ q) ^ z, Subgroup.zpow_mem_zpowers _ _⟩, ?_⟩
  change ((MulAction.toPermHom (Subgroup.zpowers σ) q.orbit) a ^ z) x = y
  rw [← map_zpow, ha]
  exact hg

private def orbitEquiv (σ : Equiv.Perm ι) :
    (ι → k) ≃ₗ[k] (∀ q : orbitRel.Quotient (Subgroup.zpowers σ) ι,
      moduleOf k (orbitPerm σ q)) where
  toFun v q := Module.AEval'.of _ (fun x => v x.val)
  invFun v x := (Module.AEval'.of _).symm
    (v (Quotient.mk'' x)) ⟨x, orbitRel.Quotient.mem_orbit.mpr rfl⟩
  left_inv v := rfl
  right_inv v := by
    funext q
    apply (Module.AEval'.of _).symm.injective
    funext x
    obtain ⟨x, hx⟩ := x
    have hq := orbitRel.Quotient.mem_orbit.mp hx
    subst q
    rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private def orbitPolynomialEquiv (σ : Equiv.Perm ι) :
    moduleOf k σ ≃ₗ[Polynomial k]
      (∀ q : orbitRel.Quotient (Subgroup.zpowers σ) ι, moduleOf k (orbitPerm σ q)) := by
  apply LinearEquiv.ofAEval _ (orbitEquiv σ)
  intro v
  funext q
  apply (Module.AEval'.of _).symm.injective
  rw [Pi.smul_apply, Module.AEval'.of_symm_X_smul]
  ext x
  change ((σ.permMatrix k).mulVecLin v) x.val =
    ((orbitPerm σ q).permMatrix k).mulVecLin (fun y => v y.val) x
  simp only [Matrix.mulVecLin_apply, Matrix.permMatrix_mulVec]
  rfl

private theorem orbit_indecomposable {p : ℕ} [Fact p.Prime] [CharP k p] (σ : Equiv.Perm ι)
    {n : ℕ} (hσ : σ ^ (p ^ n) = 1)
    (q : orbitRel.Quotient (Subgroup.zpowers σ) ι) :
    Module.IsIndecomposable (Polynomial k) (moduleOf k (orbitPerm σ q)) := by
  let : Nonempty q.orbit := q.nonempty_orbit.to_subtype
  let := orbitPerm_pretransitive σ q
  exact isIndecomposable_moduleOf_of_prime (orbitPerm σ q) (orbitPerm_pow σ q hσ)

/-- A commuting idempotent becomes restriction to a union of permutation orbits
after a linear change of coordinates commuting with the permutation operator. -/
theorem exists_linearEquiv_idempotent_of_prime {p : ℕ} [Fact p.Prime] [CharP k p] (σ : Equiv.Perm ι)
    {n : ℕ} (hσ : σ ^ (p ^ n) = 1)
    (P : Matrix ι ι k) (hP : IsIdempotentElem P)
    (hc : Commute (σ.permMatrix k) P) :
    ∃ (s : Set ι) (w : (ι → k) ≃ₗ[k] (ι → k)),
      (∀ x, σ x ∈ s ↔ x ∈ s) ∧
      (∀ v, w ((σ.permMatrix k).mulVecLin v) = (σ.permMatrix k).mulVecLin (w v)) ∧
      (∀ v, w (P.mulVecLin v) = s.indicator (w v)) := by
  let T := (σ.permMatrix k).mulVecLin
  let o := Module.AEval'.of T
  have hcomm (v : ι → k) : P.mulVecLin (T v) = T (P.mulVecLin v) := by
    have h := congrArg (fun M : Matrix ι ι k => M *ᵥ v) hc.eq
    simpa only [T, Matrix.mulVecLin_apply, Matrix.mulVec_mulVec] using h.symm
  let p : Module.End (Polynomial k) (moduleOf k σ) :=
    LinearMap.ofAEval T (o.toLinearMap.comp P.mulVecLin) (by
      intro v
      change o (P.mulVecLin (T v)) = (Polynomial.X : Polynomial k) • o (P.mulVecLin v)
      rw [Module.AEval'.X_smul_of, hcomm])
  have hp : IsIdempotentElem p := by
    ext v
    apply o.symm.injective
    change P *ᵥ (P *ᵥ o.symm v) = P *ᵥ o.symm v
    rw [Matrix.mulVec_mulVec, hP.eq]
  obtain ⟨s, d, hd⟩ := Module.exists_equiv_pi_of_idempotent
    (F := k) (orbit_indecomposable σ hσ) (orbitPolynomialEquiv σ) p hp
  let a := d.trans (orbitPolynomialEquiv σ).symm
  let w := o.trans ((a.restrictScalars k).trans o.symm)
  let S : Set ι := {x | (Quotient.mk'' x : orbitRel.Quotient (Subgroup.zpowers σ) ι) ∈ s}
  refine ⟨S, w, ?_, ?_, ?_⟩
  · intro x
    have hq : (Quotient.mk'' (σ x) : orbitRel.Quotient (Subgroup.zpowers σ) ι) =
        Quotient.mk'' x := Quotient.sound ⟨⟨σ, Subgroup.mem_zpowers σ⟩, rfl⟩
    change _ ∈ s ↔ _ ∈ s
    rw [hq]
  · intro v
    change o.symm (a (o (T v))) = T (o.symm (a (o v)))
    rw [← Module.AEval'.X_smul_of, map_smul, Module.AEval'.of_symm_X_smul]
  · intro v
    ext x
    let q : orbitRel.Quotient (Subgroup.zpowers σ) ι := Quotient.mk'' x
    let y : q.orbit := ⟨x, orbitRel.Quotient.mem_orbit.mpr rfl⟩
    have hw (v : ι → k) : w v x = (Module.AEval'.of _).symm (d (o v) q) y := rfl
    rw [hw]
    change (Module.AEval'.of _).symm (d (p (o v)) q) y = S.indicator (w v) x
    by_cases hx : q ∈ s
    · rw [(hd (o v) q).1 hx, Set.indicator_of_mem (show x ∈ S from hx), hw]
    · rw [(hd (o v) q).2 hx, map_zero, Set.indicator_of_notMem (show x ∉ S from hx)]
      rfl

/-- An idempotent commuting with a prime-power permutation matrix in characteristic
`p` is conjugate, by a commuting unit, to the diagonal projector of a union of orbits. -/
theorem exists_unit_conj_diagonal_of_prime {p : ℕ} [Fact p.Prime] [CharP k p] (σ : Equiv.Perm ι)
    {n : ℕ} (hσ : σ ^ (p ^ n) = 1)
    (P : Matrix ι ι k) (hP : IsIdempotentElem P)
    (hc : Commute (σ.permMatrix k) P) :
    ∃ (s : Set ι) (U : (Matrix ι ι k)ˣ),
      (∀ x, σ x ∈ s ↔ x ∈ s) ∧ Commute (σ.permMatrix k) (U : Matrix ι ι k) ∧
      P = (U : Matrix ι ι k) * Matrix.diagonal (s.indicator (fun _ => 1)) *
        (↑(U⁻¹) : Matrix ι ι k) := by
  obtain ⟨s, w, hs, hwT, hwP⟩ := exists_linearEquiv_idempotent_of_prime σ hσ P hP hc
  let L : Matrix ι ι k ≃ₐ[k] Module.End k (ι → k) := Matrix.toLinAlgEquiv'
  let u : (Module.End k (ι → k))ˣ :=
    { val := w.symm.toLinearMap
      inv := w.toLinearMap
      val_inv := by apply LinearMap.ext; intro v; exact w.symm_apply_apply v
      inv_val := by apply LinearMap.ext; intro v; exact w.apply_symm_apply v }
  let U := Units.map L.symm.toMonoidHom u
  have hU : L (U : Matrix ι ι k) = w.symm.toLinearMap := by simp [U, u]
  have hUi : L (↑(U⁻¹) : Matrix ι ι k) = w.toLinearMap := by simp [U, u]
  refine ⟨s, U, hs, ?_, ?_⟩
  · apply L.injective
    rw [map_mul, map_mul, hU]
    apply LinearMap.ext
    intro v
    change (σ.permMatrix k).mulVecLin (w.symm v) = w.symm ((σ.permMatrix k).mulVecLin v)
    apply w.injective
    rw [hwT, w.apply_symm_apply, w.apply_symm_apply]
  · apply L.injective
    rw [map_mul, map_mul, hU, hUi]
    apply LinearMap.ext
    intro v
    change P.mulVecLin v = w.symm ((Matrix.diagonal (s.indicator (fun _ => 1))).mulVecLin (w v))
    apply w.injective
    rw [w.apply_symm_apply, hwP]
    ext x
    by_cases hx : x ∈ s <;>
      simp [Matrix.mulVec_diagonal, Set.indicator, hx]

end OrbitDecomposition

/-- Characteristic-two specialization, retaining the original API. -/
theorem isNilpotent_operator_sub_one [CharP k 2]
    (σ : Equiv.Perm ι) {n : ℕ} (hσ : σ ^ (2 ^ n) = 1) :
    IsNilpotent ((σ.permMatrix k).mulVecLin - 1) := by
  exact isNilpotent_operator_sub_one_of_prime (p := 2) σ hσ

/-- Characteristic-two specialization, retaining the original API. -/
theorem isIndecomposable_moduleOf [CharP k 2] [Nonempty ι]
    (σ : Equiv.Perm ι) [MulAction.IsPretransitive (Subgroup.zpowers σ) ι]
    {n : ℕ} (hσ : σ ^ (2 ^ n) = 1) :
    Module.IsIndecomposable (Polynomial k) (moduleOf k σ) := by
  exact isIndecomposable_moduleOf_of_prime (p := 2) σ hσ

/-- Characteristic-two specialization, retaining the original API. -/
theorem idempotent_eq_zero_or_one [CharP k 2]
    (σ : Equiv.Perm ι) [MulAction.IsPretransitive (Subgroup.zpowers σ) ι]
    {n : ℕ} (hσ : σ ^ (2 ^ n) = 1)
    (P : Matrix ι ι k) (hP : IsIdempotentElem P)
    (hcomm : Commute (σ.permMatrix k) P) : P = 0 ∨ P = 1 := by
  exact idempotent_eq_zero_or_one_of_prime (p := 2) σ hσ P hP hcomm

/-- Characteristic-two specialization, retaining the original API. -/
theorem exists_linearEquiv_idempotent [CharP k 2] (σ : Equiv.Perm ι)
    {n : ℕ} (hσ : σ ^ (2 ^ n) = 1)
    (P : Matrix ι ι k) (hP : IsIdempotentElem P)
    (hc : Commute (σ.permMatrix k) P) :
    ∃ (s : Set ι) (w : (ι → k) ≃ₗ[k] (ι → k)),
      (∀ x, σ x ∈ s ↔ x ∈ s) ∧
      (∀ v, w ((σ.permMatrix k).mulVecLin v) = (σ.permMatrix k).mulVecLin (w v)) ∧
      (∀ v, w (P.mulVecLin v) = s.indicator (w v)) := by
  exact exists_linearEquiv_idempotent_of_prime (p := 2) σ hσ P hP hc

/-- Characteristic-two specialization, retaining the original API. -/
theorem exists_unit_conj_diagonal [CharP k 2] (σ : Equiv.Perm ι)
    {n : ℕ} (hσ : σ ^ (2 ^ n) = 1)
    (P : Matrix ι ι k) (hP : IsIdempotentElem P)
    (hc : Commute (σ.permMatrix k) P) :
    ∃ (s : Set ι) (U : (Matrix ι ι k)ˣ),
      (∀ x, σ x ∈ s ↔ x ∈ s) ∧ Commute (σ.permMatrix k) (U : Matrix ι ι k) ∧
      P = (U : Matrix ι ι k) * Matrix.diagonal (s.indicator (fun _ => 1)) *
        (↑(U⁻¹) : Matrix ι ι k) := by
  exact exists_unit_conj_diagonal_of_prime (p := 2) σ hσ P hP hc

end CyclicPermutation
