module

public import Theory.SpecificGroups.ClassicalUnitary.OddRankOneComparison
public import Theory.SpecificGroups.ClassicalUnitary.ProjectiveKernel
public import Mathlib.LinearAlgebra.Matrix.Block
public import Mathlib.LinearAlgebra.Matrix.Permutation

/-!
# Fundamental two-space blocks in odd unitary groups

The identity Hermitian form admits commuting special-unitary groups on two
complementary coordinate blocks. Each factor embeds in the actual image in PGL
when the other block is nonempty: that block forces a projectively trivial
scalar to be one. A three-cycle crossing the blocks proves properness of the
two-dimensional factor.

Over a field of order q² with conjugation x ↦ x^q, the two-dimensional special
unitary group is SL₂ over the actual fixed field of order q. A norm-minus-one
element and a nonzero anti-fixed element supply the skew basis used by the
existing determinant calculation. Orthonormalization transports both marked
factors simultaneously into every stored Hermitian form.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
manuscript (1 March 2004), A.2.17, printed pp.38–39; Huppert II.10.4 for the
Hermitian bases. These constructions prove the fundamental-subgroup clauses;
the full centralizer residual and complementary rank bounds are separate results.
-/

@[expose] public noncomputable section
open Matrix BenderSuzuki.MatrixGroups
namespace Theory.SpecificGroups.ClassicalUnitary.OddFundamental
variable {F : Type*} [Field F] (σ : F ≃+* F) (hσ : Function.Involutive σ)

def form (n : ℕ) : HermitianForm n F where
  conj := σ
  conj_involutive := hσ
  form := 1
  form_hermitian := by
    intro i j
    by_cases h : i = j <;> simp [Matrix.one_apply, h, Ne.symm]
  form_nondegenerate := by simp

variable {m n : ℕ}

def blockMatrix (A : Matrix (Fin m) (Fin m) F) (B : Matrix (Fin n) (Fin n) F) :
    Matrix (Fin (m + n)) (Fin (m + n)) F :=
  Matrix.reindex finSumFinEquiv finSumFinEquiv (fromBlocks A 0 0 B)

theorem blockMatrix_one : blockMatrix (1 : Matrix (Fin m) (Fin m) F)
    (1 : Matrix (Fin n) (Fin n) F) = 1 := by
  rw [blockMatrix, fromBlocks_one]
  exact (reindexRingEquiv F finSumFinEquiv).map_one

theorem blockMatrix_mul (A C : Matrix (Fin m) (Fin m) F)
    (B D : Matrix (Fin n) (Fin n) F) :
    blockMatrix (A * C) (B * D) = blockMatrix A B * blockMatrix C D := by
  change (reindexRingEquiv F finSumFinEquiv) _ =
    (reindexRingEquiv F finSumFinEquiv) _ * (reindexRingEquiv F finSumFinEquiv) _
  rw [← map_mul]
  congr 1
  simp [fromBlocks_multiply]

theorem blockMatrix_det (A : Matrix (Fin m) (Fin m) F)
    (B : Matrix (Fin n) (Fin n) F) :
    (blockMatrix A B).det = A.det * B.det := by
  rw [blockMatrix, det_reindex_self, det_fromBlocks_zero₂₁]

theorem blockMatrix_adj (A : Matrix (Fin m) (Fin m) F)
    (B : Matrix (Fin n) (Fin n) F) :
    (form σ hσ (m + n)).conjTranspose (blockMatrix A B) =
      blockMatrix ((form σ hσ m).conjTranspose A) ((form σ hσ n).conjTranspose B) := by
  ext i j
  obtain ⟨i, rfl⟩ := finSumFinEquiv.surjective i
  obtain ⟨j, rfl⟩ := finSumFinEquiv.surjective j
  cases i <;> cases j <;>
    simp [blockMatrix, reindex_apply, HermitianForm.conjTranspose, form]

def blockMatrixHom : (form σ hσ m).specialSubgroup × (form σ hσ n).specialSubgroup →*
    Matrix (Fin (m + n)) (Fin (m + n)) F where
  toFun A := blockMatrix A.1.val.val A.2.val.val
  map_one' := blockMatrix_one
  map_mul' _ _ := blockMatrix_mul _ _ _ _

def block : (form σ hσ m).specialSubgroup × (form σ hσ n).specialSubgroup →*
    (form σ hσ (m + n)).specialSubgroup :=
  (blockMatrixHom σ hσ).toHomUnits.codRestrict _ fun A => by
    rw [HermitianForm.mem_specialSubgroup_iff]
    have hA := ((form σ hσ m).mem_specialSubgroup_iff A.1.val).mp A.1.property
    have hB := ((form σ hσ n).mem_specialSubgroup_iff A.2.val).mp A.2.property
    refine ⟨?_, Units.ext ?_⟩
    · change (form σ hσ (m+n)).conjTranspose (blockMatrix A.1.val.val A.2.val.val) * 1 *
        blockMatrix A.1.val.val A.2.val.val = 1
      rw [mul_one, blockMatrix_adj, ← blockMatrix_mul]
      have ha : (form σ hσ m).conjTranspose A.1.val.val * A.1.val.val = 1 := by
        simpa [form] using hA.1
      have hb : (form σ hσ n).conjTranspose A.2.val.val * A.2.val.val = 1 := by
        simpa [form] using hB.1
      rw [ha, hb, blockMatrix_one]
    · change (blockMatrix A.1.val.val A.2.val.val).det = 1
      rw [blockMatrix_det]
      have ha := congrArg Units.val hA.2
      have hb := congrArg Units.val hB.2
      change A.1.val.val.det = 1 at ha
      change A.2.val.val.det = 1 at hb
      rw [ha, hb, one_mul]

def left : (form σ hσ m).specialSubgroup →* (form σ hσ (m+n)).specialSubgroup :=
  (block σ hσ).comp (MonoidHom.inl _ _)
def right : (form σ hσ n).specialSubgroup →* (form σ hσ (m+n)).specialSubgroup :=
  (block σ hσ).comp (MonoidHom.inr _ _)
def projectLeft : (form σ hσ m).specialSubgroup →*
    ProjectiveSpecialUnitaryMatrixGroup (form σ hσ (m+n)) :=
  (ProjectiveKernel.project _).comp (left σ hσ)
def projectRight : (form σ hσ n).specialSubgroup →*
    ProjectiveSpecialUnitaryMatrixGroup (form σ hσ (m+n)) :=
  (ProjectiveKernel.project _).comp (right σ hσ)

@[simp] theorem blockMatrix_inl_inl (A : Matrix (Fin m) (Fin m) F)
    (B : Matrix (Fin n) (Fin n) F) (i j : Fin m) :
    blockMatrix A B (finSumFinEquiv (.inl i)) (finSumFinEquiv (.inl j)) = A i j := by
  simp [blockMatrix, reindex_apply]
@[simp] theorem blockMatrix_inr_inr (A : Matrix (Fin m) (Fin m) F)
    (B : Matrix (Fin n) (Fin n) F) (i j : Fin n) :
    blockMatrix A B (finSumFinEquiv (.inr i)) (finSumFinEquiv (.inr j)) = B i j := by
  simp [blockMatrix, reindex_apply]
@[simp] theorem blockMatrix_inl_inr (A : Matrix (Fin m) (Fin m) F)
    (B : Matrix (Fin n) (Fin n) F) (i : Fin m) (j : Fin n) :
    blockMatrix A B (finSumFinEquiv (.inl i)) (finSumFinEquiv (.inr j)) = 0 := by
  simp [blockMatrix, reindex_apply]

/-- Block extension is already faithful on the covering special unitary group. -/
theorem left_injective : Function.Injective (left σ hσ (m := m) (n := n)) := by
  intro A B h
  apply Subtype.ext
  apply Units.ext
  ext i j
  have hh := congrArg (fun g : (form σ hσ (m+n)).specialSubgroup =>
    g.val.val (finSumFinEquiv (.inl i)) (finSumFinEquiv (.inl j))) h
  change blockMatrix A.val.val (1 : Matrix (Fin n) (Fin n) F) _ _ =
    blockMatrix B.val.val (1 : Matrix (Fin n) (Fin n) F) _ _ at hh
  simpa only [blockMatrix_inl_inl] using hh

theorem projectLeft_injective [NeZero n] :
    Function.Injective (projectLeft σ hσ (m := m) (n := n)) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro A hA
  have hp : ProjGenLinGroup.mk (left σ hσ A).val = 1 := congrArg Subtype.val hA
  rw [ProjGenLinGroup.mk_eq_one, GeneralLinearGroup.center_eq_range_scalar] at hp
  obtain ⟨u, hu⟩ := hp
  have he := congrArg (fun g : GL (Fin (m+n)) F =>
    g.val (finSumFinEquiv (.inr (0 : Fin n))) (finSumFinEquiv (.inr (0 : Fin n)))) hu
  change (GeneralLinearGroup.scalar (Fin (m+n)) u).val _ _ =
    blockMatrix A.val.val (1 : Matrix (Fin n) (Fin n) F) _ _ at he
  have hu1 : (u : F) = 1 := by
    rw [blockMatrix_inr_inr] at he
    simpa [GeneralLinearGroup.coe_scalar] using he
  have huone : u = 1 := Units.ext hu1
  rw [huone, map_one] at hu
  apply Subtype.ext
  apply Units.ext
  ext i j
  have hh := congrArg (fun g : GL (Fin (m+n)) F =>
    g.val (finSumFinEquiv (.inl i)) (finSumFinEquiv (.inl j))) hu
  change (1 : Matrix (Fin (m+n)) (Fin (m+n)) F) _ _ =
    blockMatrix A.val.val (1 : Matrix (Fin n) (Fin n) F) _ _ at hh
  rw [blockMatrix_inl_inl] at hh
  simpa [Matrix.one_apply] using hh.symm

theorem projectRight_injective [NeZero m] :
    Function.Injective (projectRight σ hσ (m := m) (n := n)) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro A hA
  have hp : ProjGenLinGroup.mk (right σ hσ A).val = 1 := congrArg Subtype.val hA
  rw [ProjGenLinGroup.mk_eq_one, GeneralLinearGroup.center_eq_range_scalar] at hp
  obtain ⟨u, hu⟩ := hp
  have he := congrArg (fun g : GL (Fin (m+n)) F =>
    g.val (finSumFinEquiv (.inl (0 : Fin m))) (finSumFinEquiv (.inl (0 : Fin m)))) hu
  change (GeneralLinearGroup.scalar (Fin (m+n)) u).val _ _ =
    blockMatrix (1 : Matrix (Fin m) (Fin m) F) A.val.val _ _ at he
  have hu1 : (u : F) = 1 := by
    rw [blockMatrix_inl_inl] at he
    simpa [GeneralLinearGroup.coe_scalar] using he
  have huone : u = 1 := Units.ext hu1
  rw [huone, map_one] at hu
  apply Subtype.ext
  apply Units.ext
  ext i j
  have hh := congrArg (fun g : GL (Fin (m+n)) F =>
    g.val (finSumFinEquiv (.inr i)) (finSumFinEquiv (.inr j))) hu
  change (1 : Matrix (Fin (m+n)) (Fin (m+n)) F) _ _ =
    blockMatrix (1 : Matrix (Fin m) (Fin m) F) A.val.val _ _ at hh
  rw [blockMatrix_inr_inr] at hh
  simpa [Matrix.one_apply] using hh.symm

theorem factors_commute (A : (form σ hσ m).specialSubgroup)
    (B : (form σ hσ n).specialSubgroup) :
    Commute (projectLeft σ hσ A) (projectRight σ hσ B) := by
  have h : Commute (A, (1 : (form σ hσ n).specialSubgroup))
      ((1 : (form σ hσ m).specialSubgroup), B) := by
    change (A, 1) * (1, B) = (1, B) * (A, 1)
    simp
  exact (h.map (block σ hσ)).map (ProjectiveKernel.project _)

private def permutationSU {k : ℕ} (p : Equiv.Perm (Fin k))
    (hp : Equiv.Perm.sign p = 1) : (form σ hσ k).specialSubgroup :=
  ⟨GeneralLinearGroup.mkOfDetNeZero (p.permMatrix F) (by simp [hp]), by
    rw [HermitianForm.mem_specialSubgroup_iff]
    refine ⟨?_, Units.ext ?_⟩
    · change (form σ hσ k).conjTranspose (p.permMatrix F) * 1 * p.permMatrix F = 1
      have ha : (form σ hσ k).conjTranspose (p.permMatrix F) =
          (p.permMatrix F).transpose := by
        ext i j
        simp [form, HermitianForm.conjTranspose, Equiv.Perm.permMatrix,
          PEquiv.toMatrix_apply, Equiv.toPEquiv_apply, apply_ite]
      rw [ha, mul_one, transpose_permMatrix, ← permMatrix_mul]
      simp
    · change (p.permMatrix F).det = 1
      simp [hp]⟩

theorem projectLeft_range_ne_top [NeZero n] :
    (projectLeft σ hσ (m := 2) (n := n)).range ≠ ⊤ := by
  let i : Fin (2+n) := finSumFinEquiv (.inl (0 : Fin 2))
  let j : Fin (2+n) := finSumFinEquiv (.inl (1 : Fin 2))
  let k : Fin (2+n) := finSumFinEquiv (.inr (0 : Fin n))
  have hij : i ≠ j := by simp [i, j]
  have hjk : j ≠ k := by
    intro h
    have hh := finSumFinEquiv.injective h
    cases hh
  let p : Equiv.Perm (Fin (2+n)) := Equiv.swap j k * Equiv.swap i j
  have hp : Equiv.Perm.sign p = 1 := by
    simp [p, map_mul, Equiv.Perm.sign_swap hij, Equiv.Perm.sign_swap hjk]
  let g := permutationSU σ hσ p hp
  have hg : g.val.val i k = 1 := by
    change p.permMatrix F i k = 1
    simp [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, Equiv.toPEquiv_apply,
      p, Equiv.Perm.mul_apply]
  intro htop
  have hm : ProjectiveKernel.project _ g ∈ (projectLeft σ hσ (m := 2) (n := n)).range :=
    htop ▸ Subgroup.mem_top _
  obtain ⟨A, hA⟩ := hm
  have hproj : ProjGenLinGroup.mk (left σ hσ A).val = ProjGenLinGroup.mk g.val :=
    congrArg Subtype.val hA
  obtain ⟨u, hu⟩ := ProjGenLinGroup.mk_eq_mk_iff.mp hproj
  have he := congrArg (fun x : GL (Fin (2+n)) F => x.val i k) hu
  change (blockMatrix A.val.val (1 : Matrix (Fin n) (Fin n) F) *
    Matrix.scalar (Fin (2+n)) (u : F)) i k = g.val.val i k at he
  rw [hg] at he
  have hz : blockMatrix A.val.val (1 : Matrix (Fin n) (Fin n) F) i k = 0 :=
    blockMatrix_inl_inr _ _ _ _
  simp [Matrix.scalar, Matrix.mul_diagonal, hz] at he

variable [Finite F]

theorem nonempty_specialTwoEquiv_odd {q : ℕ} (hq : IsPrimePow q) (ho : Odd q)
    (hc : Nat.card F = q ^ 2) (hj : ∀ x, σ x = x ^ q) :
    Nonempty ((form σ hσ 2).specialSubgroup ≃*
      SpecialLinearGroup (Fin 2) (FixedBy.subfield F σ)) := by
  let I := form σ hσ 2
  have hk := I.fixed_card_prime_power hq hc hj
  have h2 : (2 : F) ≠ 0 := by
    intro h
    let : CharP F 2 := (CharP.charP_iff_prime_eq_zero Nat.prime_two).mpr h
    let : Fintype F := Fintype.ofFinite F
    have hh := FiniteField.even_card_of_char_two (ringChar.eq F 2)
    rw [← Nat.card_eq_fintype_card, hc] at hh
    exact Nat.not_even_iff_odd.mpr (ho.pow : Odd (q ^ 2))
      (even_iff_two_dvd.mpr (Nat.dvd_of_mod_eq_zero hh))
  obtain ⟨z, _, hz⟩ := BenderSuzuki.External.huppert_II_10_4_norm_surjective I q hc hk
    (-1) (by simp) (by simp)
  have hex : ∃ a : F, σ a ≠ a := by
    by_contra! hall
    let e : {x : F // I.conj x = x} ≃ F :=
      { toFun := Subtype.val
        invFun := fun a => ⟨a, hall a⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    have he := Nat.card_congr e
    rw [hk, hc] at he
    have hq1 : 1 < q := hq.one_lt
    nlinarith
  obtain ⟨a, ha⟩ := hex
  have ht0 : a - σ a ≠ 0 := sub_ne_zero.mpr ha.symm
  have ht : I.conj (a - σ a) = -(a - σ a) := by
    change σ (a - σ a) = _
    rw [map_sub, hσ a]
    ring
  obtain ⟨C, _, hC⟩ := HermitianForm.exists_skew_basis I rfl h2 z (a - σ a) hz ht0 ht
  exact ⟨I.specialUnitaryEquivFixed C (2 * (a - σ a)) (mul_ne_zero h2 ht0) hC⟩

/-- Simultaneous transport of both coordinate factors to the stored Hermitian form. -/
theorem exists_fundamental_complement [NeZero n]
    (J : HermitianForm (2+n) F) {q : ℕ} (hq : IsPrimePow q) (ho : Odd q)
    (hc : Nat.card F = q ^ 2) (hj : ∀ x, J.conj x = x ^ q) :
    ∃ (f : SpecialLinearGroup (Fin 2) (FixedBy.subfield F J.conj) →*
        ProjectiveSpecialUnitaryMatrixGroup J)
      (c : (form J.conj J.conj_involutive n).specialSubgroup →*
        ProjectiveSpecialUnitaryMatrixGroup J),
      Function.Injective f ∧ f.range ≠ ⊤ ∧ Function.Injective c ∧
      (∀ a b, Commute (f a) (c b)) := by
  have hk := J.fixed_card_prime_power hq hc hj
  obtain ⟨C, hC⟩ := BenderSuzuki.External.huppert_II_10_4_a_orthonormal_basis
    (2+n) J q hc hk
  let e := (HermitianForm.IdentityGram.projectiveEquiv J C hC).symm
  obtain ⟨a⟩ := nonempty_specialTwoEquiv_odd J.conj J.conj_involutive hq ho hc hj
  let f := e.toMonoidHom.comp
    ((projectLeft J.conj J.conj_involutive (n := n)).comp a.symm.toMonoidHom)
  let c := e.toMonoidHom.comp (projectRight J.conj J.conj_involutive (m := 2) (n := n))
  refine ⟨f, c, e.injective.comp ((projectLeft_injective _ _).comp a.symm.injective), ?_,
    e.injective.comp (projectRight_injective _ _), ?_⟩
  · intro htop
    apply projectLeft_range_ne_top J.conj J.conj_involutive (n := n)
    apply top_unique
    intro x _
    have hx : e x ∈ f.range := htop ▸ Subgroup.mem_top _
    obtain ⟨y, hy⟩ := hx
    exact ⟨a.symm y, e.injective hy⟩
  · intro x y
    exact (factors_commute J.conj J.conj_involutive (a.symm x) y).map e.toMonoidHom

end Theory.SpecificGroups.ClassicalUnitary.OddFundamental
