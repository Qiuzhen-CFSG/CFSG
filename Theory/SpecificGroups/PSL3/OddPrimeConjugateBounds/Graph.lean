module

public import Theory.SpecificGroups.PSL3.OddPrimeConjugateBounds.Defs
public import Theory.SpecificGroups.PSL3.OddInvolutionFixed.Graph
public import Theory.AtlasPort.ExceptionalIsomorphisms.Elementary
public import Theory.SpecificGroups.SU3.OddPrimeSylowAutomorphisms.NormalizedOuterInvolutions.Descent.SymmetricSimilarity.FiniteForms

/-!
# Three inner conjugates of odd-prime PSL₃ graph involutions

Write J for the matrix interchanging coordinates zero and two, and let a be
conjugation by J followed by inverse transpose. This actor inverts both a
three-cycle permutation matrix c and the elementary matrix t = x₀₂(1/2).
The conjugates by 1, c and t therefore generate the inner actors of c² and
t² = x₀₂(1). The cube relation recovers c. Cycling x₀₂ gives x₁₀ and x₂₁;
elementary commutators give the other three roots. Over a prime field, powers
supply every coefficient, so these matrices generate the entire actual PSL₃.

For an arbitrary linear-times-graph involution, its conjugating matrix is
symmetric. Finite-field quadratic-form classification gives CᵀgC = rJ with
r nonzero. The scalar acts trivially on the projective group, so this is a
conjugacy of the actual automorphisms. Transport sends every conjugator to
another element of PSL₃ and preserves the containment of the whole inner group.

Source: Guralnick–Malle, *Classification of 2F-modules I*, (2.6) and
Proposition 4.2, manuscript pp.4 and 9–10; Aschbacher–Smith K.2, p.453.
GM02 explicitly states the count at p = 3; the argument here proves the
requested uniform odd-prime auxiliary bound. Matrix conventions are GLS3 §2.7.
The ternary-form bridge adapts the existing proof in
`SU3/OddPrimeSylowAutomorphisms/NormalizedOuterInvolutions/Descent/SymmetricSimilarity`.
Its finite-field classification and the elementary generation imports retain
the ATLAS attribution and Research and Attribution License 1.0; see
`LICENSES/ATLAS.txt` and `LICENSES/ATLAS-CITATION.cff`.
-/

public section
open scoped MatrixGroups commutatorElement
open Matrix Subgroup
open Matrix.PSL3.OuterSolvable Matrix.PSL3.OddInvolutionFixed
open Matrix.PSL3.OuterSolvable.OddPrimeCoverage
namespace Matrix.PSL3.OddPrimeConjugateBounds.Graph
variable (F : Type*) [Field F]

private def splitGram : GL (Fin 3) F where
  val := !![0, 0, 1; 0, 1, 0; 1, 0, 0]
  inv := !![0, 0, 1; 0, 1, 0; 1, 0, 0]
  val_inv := by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]
  inv_val := by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]

private def cycleGL : GL (Fin 3) F where
  val := !![0, 0, 1; 1, 0, 0; 0, 1, 0]
  inv := !![0, 1, 0; 0, 0, 1; 1, 0, 0]
  val_inv := by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]
  inv_val := by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]

private def cycleSL : SL(3,F) := ⟨(cycleGL F).val, by simp [cycleGL, Matrix.det_fin_three]⟩

private theorem cycleSL_toGL : SpecialLinearGroup.toGL (cycleSL F) = cycleGL F := Units.ext rfl

private def splitActor : MulAut PSL(3,F) := linearConj F (splitGram F) * graph F

private def cycle : PSL(3,F) := QuotientGroup.mk (cycleSL F)

private theorem splitGram_inverseTranspose : inverseTransposeGL (splitGram F) = splitGram F := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

private theorem splitGram_sq : splitGram F ^ 2 = 1 := by
  rw [pow_two]
  apply Units.ext
  exact (splitGram F).val_inv

private theorem splitActor_sq : splitActor F ^ 2 = 1 := by
  simp only [splitActor, pow_two]
  rw [mul_assoc, ← mul_assoc (graph F), graph_linearConj, splitGram_inverseTranspose,
    mul_assoc, ← pow_two, graph_sq, mul_one, ← map_mul, ← pow_two, splitGram_sq, map_one]

private theorem cycle_cube : cycle F ^ 3 = 1 := by
  have h : cycleSL F ^ 3 = 1 := by
    apply SpecialLinearGroup.toGL_injective
    rw [map_pow, cycleSL_toGL, map_one]
    apply Units.ext
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [cycleGL, pow_succ, Matrix.mul_apply, Fin.sum_univ_three]
  simpa only [cycle, QuotientGroup.mk_pow, QuotientGroup.mk_one] using
    congrArg (QuotientGroup.mk : SL(3,F) → PSL(3,F)) h

private theorem splitActor_cycle : splitActor F (cycle F) = (cycle F)⁻¹ := by
  change QuotientGroup.mk (linearConjSL F (splitGram F) (graphSL F (cycleSL F))) = _
  rw [cycle, ← QuotientGroup.mk_inv]
  congr 1
  apply SpecialLinearGroup.toGL_injective
  rw [linearConjSL_toGL, OddInvolutionFixed.graphSL_toGL, map_inv, cycleSL_toGL]
  apply Units.ext
  change (splitGram F).val * (cycleGL F).inv.transpose * (splitGram F).inv = (cycleGL F).inv
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [splitGram, cycleGL, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_three]


private theorem splitActor_root (a : F) :
    splitActor F (rootElement (show (0 : Fin 3) ≠ 2 by decide) a) =
      (rootElement (show (0 : Fin 3) ≠ 2 by decide) a)⁻¹ := by
  change QuotientGroup.mk (linearConjSL F (splitGram F)
    (graphSL F (SpecialLinearGroup.transvection (show (0 : Fin 3) ≠ 2 by decide) a))) = _
  rw [rootElement, ← QuotientGroup.mk_inv]
  congr 1
  apply SpecialLinearGroup.toGL_injective
  rw [linearConjSL_toGL, graphSL_toGL, map_inv]
  apply Units.ext
  change (splitGram F).val *
      ((SpecialLinearGroup.transvection (show (0 : Fin 3) ≠ 2 by decide) a)⁻¹).val.transpose *
      (splitGram F).inv =
    ((SpecialLinearGroup.transvection (show (0 : Fin 3) ≠ 2 by decide) a)⁻¹).val
  rw [SpecialLinearGroup.transvection_inv]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [splitGram, SpecialLinearGroup.transvection_coe, Matrix.single_apply,
      Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_three]

private theorem cycle_root_conj (i j : Fin 3) (hij : i ≠ j) (a : F) :
    cycle F * rootElement hij a * (cycle F)⁻¹ =
      rootElement (show i + 1 ≠ j + 1 from fun h => hij (add_right_cancel h)) a := by
  change QuotientGroup.mk (cycleSL F) * QuotientGroup.mk (SpecialLinearGroup.transvection hij a) *
    (QuotientGroup.mk (cycleSL F))⁻¹ = _
  rw [← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
  apply congrArg (QuotientGroup.mk : SL(3,F) → PSL(3,F))
  apply SpecialLinearGroup.toGL_injective
  rw [map_mul, map_mul, map_inv, cycleSL_toGL]
  apply Units.ext
  change (cycleGL F).val * (SpecialLinearGroup.transvection hij a).val * (cycleGL F).inv = _
  ext r s
  fin_cases i <;> fin_cases j
  all_goals try exact (hij rfl).elim
  all_goals fin_cases r <;> fin_cases s <;>
    simp [cycleGL, SpecialLinearGroup.transvection_coe, Matrix.single_apply,
      Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_three]

variable {F}
private theorem prime_roots_mem [Finite F] {p : ℕ} (hp : p.Prime) (hF : Nat.card F = p)
    (H : Subgroup PSL(3,F)) {i j : Fin 3} (hij : i ≠ j)
    (h : rootElement hij (1 : F) ∈ H) (a : F) : rootElement hij a ∈ H := by
  obtain ⟨n, rfl⟩ := exists_natCast hp hF a
  rw [rootElement_natCast]
  exact H.pow_mem h n

private theorem cycle_root_generate [Finite F] {p : ℕ} (hp : p.Prime) (hF : Nat.card F = p)
    (H : Subgroup PSL(3,F)) (hc : cycle F ∈ H)
    (hu : rootElement (show (0 : Fin 3) ≠ 2 by decide) (1 : F) ∈ H) : H = ⊤ := by
  have h10 : rootElement (show (1 : Fin 3) ≠ 0 by decide) (1 : F) ∈ H := by
    simpa only [cycle_root_conj] using H.mul_mem (H.mul_mem hc hu) (H.inv_mem hc)
  have h21 : rootElement (show (2 : Fin 3) ≠ 1 by decide) (1 : F) ∈ H := by
    simpa only [cycle_root_conj] using H.mul_mem (H.mul_mem hc h10) (H.inv_mem hc)
  have hcomm {i j k : Fin 3} (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k)
      (h1 : rootElement hij (1 : F) ∈ H) (h2 : rootElement hjk (1 : F) ∈ H) :
      rootElement hik (1 : F) ∈ H := by
    have he : rootElement hik (1 : F) =
        (rootElement hjk (1 : F))⁻¹ *
          (rootElement hij (1 : F) * rootElement hjk (1 : F)) *
            (rootElement hij (1 : F))⁻¹ := by
      rw [rootElement_chain hij hjk hik, one_mul]
      group
    rw [he]
    exact H.mul_mem (H.mul_mem (H.inv_mem h2) (H.mul_mem h1 h2)) (H.inv_mem h1)
  have h01 := hcomm (by decide : (0 : Fin 3) ≠ 2) (by decide : (2 : Fin 3) ≠ 1)
    (by decide) hu h21
  have h12 := hcomm (by decide : (1 : Fin 3) ≠ 0) (by decide : (0 : Fin 3) ≠ 2)
    (by decide) h10 hu
  have h20 := hcomm (by decide : (2 : Fin 3) ≠ 1) (by decide : (1 : Fin 3) ≠ 0)
    (by decide) h21 h10
  apply top_unique
  intro x _
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (center SL(3,F)) x
  apply Atlas.sl_elementary_induction (fun x : SL(3,F) => QuotientGroup.mk x ∈ H)
    _ (fun a b ha hb => by simpa only [QuotientGroup.mk_mul] using H.mul_mem ha hb) x
  intro i j hij a
  apply prime_roots_mem hp hF H hij _ a
  fin_cases i <;> fin_cases j
  all_goals try exact (hij rfl).elim
  all_goals assumption

end Matrix.PSL3.OddPrimeConjugateBounds.Graph

namespace Matrix.PSL3.OddPrimeConjugateBounds.Graph
variable {S : Type*} [Group S]

private theorem aut_conj (b : MulAut S) (x : S) :
    b * MulAut.conj x * b⁻¹ = MulAut.conj (b x) := by
  ext y
  simp [MulAut.mul_apply, MulAut.conj_apply]

private theorem cover_transport {a : MulAut S} {n : ℕ}
    (ha : MulAut.HasInnerConjugateCover a n) (b : MulAut S) :
    MulAut.HasInnerConjugateCover (b * a * b⁻¹) n := by
  obtain ⟨c, hc⟩ := ha
  let K := closure (Set.range fun i =>
    MulAut.conj (b (c i)) * (b * a * b⁻¹) * (MulAut.conj (b (c i)))⁻¹)
  have hmap : (closure (Set.range fun i =>
      MulAut.conj (c i) * a * (MulAut.conj (c i))⁻¹)).map
      (MulAut.conj b).toMonoidHom ≤ K := by
    rw [MonoidHom.map_closure]
    apply (closure_le K).mpr
    rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
    apply Subgroup.subset_closure
    refine ⟨i, ?_⟩
    change _ = b * (MulAut.conj (c i) * a * (MulAut.conj (c i))⁻¹) * b⁻¹
    dsimp only
    rw [← aut_conj b (c i)]
    group
  refine ⟨fun i => b (c i), ?_⟩
  rintro _ ⟨x, rfl⟩
  have hm := hmap (mem_map_of_mem (MulAut.conj b).toMonoidHom
    (hc (show MulAut.conj (b⁻¹ x) ∈ (MulAut.conj : S →* MulAut S).range from
      ⟨b⁻¹ x, rfl⟩)))
  change b * MulAut.conj (b⁻¹ x) * b⁻¹ ∈ K at hm
  simpa only [aut_conj, MulAut.apply_inv_self] using hm

private theorem inverted_conjugate_product (a : MulAut S) (ha : a ^ 2 = 1)
    (x : S) (hx : a x = x⁻¹) :
    (MulAut.conj x * a * (MulAut.conj x)⁻¹) * a = MulAut.conj (x ^ 2) := by
  have hai : a⁻¹ = a := inv_eq_of_mul_eq_one_right (by simpa only [pow_two] using ha)
  have he := aut_conj a x⁻¹
  simp only [map_inv, hx, inv_inv, hai] at he
  calc
    _ = MulAut.conj x * (a * (MulAut.conj x)⁻¹ * a) := by group
    _ = MulAut.conj x * MulAut.conj x := by rw [he]
    _ = MulAut.conj (x ^ 2) := by rw [pow_two, map_mul]
end Matrix.PSL3.OddPrimeConjugateBounds.Graph
namespace Matrix.PSL3.OddPrimeConjugateBounds.Graph
open Matrix.PSL3.OuterSolvable.OddPrimeCoverage
variable {F : Type*} [Field F] [Finite F]

private theorem two_ne_zero {p : ℕ} (ho : Odd p) (hF : Nat.card F = p) : (2 : F) ≠ 0 := by
  let := Fintype.ofFinite F
  intro hz
  have hc : ringChar F = 2 := CharP.ringChar_of_prime_eq_zero Nat.prime_two hz
  have he := FiniteField.even_card_iff_char_two.mp hc
  rw [← Nat.card_eq_fintype_card, hF] at he
  have hodd := Nat.odd_iff.mp ho
  omega

private theorem splitActor_three_cover {p : ℕ} (hp : p.Prime) (ho : Odd p) (hF : Nat.card F = p) :
    MulAut.HasInnerConjugateCover (splitActor F) 3 := by
  let u : PSL(3,F) := rootElement (show (0 : Fin 3) ≠ 2 by decide) ((2 : F)⁻¹)
  let c : Fin 3 → PSL(3,F) := ![1, cycle F, u]
  let H := closure (Set.range fun i =>
    MulAut.conj (c i) * splitActor F * (MulAut.conj (c i))⁻¹)
  have hgen (i : Fin 3) : MulAut.conj (c i) * splitActor F * (MulAut.conj (c i))⁻¹ ∈ H :=
    subset_closure ⟨i, rfl⟩
  have ha : splitActor F ∈ H := by simpa [c] using hgen 0
  have hcycle : MulAut.conj (cycle F ^ 2) ∈ H := by
    rw [← inverted_conjugate_product (splitActor F) (splitActor_sq F) (cycle F)
      (splitActor_cycle F)]
    exact H.mul_mem (by simpa [c] using hgen 1) ha
  have hu : MulAut.conj (u ^ 2) ∈ H := by
    rw [← inverted_conjugate_product (splitActor F) (splitActor_sq F) u
      (splitActor_root F ((2 : F)⁻¹))]
    exact H.mul_mem (by simpa [c] using hgen 2) ha
  have hcycle4 : (cycle F ^ 2) ^ 2 = cycle F := by
    rw [← pow_mul]
    change cycle F ^ (3 + 1) = cycle F
    rw [pow_add, cycle_cube, one_mul, pow_one]
  have hc : MulAut.conj (cycle F) ∈ H := by
    rw [← hcycle4, map_pow]
    exact H.pow_mem hcycle 2
  have hu2 : u ^ 2 = rootElement (show (0 : Fin 3) ≠ 2 by decide) (1 : F) := by
    dsimp only [u]
    rw [pow_two, ← rootElement_add, ← two_mul, mul_inv_cancel₀ (two_ne_zero ho hF)]
  rw [hu2] at hu
  have htop : H.comap (MulAut.conj : PSL(3,F) →* MulAut PSL(3,F)) = ⊤ :=
    cycle_root_generate hp hF _ hc hu
  refine ⟨c, ?_⟩
  rintro _ ⟨x, rfl⟩
  change x ∈ H.comap MulAut.conj
  rw [htop]
  exact mem_top x
end Matrix.PSL3.OddPrimeConjugateBounds.Graph
namespace Matrix.PSL3.OddPrimeConjugateBounds.Graph
variable {F : Type*} [Field F] [Invertible (2 : F)]
private theorem matrix_form_matrix (S : Matrix (Fin 3) (Fin 3) F) (hs : S.transpose = S) :
    S.toQuadraticForm'.toMatrix' = S := by
  have hB := Matrix.isSymm_toBilin'_iff_isSymm.mpr hs
  change LinearMap.toMatrix₂' F (QuadraticMap.associated S.toBilin'.toQuadraticMap) = S
  rw [QuadraticMap.associated_left_inverse F (fun x y => hB.eq x y)]
  exact LinearMap.toMatrix'_toLinearMap₂' S

private theorem polar_nondegenerate (Q : QuadraticForm F (Fin 3 → F)) (h2 : (2 : F) ≠ 0)
    (hQ : Q.toMatrix'.det ≠ 0) : Q.polarBilin.Nondegenerate := by
  have ha : Q.associated.Nondegenerate :=
    LinearMap.BilinForm.nondegenerate_toMatrix'_iff.mp
      (Matrix.nondegenerate_iff_det_ne_zero.mpr hQ)
  constructor
  · intro x hx
    apply ha.1
    intro y
    have h := congrArg (fun B => B x y) (QuadraticMap.two_nsmul_associated (S := F) Q)
    simp only [LinearMap.smul_apply, nsmul_eq_mul, hx] at h
    exact (mul_eq_zero.mp h).resolve_left h2
  · intro x hx
    apply ha.2
    intro y
    have h := congrArg (fun B => B y x) (QuadraticMap.two_nsmul_associated (S := F) Q)
    simp only [LinearMap.smul_apply, nsmul_eq_mul, hx] at h
    exact (mul_eq_zero.mp h).resolve_left h2

private theorem ternary_similarity [Finite F] (h2 : (2 : F) ≠ 0)
    (S : Matrix (Fin 3) (Fin 3) F) (hs : S.transpose = S) (hd : S.det ≠ 0) :
    ∃ (a : F) (C : GL (Fin 3) F), a ≠ 0 ∧
      C.val.transpose * S * C.val = a • !![0, 0, 1; 0, 1, 0; 1, 0, 0] := by
  let T : Matrix (Fin 3) (Fin 3) F := !![0, 0, 1; 0, 1, 0; 1, 0, 0]
  have ht : T.transpose = T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have htd : T.det = -1 := by simp [T, Matrix.det_fin_three]
  let a := -S.det
  have ha : a ≠ 0 := neg_ne_zero.mpr hd
  let Q := S.toQuadraticForm'
  let R := a • T.toQuadraticForm'
  have hQ : Q.toMatrix' = S := matrix_form_matrix S hs
  have hR : R.toMatrix' = a • T := by
    rw [QuadraticForm.toMatrix'_smul, matrix_form_matrix T ht]
  have hRd : R.discr' = S.det ^ 3 := by
    rw [QuadraticForm.discr', hR, Matrix.det_smul, htd]
    simp only [a, Fintype.card_fin, mul_neg, mul_one]
    ring
  have hQd : Q.discr' = S.det := congrArg Matrix.det hQ
  obtain ⟨e⟩ := (BenderSuzuki.MatrixGroups.HermitianForm.OddPrimeSylow.NormalizedOuter.Descent.SymmetricSimilarity.finite_nondegenerate_isometry_iff_discr_square h2 2 R Q
    (polar_nondegenerate R h2 (by change R.discr' ≠ 0; rw [hRd]; exact pow_ne_zero _ hd))
    (polar_nondegenerate Q h2 (by rwa [hQ]))).mpr (by
      rw [hRd, hQd]
      refine ⟨S.det, ?_⟩
      field_simp)
  let M := LinearMap.toMatrix' e.toLinearEquiv.toLinearMap
  have hM : M.det ≠ 0 := by
    rw [LinearMap.det_toMatrix']
    exact e.toLinearEquiv.isUnit_det'.ne_zero
  refine ⟨a, GeneralLinearGroup.mkOfDetNeZero M hM, ha, ?_⟩
  have he : Q.comp e.toLinearEquiv.toLinearMap = R := by
    ext v
    exact e.map_app v
  have h := congrArg QuadraticForm.toMatrix' he
  rw [QuadraticForm.toMatrix'_comp, hQ, hR] at h
  exact h


end Matrix.PSL3.OddPrimeConjugateBounds.Graph
namespace Matrix.PSL3.OddPrimeConjugateBounds.Graph
open Matrix.PSL3.OuterSolvable Matrix.PSL3.OddInvolutionFixed
variable {F : Type*} [Field F]

private theorem conjugate_graph (h g : GL (Fin 3) F) :
    linearConj F h * (linearConj F g * graph F) * (linearConj F h)⁻¹ =
      linearConj F (h * g * inverseTransposeGL h⁻¹) * graph F := by
  calc
    _ = (linearConj F h * linearConj F g) * (graph F * linearConj F h⁻¹) := by
      rw [map_inv]
      group
    _ = _ := by rw [graph_linearConj, ← mul_assoc, ← map_mul, ← map_mul]

private theorem graph_conjugate_split [Finite F] (h2 : (2 : F) ≠ 0)
    (g : GL (Fin 3) F) (hg : (linearConj F g * graph F) ^ 2 = 1) :
    ∃ b : MulAut PSL(3,F),
      b * (linearConj F g * graph F) * b⁻¹ = splitActor F := by
  let := invertibleOfNonzero h2
  obtain ⟨a, C, ha, hC⟩ := ternary_similarity h2 g.val (graph_involution_symmetric g hg)
    (GeneralLinearGroup.det_ne_zero g)
  let h : GL (Fin 3) F := (inverseTransposeGL C)⁻¹
  have he : h * g * inverseTransposeGL h⁻¹ =
      GeneralLinearGroup.scalar (Fin 3) (Units.mk0 a ha) * splitGram F := by
    have ht : inverseTransposeGL (inverseTransposeGL C) = C := Units.ext rfl
    dsimp only [h]
    rw [inv_inv, ht]
    apply Units.ext
    change C.val.transpose * g.val * C.val =
      Matrix.diagonal (fun _ : Fin 3 => a) * (splitGram F).val
    rw [← Matrix.smul_eq_diagonal_mul]
    exact hC
  refine ⟨linearConj F h, ?_⟩
  rw [conjugate_graph, he, map_mul, linearConj_scalar, one_mul]
  rfl

/-- Three actual projective inner conjugators cover the inner automorphism group
for every involutory linear-times-graph actor over an odd prime field. -/
theorem graph_three_cover [Finite F] {p : ℕ} (hp : p.Prime) (ho : Odd p)
    (hF : Nat.card F = p) (g : GL (Fin 3) F)
    (hg : (linearConj F g * graph F) ^ 2 = 1) :
    MulAut.HasInnerConjugateCover (linearConj F g * graph F) 3 := by
  obtain ⟨b, hb⟩ := graph_conjugate_split (two_ne_zero ho hF) g hg
  have he : linearConj F g * graph F = b⁻¹ * splitActor F * (b⁻¹)⁻¹ := by
    rw [← hb]
    group
  rw [he]
  exact cover_transport (splitActor_three_cover hp ho hF) b⁻¹

end Matrix.PSL3.OddPrimeConjugateBounds.Graph

namespace Matrix.PSL3.OddPrimeConjugateBounds
universe u

/-- The graph branch of the odd-prime PSL₃ three-conjugate generation bound. -/
theorem graph_three_bound : GraphThreeBound.{u} := by
  intro F _ _ _ _ p hp ho hF g _ hg
  exact Graph.graph_three_cover hp ho hF g hg

end Matrix.PSL3.OddPrimeConjugateBounds
