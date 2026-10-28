module

public import Theory.SpecificGroups.PSL3.OuterSolvable.OddPrimeCoverage.RootOrientation.Signs

/-!
# Diagonal involutions from an opposite unipotent pair

The two Borel normalizers intersect in the diagonal projective torus.
For a projective involution in that torus, the square of a diagonal lift
is central and has cube one. Cubing the lift therefore gives an actual
involution with the same projective image. Its diagonal entries are signs,
and determinant one leaves exactly the three nonidentity sign matrices.
Thus preserving the opposite pair permutes those three matrices.

The normalizer calculation uses the coprime scalar kernel and applies
also in characteristic three. No lift of the given automorphism is used.
Source: GLS3, Theorem 2.5.12(a) and §2.7,
`refs/KGroup/GLS3/chapter2.tex`, lines 1111–1115.
-/

public section

open scoped MatrixGroups
open Matrix Matrix.PSL3.LinearThree
namespace Matrix.PSL3.OuterSolvable.OddPrimeCoverage
variable {F : Type*} [Field F] [Finite F]

private theorem diagonal_of_borel_pair (x : PSL(3,F))
    (hu : x ∈ borel F) (hl : x ∈ (borel F).map (graph F).toMonoidHom) :
    ∃ g : SL(3,F), projection F g = x ∧ g.val = Matrix.diagonal (fun i => g.val i i) := by
  obtain ⟨g, rfl⟩ := projection_surjective F x
  have hu' : g ∈ borelSL F := by
    rw [← borel_comap F]
    exact hu
  have hgg (y : PSL(3,F)) : graph F (graph F y) = y :=
    congrArg (fun a : MulAut PSL(3,F) => a y) (graph_sq F)
  have hl' : graph F (projection F g) ∈ borel F := by
    obtain ⟨y, hy, he⟩ := hl
    rw [← he]
    change graph F (graph F y) ∈ borel F
    rwa [hgg]
  have ht : (SpecialLinearGroup.transpose g)⁻¹ ∈ borelSL F := by
    rw [← borel_comap F]
    exact hl'
  have ht' : SpecialLinearGroup.transpose g ∈ borelSL F := by
    simpa only [inv_inv] using (borelSL F).inv_mem ht
  obtain ⟨h10,h20,h21⟩ := (mem_borelSL_iff F g).mp hu'
  obtain ⟨h01,h02,h12⟩ := (mem_borelSL_iff F _).mp ht'
  change g.val 0 1 = 0 at h01
  change g.val 0 2 = 0 at h02
  change g.val 1 2 = 0 at h12
  refine ⟨g, rfl, ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;> simp [h10,h20,h21,h01,h02,h12]

omit [Finite F] in
private theorem central_cube (g : SL(3,F)) (hg : g ∈ Subgroup.center SL(3,F)) :
    g ^ 3 = 1 := by
  obtain ⟨r, hr, he⟩ := SpecialLinearGroup.mem_center_iff.mp hg
  have hr' : r ^ 3 = 1 := hr
  apply Subtype.ext
  change g.val ^ 3 = (1 : Matrix (Fin 3) (Fin 3) F)
  rw [← he]
  change (Matrix.diagonal (fun _ : Fin 3 => r)) ^ 3 = _
  simp only [Matrix.diagonal_pow]
  congr 1
  funext i
  exact hr'

omit [Finite F] in
private theorem diagonal_involution (g : SL(3,F))
    (hd : g.val = Matrix.diagonal (fun i => g.val i i)) (hs : g ^ 2 = 1) :
    g = 1 ∨ ∃ k, g = signSL k := by
  have hsq (i : Fin 3) : g.val i i ^ 2 = 1 := by
    have hm := congrArg (fun a : SL(3,F) => a.val) hs
    change g.val ^ 2 = (1 : Matrix (Fin 3) (Fin 3) F) at hm
    rw [hd, Matrix.diagonal_pow] at hm
    have h := congrArg (fun m : Matrix (Fin 3) (Fin 3) F => m i i) hm
    simpa only [Matrix.diagonal_apply_eq, Pi.pow_apply, Matrix.one_apply_eq] using h
  have he (i : Fin 3) : g.val i i = 1 ∨ g.val i i = -1 := by
    exact (sq_eq_sq_iff_eq_or_eq_neg).mp (by simpa using hsq i)
  have hdet := g.property
  rw [hd, Matrix.det_diagonal, Fin.prod_univ_three] at hdet
  rcases he 0 with h0 | h0 <;> rcases he 1 with h1 | h1 <;> rcases he 2 with h2 | h2
  all_goals simp only [h0,h1,h2,mul_one,mul_neg,neg_neg] at hdet
  · left; apply Subtype.ext; rw [hd]; ext i j
    fin_cases i <;> fin_cases j <;> simp [h0,h1,h2]
  · left; apply Subtype.ext; rw [hd]; ext i j
    fin_cases i <;> fin_cases j <;> simp [h0,h1,h2,hdet]
  · left; apply Subtype.ext; rw [hd]; ext i j
    fin_cases i <;> fin_cases j <;> simp [h0,h1,h2,hdet]
  · right; refine ⟨0, Subtype.ext ?_⟩; rw [hd]; ext i j
    fin_cases i <;> fin_cases j <;> simp [h0,h1,h2,signSL]
  · left; apply Subtype.ext; rw [hd]; ext i j
    fin_cases i <;> fin_cases j <;> simp [h0,h1,h2,hdet]
  · right; refine ⟨1, Subtype.ext ?_⟩; rw [hd]; ext i j
    fin_cases i <;> fin_cases j <;> simp [h0,h1,h2,signSL]
  · right; refine ⟨2, Subtype.ext ?_⟩; rw [hd]; ext i j
    fin_cases i <;> fin_cases j <;> simp [h0,h1,h2,signSL]
  · left; apply Subtype.ext; rw [hd]; ext i j
    fin_cases i <;> fin_cases j <;> simp [h0,h1,h2,hdet]

/-- The nonidentity involutions in the diagonal projective torus are exactly
its three coordinate sign matrices. Cubing a lift removes the scalar kernel. -/
theorem exists_signElement_of_borel_pair (x : PSL(3,F))
    (hu : x ∈ borel F) (hl : x ∈ (borel F).map (graph F).toMonoidHom)
    (hs : x ^ 2 = 1) (hne : x ≠ 1) : ∃ k, x = signElement k := by
  obtain ⟨g, rfl, hd⟩ := diagonal_of_borel_pair x hu hl
  have hc : g ^ 2 ∈ Subgroup.center SL(3,F) := by
    rw [← projection_ker F, MonoidHom.mem_ker, map_pow]
    exact hs
  have hs' : (g ^ 3) ^ 2 = 1 := by
    rw [← pow_mul, Nat.mul_comm 3 2, pow_mul]
    exact central_cube _ hc
  have hd' : (g ^ 3).val = Matrix.diagonal (fun i => (g ^ 3).val i i) := by
    have he : (g ^ 3).val = Matrix.diagonal ((fun i => g.val i i) ^ 3) := by
      change g.val ^ 3 = _
      rw [hd, Matrix.diagonal_pow]
      simp only [Matrix.diagonal_apply_eq]
    rw [he]
    simp only [Matrix.diagonal_apply_eq]
  have hproj : projection F (g ^ 3) = projection F g := by
    rw [map_pow, pow_succ, hs, one_mul]
  rcases diagonal_involution (g ^ 3) hd' hs' with he | ⟨k,hk⟩
  · exact (hne (hproj.symm.trans (by rw [he, map_one]))).elim
  · exact ⟨k, hproj.symm.trans (congrArg (projection F) hk)⟩

/-- Preserving an opposite unipotent pair permutes the three diagonal
involutions, using the Borel normalizer formulas valid also at p = 3. -/
theorem exists_sign_permutation {p : ℕ} (hp : p.Prime) (hF : Nat.card F = p)
    (h2 : (2 : F) ≠ 0) (α : MulAut PSL(3,F)) (hα : PreservesUnipotentPair F α) :
    ∃ σ : Equiv.Perm (Fin 3), ∀ k, α (signElement k) = signElement (σ k) := by
  have hB : (borel F).map α.toMonoidHom = borel F := by
    rw [← normalizer_upperUnipotent F hp hF, Subgroup.map_equiv_normalizer_eq, hα.1]
  have hC : ((borel F).map (graph F).toMonoidHom).map α.toMonoidHom =
      (borel F).map (graph F).toMonoidHom := by
    rw [← normalizer_lowerUnipotent F hp hF, Subgroup.map_equiv_normalizer_eq, hα.2]
  have hb (k : Fin 3) : signElement (F := F) k ∈ borel F := by
    apply Subgroup.mem_map_of_mem (projection F)
    rw [mem_borelSL_iff]
    simp [signSL]
  have hc (k : Fin 3) : signElement (F := F) k ∈ (borel F).map (graph F).toMonoidHom :=
    ⟨signElement k, hb k, graph_signElement k⟩
  have hex (k : Fin 3) : ∃ l, α (signElement k) = signElement l := by
    apply exists_signElement_of_borel_pair
    · rw [← hB]; exact Subgroup.mem_map_of_mem _ (hb k)
    · rw [← hC]; exact Subgroup.mem_map_of_mem _ (hc k)
    · rw [← map_pow, signElement_sq, map_one]
    · exact fun he => signElement_ne_one h2 k (α.injective (he.trans (map_one α).symm))
  choose f hf using hex
  have hinj : Function.Injective f := by
    intro k l h
    apply signElement_injective h2
    apply α.injective
    rw [hf, hf, h]
  exact ⟨Equiv.ofBijective f ((Finite.injective_iff_bijective).mp hinj), hf⟩

end Matrix.PSL3.OuterSolvable.OddPrimeCoverage
