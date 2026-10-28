module

public import Theory.SpecificGroups.SymplecticFour.CentralCovers.OddPrime.LargeSections.OddNondefining.NonsplitTransfer
public import Theory.SpecificGroups.GL2.QuadraticRegularRepresentation

import Mathlib.Tactic.Group

/-!
# Corrected quadratic product tori in odd-prime symplectic four-space

The norm-one units of the actual quadratic extension embed faithfully in SL₂.
In a quadratic basis, regular multiplication has determinant equal to the
field norm. Frobenius inverts the norm-one units. Multiplying its matrix by
regular multiplication by a unit of inverse determinant corrects the
Frobenius matrix to determinant one, without changing that conjugation action.
Norm surjectivity supplies the correcting unit; no order-two assertion is needed.

The two SL₂ factors act on the actual orthogonal hyperbolic planes through
`ProductTori.pairHom`. The corrected matrix on the first plane inverts the
first torus factor and fixes the second. `NonsplitTransfer` then excludes
every odd prime dividing p+1 from every finite perfect central kernel.

This supplies the nonsplit-prime branch of the symplectic covering calculation
underlying Aschbacher–Smith I.1.1–4, printed pp.407–408, and GLS3 §6.1.
The regular representation refines the construction in
`GL2.QuadraticRegularRepresentation` by retaining its determinant formula.
-/

open Matrix Subgroup
namespace Theory.SpecificGroups.SymplecticFour.CentralCovers.OddPrime.LargeSections.OddNondefining.Nonsplit

private theorem exists_regular_norm
    (F K : Type*) [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]
    (hdim : Module.finrank F K = 2) (σ : K ≃ₐ[F] K) :
    ∃ (ρ : Kˣ →* GL (Fin 2) F) (w : GL (Fin 2) F),
      Function.Injective ρ ∧
      (∀ a, GeneralLinearGroup.det (ρ a) = Units.map (Algebra.norm F) a) ∧
      (∀ a, w * ρ a * w⁻¹ = ρ (Units.map σ.toRingHom.toMonoidHom a)) := by
  let b := Module.finBasisOfFinrankEq F K hdim
  let j : LinearMap.GeneralLinearGroup F K ≃* GL (Fin 2) F :=
    Units.mapEquiv (LinearMap.toMatrixAlgEquiv b).toRingEquiv.toMulEquiv
  let r : Kˣ →* LinearMap.GeneralLinearGroup F K :=
    Units.map (Algebra.lmul F K).toMonoidHom
  let v := LinearMap.GeneralLinearGroup.ofLinearEquiv σ.toLinearEquiv
  let ρ := j.toMonoidHom.comp r
  refine ⟨ρ, j v, j.injective.comp (Units.map_injective Algebra.lmul_injective), ?_, ?_⟩
  · intro a
    apply Units.ext
    change (LinearMap.toMatrix b b (Algebra.lmul F K (a : K))).det = Algebra.norm F (a : K)
    exact (Algebra.norm_eq_matrix_det b (a : K)).symm
  · intro a
    change j v * j (r a) * (j v)⁻¹ = j (r _)
    rw [← map_inv, ← map_mul, ← map_mul]
    apply congrArg j
    apply Units.ext
    ext x
    change σ ((a : K) * σ.symm x) = σ (a : K) * x
    rw [map_mul, σ.apply_symm_apply]

private theorem exists_norm_one_sl (p : ℕ) [Fact p.Prime] (hp : 3 < p) :
    ∃ (s : quadraticNormOne p →* SpecialLinearGroup (Fin 2) (ZMod p))
      (v : SpecialLinearGroup (Fin 2) (ZMod p)),
      Function.Injective s ∧ ∀ c, v * s c * v⁻¹ = s c⁻¹ := by
  let F := ZMod p
  let K := FiniteField.Extension F p 2
  -- Retain Frobenius's extension algebra, rather than the other ZMod algebra instance.
  let : Algebra F K := FiniteField.instAlgebraExtension F p 2
  let C := quadraticNormOne p
  let σ := FiniteField.Extension.frob F p 2
  obtain ⟨ρ, w₀, hi, hdet, hconj⟩ := exists_regular_norm F K
    (FiniteField.finrank_extension F p 2) σ
  have hconj' (a : Kˣ) : w₀ * ρ a * w₀⁻¹ = ρ (a ^ p) := by
    rw [hconj]
    apply congrArg ρ
    apply Units.ext
    change σ (a : K) = (a : K) ^ p
    simpa only [F, Nat.card_zmod] using
      (FiniteField.Extension.frob_apply F p 2 (x := (a : K)))
  have hexp : (Nat.card K - 1) / (Nat.card F - 1) = p + 1 := by
    change (Nat.card (FiniteField.Extension (ZMod p) p 2) - 1) /
      (Nat.card (ZMod p) - 1) = p + 1
    rw [FiniteField.natCard_extension, Nat.card_zmod,
      show p^2 - 1 = (p + 1) * (p - 1) by
        simpa using Nat.sq_sub_sq p 1]
    exact Nat.mul_div_cancel _ (by omega)
  have hnorm (c : C) : Units.map (Algebra.norm F) c.val = 1 := by
    apply Units.ext
    apply (algebraMap F K).injective
    change algebraMap F K (Algebra.norm F (c.val : K)) = algebraMap F K 1
    rw [FiniteField.algebraMap_norm_eq_pow, hexp, map_one]
    exact congrArg Units.val ((mem_rootsOfUnity _ _).mp c.property)
  obtain ⟨a, ha⟩ := FiniteField.unitsMap_norm_surjective F K
    (GeneralLinearGroup.det w₀)⁻¹
  let w := ρ a * w₀
  have hwd : GeneralLinearGroup.det w = 1 := by
    change GeneralLinearGroup.det (ρ a * w₀) = 1
    rw [map_mul, hdet, ha, inv_mul_cancel]
  let r : C →* GL (Fin 2) F := ρ.comp (rootsOfUnity (p+1) K).subtype
  have hd (c : C) : GeneralLinearGroup.det (r c) = 1 := (hdet c.val).trans (hnorm c)
  let s : C →* SpecialLinearGroup (Fin 2) F := {
    toFun c := ⟨(r c).val, congrArg Units.val (hd c)⟩
    map_one' := Subtype.ext (congrArg Units.val r.map_one)
    map_mul' c d := Subtype.ext (congrArg Units.val (r.map_mul c d)) }
  let v : SpecialLinearGroup (Fin 2) F := ⟨w.val, congrArg Units.val hwd⟩
  have hs : Function.Injective s := by
    intro c d h
    apply Subtype.ext
    exact hi (Units.ext (congrArg Subtype.val h))
  refine ⟨s, v, hs, ?_⟩
  intro c
  apply SpecialLinearGroup.toGL_injective
  have hvGL : SpecialLinearGroup.toGL v = w := Units.ext rfl
  have hsGL (d : C) : SpecialLinearGroup.toGL (s d) = r d := Units.ext rfl
  simp only [map_mul, map_inv, hvGL, hsGL]
  change (ρ a * w₀) * ρ c.val * (ρ a * w₀)⁻¹ = (ρ c.val)⁻¹
  rw [← ρ.map_inv]
  have hc : c.val ^ p = c.val⁻¹ := by
    apply eq_inv_of_mul_eq_one_left
    rw [← pow_succ]
    exact (mem_rootsOfUnity _ _).mp c.property
  calc
    (ρ a * w₀) * ρ c.val * (ρ a * w₀)⁻¹ =
        ρ a * (w₀ * ρ c.val * w₀⁻¹) * (ρ a)⁻¹ := by group
    _ = ρ a * ρ (c.val⁻¹) * (ρ a)⁻¹ := by rw [hconj', hc]
    _ = ρ (c.val⁻¹) := by
      rw [← map_inv, ← map_mul, ← map_mul]
      congr 1
      simp [mul_comm]

/-- The two actual norm-one factors with independent inversion of the first. -/
public theorem exists_nonsplit_product (p : ℕ) [Fact p.Prime] (hp : 3 < p) :
    ∃ (ι : quadraticNormOne p × quadraticNormOne p →* Sp (ZMod p))
      (w : Sp (ZMod p)), Function.Injective ι ∧
      (∀ c, w * ι (c,1) * w⁻¹ = ι (c⁻¹,1)) ∧
      (∀ c, w * ι (1,c) * w⁻¹ = ι (1,c)) := by
  obtain ⟨s, v, hs, hv⟩ := exists_norm_one_sl p hp
  let ι := ProductTori.pairHom.comp (s.prodMap s)
  refine ⟨ι, ProductTori.pairHom (v,1),
    ProductTori.pairHom_injective.comp (Prod.map_injective.mpr ⟨hs, hs⟩), ?_, ?_⟩
  · intro c
    change ProductTori.pairHom (v,1) * ProductTori.pairHom (s c,s 1) *
      (ProductTori.pairHom (v,1))⁻¹ = ProductTori.pairHom (s c⁻¹,s 1)
    rw [← map_inv, ← map_mul, ← map_mul]
    apply congrArg ProductTori.pairHom
    apply Prod.ext
    · exact hv c
    · simp
  · intro c
    change ProductTori.pairHom (v,1) * ProductTori.pairHom (s 1,s c) *
      (ProductTori.pairHom (v,1))⁻¹ = ProductTori.pairHom (s 1,s c)
    rw [← map_inv, ← map_mul, ← map_mul]
    apply congrArg ProductTori.pairHom
    apply Prod.ext <;> simp

/-- Every odd prime dividing p+1 is absent from a perfect central kernel. -/
public theorem not_dvd_card_kernel_of_dvd_add_one
    {p r : ℕ} [Fact p.Prime] [Fact r.Prime]
    (hp : 3 < p) (hr2 : r ≠ 2) (hd : r ∣ p + 1)
    {E : Type*} [Group E] [Finite E]
    (f : PerfectCentralCovering.Cover E (Sp (ZMod p))) :
    ¬ r ∣ Nat.card f.toMonoidHom.ker := by
  obtain ⟨ι, w, hi, hinv, hfix⟩ := exists_nonsplit_product p hp
  exact NonsplitTransfer.not_dvd_card_kernel_of_product hr2
    (by simpa only [Nat.card_zmod] using hd) ι hi
    (by simpa only [Nat.card_zmod] using card_quadraticNormOne p) w hinv hfix f

end Theory.SpecificGroups.SymplecticFour.CentralCovers.OddPrime.LargeSections.OddNondefining.Nonsplit
