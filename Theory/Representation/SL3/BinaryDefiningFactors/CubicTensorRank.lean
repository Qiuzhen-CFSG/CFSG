module
public import Theory.Representation.SL3.BinaryDefiningFactors
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.LinearAlgebra.TensorProduct.Basis
public import Mathlib.LinearAlgebra.Dual.Basis

/-!
# Cubic displacement on the natural tensor words

A natural eigenbasis with weights 1, ω, ω² gives inverse weights on the
actual contragredient basis. Tensoring two such bases, including the final
scalar factor of `wordRep`, gives three fixed and six moved coordinates
for both the natural and dual two-letter words.

The Chapter H PSL₃(4) displacement consumer supplies these eigenbases for
an actual projective cubic. This is the nine-dimensional case in
Aschbacher–Smith H.4.7, printed pp.382–383 of refs/quasithin.pdf.
-/

public noncomputable section
open scoped MatrixGroups TensorProduct
open Representation
namespace Representation.SL3.BinaryDefiningFactors
set_option backward.isDefEq.respectTransparency false
variable {F K : Type*} [Field F] [Field K] [CharP K 2]

omit [CharP K 2] in
private theorem eigen_rank {I V : Type*} [Fintype I] [AddCommGroup V] [Module K V]
    (b : Module.Basis I K V) (f : Module.End K V) (ω : K) (hω : orderOf ω = 3)
    (e : I → ℕ) (h : ∀ i, f (b i) = ω ^ e i • b i) :
    Module.finrank K (LinearMap.range (f - 1)) =
      Fintype.card {i : I // e i % 3 ≠ 0} := by
  classical
  have hmat : LinearMap.toMatrix b b (f - 1) =
      Matrix.diagonal (fun i => ω ^ e i - 1) := by
    ext i j
    simp only [LinearMap.toMatrix_apply, LinearMap.sub_apply, Module.End.one_apply,
      h, map_sub, map_smul, Module.Basis.repr_self, Finsupp.sub_apply,
      Finsupp.smul_apply, smul_eq_mul, Finsupp.single_apply, Matrix.diagonal_apply]
    split_ifs <;> simp_all
  have hr := Matrix.rank_eq_finrank_range_toLin (LinearMap.toMatrix b b (f - 1)) b b
  rw [Matrix.toLin_toMatrix, hmat, Matrix.rank_diagonal] at hr
  rw [← hr]
  apply Fintype.card_congr
  exact Equiv.subtypeEquivRight (fun i => by
    rw [sub_ne_zero, ne_eq, ← orderOf_dvd_iff_pow_eq_one, hω, Nat.dvd_iff_mod_eq_zero])

private theorem pair_rank {I J : Type*} [Fintype I] [Fintype J]
    (ι : F →+* K) (g : SL(3,F)) (ω : K) (hω : orderOf ω = 3)
    (a b : Factor) (b0 : Module.Basis I K (Space K a))
    (b1 : Module.Basis J K (Space K b)) (e0 : I → ℕ) (e1 : J → ℕ)
    (h0 : ∀ i, factorRep ι a g (b0 i) = ω ^ e0 i • b0 i)
    (h1 : ∀ j, factorRep ((frobenius K 2).comp ι) b g (b1 j) = ω ^ e1 j • b1 j) :
    Module.finrank K (LinearMap.range (wordRep ι [a,b] g - 1)) =
      Fintype.card {i : I × J // (e0 i.1 + e1 i.2) % 3 ≠ 0} := by
  let B := b0.tensorProduct (b1.tensorProduct (Module.Basis.singleton Unit K))
  have hB : ∀ i : I × (J × Unit), wordRep ι [a,b] g (B i) =
      ω ^ (e0 i.1 + e1 i.2.1) • B i := by
    rintro ⟨i,j,u⟩
    dsimp only [B]
    simp only [Module.Basis.tensorProduct_apply]
    change TensorProduct.map (factorRep ι a g)
      (TensorProduct.map (factorRep ((frobenius K 2).comp ι) b g)
        (1 : Module.End K K))
      (b0 i ⊗ₜ[K] (b1 j ⊗ₜ[K] (Module.Basis.singleton Unit K) u)) = _
    simp only [TensorProduct.map_tmul, h0, h1, Module.End.one_apply,
      pow_add, ← TensorProduct.smul_tmul', ← TensorProduct.tmul_smul, smul_smul]
  refine (eigen_rank B _ ω hω _ hB).trans ?_
  exact Fintype.card_congr
    ((Equiv.prodCongr (Equiv.refl I) (Equiv.prodUnique J Unit)).subtypeEquiv
      (fun _ => Iff.rfl))

omit [CharP K 2] in
private theorem dual_eigenbasis (ι : F →+* K) (g : SL(3,F)) (ω : K)
    (hω : orderOf ω = 3) (b : Module.Basis (Fin 3) K (Fin 3 → K))
    (hb : ∀ i, natural ι g (b i) = ω ^ i.val • b i) :
    ∀ i, factorRep ι .dual g (b.dualBasis i) = ω ^ (2*i.val) • b.dualBasis i := by
  have hω3 : ω ^ 3 = 1 := by simpa only [hω] using pow_orderOf_eq_one ω
  have hω0 : ω ≠ 0 := by intro h; simp [h] at hω3
  have hi (j : Fin 3) : natural ι g⁻¹ (b j) = (ω ^ j.val)⁻¹ • b j := by
    have hh : natural ι g⁻¹ (natural ι g (b j)) = b j := by
      change (natural ι g⁻¹ * natural ι g) (b j) = b j
      rw [← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
    rw [hb, map_smul] at hh
    calc
      natural ι g⁻¹ (b j) = (ω ^ j.val)⁻¹ •
          (ω ^ j.val • natural ι g⁻¹ (b j)) := by
        rw [← mul_smul, inv_mul_cancel₀ (pow_ne_zero _ hω0), one_smul]
      _ = _ := by rw [hh]
  have hinv : ω⁻¹ = ω ^ 2 := by
    apply inv_eq_of_mul_eq_one_right
    simpa only [← pow_succ'] using hω3
  intro i
  apply b.ext
  intro j
  change b.dualBasis i (natural ι g⁻¹ (b j)) =
    (ω ^ (2*i.val) • b.dualBasis i) (b j)
  rw [hi, map_smul, LinearMap.smul_apply, ← inv_pow, hinv, ← pow_mul]
  simp only [Module.Basis.dualBasis_apply_self, smul_eq_mul]
  split_ifs with h
  · subst j; rfl
  · simp

/-- Both literal nine-dimensional words have cubic displacement six.
The two eigenbases use the original embedding and its actual Frobenius twist. -/
theorem natural_pair_cubic_ranks_of_eigenbases
    (ι : F →+* K) (g : SL(3,F)) (ω : K) (hω : orderOf ω = 3)
    (b c : Module.Basis (Fin 3) K (Fin 3 → K))
    (hb : ∀ i, natural ι g (b i) = ω ^ i.val • b i)
    (hc : ∀ i, natural ((frobenius K 2).comp ι) g (c i) = ω ^ i.val • c i) :
    Module.finrank K (LinearMap.range (wordRep ι [.natural,.natural] g - 1)) = 6 ∧
    Module.finrank K (LinearMap.range (wordRep ι [.dual,.dual] g - 1)) = 6 := by
  constructor
  · rw [pair_rank ι g ω hω .natural .natural b c (fun i => i.val) (fun i => i.val) hb hc]
    decide
  · rw [pair_rank ι g ω hω .dual .dual b.dualBasis c.dualBasis
      (fun i => 2*i.val) (fun i => 2*i.val)
      (dual_eigenbasis ι g ω hω b hb)
      (dual_eigenbasis ((frobenius K 2).comp ι) g ω hω c hc)]
    decide

end Representation.SL3.BinaryDefiningFactors
