module
public import Theory.Representation.HermitianTensorThree.ParabolicTorus.Geometry
public import Theory.Representation.HermitianTensorThree.UnipotentRadicals.LargeActors
import all Theory.Representation.HermitianTensorThree.UnipotentRadicals
import all Theory.Representation.HermitianTensorThree.UnipotentRadicals.LargeActors
/-!
# Odd normalizers of large Hermitian elementary actors

Conjugate the actual inner elementary actor into the upper-unitriangular
SL₃ image. Its rank exceeds the binary dimension of the extension field,
so its common natural fixed space is the standard point or plane. A GL₃
congruence normalizing its Hermitian image preserves this fixed space:
trace one removes the scalar ambiguity in lifting conjugation. The odd
parabolic exponent then applies to the same operator and the same cover
conjugation, without a separate preserved-parabolic assumption.

The Chapter 8 HermitianSourceNormalizedTorus consumer obtains this large
actor from the original selected core and r-bound. This calculation includes
n = 1, but does not assert the ambient field-four exclusion.

Source: Aschbacher–Smith, 8.2.3, printed pp.715–716, using the H.4.2
Hermitian action (1 March 2004 manuscript, refs/quasithin.pdf).
-/

public noncomputable section
open Subgroup Matrix Representation Representation.BinaryOffender
open Representation.HermitianTensorThree Representation.HermitianTensorThree.ImageOuter
open Matrix.PSL3Even.UnipotentGeometry
open scoped MatrixGroups
set_option backward.isDefEq.respectTransparency false
namespace Representation.HermitianTensorThree.ParabolicTorus
variable (n : ℕ) [NeZero n]

omit [NeZero n] in
private theorem trace_unipotent (b : U (E n)) :
    Matrix.trace (matrix (E n) b) = 1 := by
  simp [matrix,Matrix.trace,Fin.sum_univ_three,CharTwo.add_self_eq_zero]

private theorem congruence_conjugate_unipotent
    (g : Matrix.GeneralLinearGroup (Fin 3) (E n)) (a b : U (E n))
    (h : binaryCongruence n g * UnipotentRadicals.unipotentHom n a *
      (binaryCongruence n g)⁻¹ = UnipotentRadicals.unipotentHom n b) :
    g.val * matrix (E n) a * g.inv = matrix (E n) b := by
  let u := Matrix.SpecialLinearGroup.toGL (specialLinear (E n) a)
  let v := Matrix.SpecialLinearGroup.toGL (specialLinear (E n) b)
  have he : binaryCongruence n (g*u*g⁻¹) = binaryCongruence n v := by
    rw [map_mul,map_mul,map_inv]
    exact h
  have hk := (binaryCongruence n).eq_iff.mp he
  obtain ⟨c,hc,_⟩ := (mem_binaryCongruence_ker_iff n _).mp hk
  have hm : (g*u*g⁻¹).val = c • v.val := by
    calc
      (g*u*g⁻¹).val = (v * (v⁻¹ * (g*u*g⁻¹))).val := by simp only [mul_inv_cancel_left]
      _ = v.val * Matrix.scalar (Fin 3) c := by rw [Units.val_mul,hc]
      _ = c • v.val := by ext i j; simp [Matrix.scalar,Matrix.mul_diagonal,mul_comm]
  have ht : Matrix.trace (g*u*g⁻¹).val = 1 := by
    change Matrix.trace (g.val*u.val*g.inv) = 1
    rw [Matrix.trace_mul_cycle,g.inv_val,one_mul]
    exact trace_unipotent n a
  rw [hm,Matrix.trace_smul,show Matrix.trace v.val = 1 from trace_unipotent n b,
    smul_eq_mul,mul_one] at ht
  rw [ht,one_smul] at hm
  exact hm

private theorem fixed_vector_image (B : Subgroup (U (E n)))
    (g : Matrix.GeneralLinearGroup (Fin 3) (E n))
    (hg : binaryCongruence n g ∈ normalizer
      (B.map (UnipotentRadicals.unipotentHom n) : Set (BinaryAut n)))
    (v : Fin 3 → E n) (hv : ∀ b ∈ B, (matrix (E n) b).mulVec v = v) :
    ∀ b ∈ B, (matrix (E n) b).mulVec (g.val.mulVec v) = g.val.mulVec v := by
  intro b hb
  have hmem := (mem_normalizer_iff''.mp hg (UnipotentRadicals.unipotentHom n b)).mp
    (mem_map_of_mem _ hb)
  obtain ⟨a,ha,he⟩ := hmem
  have hm := congruence_conjugate_unipotent n g⁻¹ b a (by
    simpa only [map_inv,inv_inv] using he.symm)
  have hmul : matrix (E n) b * g.val = g.val * matrix (E n) a := by
    calc
      _ = g.val * (g.inv * matrix (E n) b * g.val) := by
        rw [←mul_assoc,←mul_assoc,g.val_inv,one_mul]
      _ = _ := by rw [←hm]; rfl
  rw [Matrix.mulVec_mulVec,hmul,←Matrix.mulVec_mulVec,hv a ha]

private theorem unipotent_normalizer_shape (B : Subgroup (U (E n)))
    [IsElementaryAbelian 2 B] (hr : 2*n < rank B)
    (g : Matrix.GeneralLinearGroup (Fin 3) (E n))
    (hg : binaryCongruence n g ∈ normalizer
      (B.map (UnipotentRadicals.unipotentHom n) : Set (BinaryAut n))) :
    OddExponent.NaturalParabolicShape n g := by
  rcases elementary_le_plane (E n) B with hB | hB
  · have hv : ∀ b ∈ B, (matrix (E n) b).mulVec (![1,0,0] : Fin 3 → E n) = ![1,0,0] := by
      intro b hb
      ext i
      fin_cases i <;> simp [matrix,Matrix.mulVec,dotProduct,Fin.sum_univ_three]
    have hf := fixed_vector_image n B g hg _ hv
    have rel (b : B) : b.val.x * g.val 1 0 + b.val.c * g.val 2 0 = 0 := by
      have he := congrFun (hf b.val b.property) 0
      have hy := (mem_V₁ _ _).mp (hB b.property)
      simp [matrix,Matrix.mulVec,dotProduct,Fin.sum_univ_three,hy] at he
      linear_combination he
    exact Or.inl (LargeActors.independent_coordinates
      (fun b : B => b.val.x) (fun b : B => b.val.c)
      (LargeActors.point_coordinates_injective n B hB)
      (LargeActors.card_gt_field n B hr) _ _ rel)
  · have hv (j : Fin 3) (hj : j = 0 ∨ j = 1) :
        ∀ b ∈ B, (matrix (E n) b).mulVec (Pi.single j 1) = Pi.single j 1 := by
      intro b hb
      have hx := (mem_V₂ _ _).mp (hB hb)
      rcases hj with rfl | rfl <;> ext i <;> fin_cases i <;>
        simp [matrix,Matrix.mulVec,dotProduct,Fin.sum_univ_three,hx]
    have col (j : Fin 3) (hj : j = 0 ∨ j = 1) : g.val 2 j = 0 := by
      have hf := fixed_vector_image n B g hg _ (hv j hj)
      have rel (b : B) : b.val.c * g.val 2 j + sigma n b.val.y * 0 = 0 := by
        have he := congrFun (hf b.val b.property) 0
        have hx := (mem_V₂ _ _).mp (hB b.property)
        simp [matrix,Matrix.mulVec,dotProduct,Fin.sum_univ_three,hx,-mul_eq_zero] at he ⊢
        rcases hj with rfl | rfl <;> simp [-mul_eq_zero] at he ⊢ <;> linear_combination he
      exact (LargeActors.independent_coordinates
        (fun b : B => b.val.c) (fun b : B => sigma n b.val.y)
        (LargeActors.plane_coordinates_injective n B hB)
        (LargeActors.card_gt_field n B hr) _ _ rel).1
    exact Or.inr ⟨col 0 (Or.inl rfl),col 1 (Or.inr rfl)⟩

/-- A large inner elementary actor forces every odd fixed-field-linear
normalizer to have the natural parabolic exponent. -/
theorem odd_order_dvd_of_large_inner_actor
    (A : Subgroup (BinaryAut n)) [IsElementaryAbelian 2 A]
    (hA : A ≤ binaryImage n) (hr : 2*n < rank A)
    (x : BinaryAut n) (hx : x ∈ binaryNormalizer n) (ho : Odd (orderOf x))
    (hl : IsFixedFieldLinear n x) (hn : x ∈ normalizer (A : Set (BinaryAut n))) :
    orderOf x ∣ 2^(4*n)-1 := by
  obtain ⟨g,hg⟩ := OddExponent.mem_congruenceImage_of_odd_of_isFixedFieldLinear n x hx ho hl
  obtain ⟨c,hc⟩ := UnipotentRadicals.two_subgroup_conjugate_le_unipotent n A
    (IsElementaryAbelian.isPGroup 2 A) hA
  let f := (MulAut.conj (binaryActionHom n c)).toMonoidHom
  let B := (A.map f).comap (UnipotentRadicals.unipotentHom n)
  let : IsElementaryAbelian 2 (A.map f) := IsElementaryAbelian.map f
  have hi : Function.Injective ((UnipotentRadicals.unipotentHom n).subgroupComap (A.map f)) :=
    fun a b h => Subtype.ext (UnipotentRadicals.unipotentHom_injective n (congrArg Subtype.val h))
  let : IsElementaryAbelian 2 B := IsElementaryAbelian.of_injective _ hi
  have hm : B.map (UnipotentRadicals.unipotentHom n) = A.map f := map_comap_eq_self hc
  have hrB : 2*n < rank B := by
    rw [←rank_map_injective (UnipotentRadicals.unipotentHom n)
      (UnipotentRadicals.unipotentHom_injective n),hm,rank_map_conj]
    exact hr
  let d := Matrix.SpecialLinearGroup.toGL c
  let g' := d*g*d⁻¹
  have he : binaryCongruence n g' = f x := by
    dsimp [g',d,f]
    rw [map_mul,map_mul,map_inv,binaryCongruence_toGL,hg]
  have hnormal : binaryCongruence n g' ∈ normalizer
      (B.map (UnipotentRadicals.unipotentHom n) : Set (BinaryAut n)) := by
    rw [hm,he]
    exact A.le_normalizer_map f (mem_map_of_mem f hn)
  have hord : orderOf (binaryCongruence n g') = orderOf x := by
    rw [he]
    exact (MulAut.conj (binaryActionHom n c)).orderOf_eq x
  have hodd := OddExponent.odd_orderOf_of_odd_binaryCongruence n g' (hord ▸ ho)
  have hd := (orderOf_map_dvd (binaryCongruence n) g').trans
    (naturalParabolicOddExponent n g' hodd (unipotent_normalizer_shape n B hrB g' hnormal))
  rwa [hord] at hd
end Representation.HermitianTensorThree.ParabolicTorus
