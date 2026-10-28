module
public import Theory.SpecificGroups.SymplecticFour.InvolutionCentralizers.NormalForms
public import Theory.LinearAlgebra.Matrix.BinaryPairTrace
/-!
# Native symplectic involutions have a pair beyond two-groups and S₃

The genuine involution normal forms are a long root, a short root, and
the mixed c₂ representative. Opposite root conjugation gives each pair
product an invariant two-dimensional block. Choose its parameter outside
{0,1}; the checked binary trace identities exclude all two-power orders
and sixth power one. Transport by the original normal-form conjugator
and apply these power obstructions in the literal generated pair subgroup.
This includes every finite characteristic-two field of order greater than
two, including order four, and all three involution types.
Source: Aschbacher–Smith 13.5.21, printed p.924.
-/
public section
open Matrix Subgroup
open scoped CharTwo
set_option linter.unusedSimpArgs false
namespace Theory.SpecificGroups.SymplecticFour.InvolutionPairs
open Representation.OneCohomology.SymplecticFour InvolutionCentralizers
variable {F:Type*} [Field F] [CharP F 2]
omit [CharP F 2] in
private theorem pow_eq_one_of_block
    {ι:Type*} [Fintype ι] [DecidableEq ι]
    (A:Matrix ι ι F) (B:Matrix (Fin 2) (Fin 2) F)
    (R:Matrix ι (Fin 2) F) (L:Matrix (Fin 2) ι F)
    (hR:A*R=R*B) (hL:L*R=1) (n:ℕ) (h:A^n=1) : B^n=1 := by
  have hh (m:ℕ) : A^m*R=R*B^m := by
    induction m with
    | zero => simp
    | succ m ih =>
      rw [pow_succ',Matrix.mul_assoc,ih,←Matrix.mul_assoc,hR,Matrix.mul_assoc,←pow_succ']
  have he := congrArg (fun M=>L*M) (hh n)
  rw [h,Matrix.one_mul,←Matrix.mul_assoc,hL,Matrix.one_mul] at he
  exact he.symm

private def column (j:Fin 2) : Matrix (Fin 2⊕Fin 2) (Fin 2) F :=
  fun i k => if k=0 then if i=Sum.inl 0 then 1 else 0
    else if i=Sum.inr j then 1 else 0

omit [CharP F 2] in
private theorem column_left_inverse (j:Fin 2) : (column (F:=F) j)ᵀ*column (F:=F) j=1 := by
  ext k l
  fin_cases j <;> fin_cases k <;> fin_cases l <;>
    simp [column,Matrix.mul_apply,Fintype.sum_sum_type,Fin.sum_univ_two]

private theorem root_inv (r:Fin 8) (t:F) : (rootElement r t)⁻¹=rootElement r t := by
  apply inv_eq_of_mul_eq_one_left
  exact (pow_two _).symm.trans (rootElement_sq r t)

private theorem long_product_block (t s:F) :
    (rootElement 0 t*rootElement 1 s*rootElement 0 t*(rootElement 1 s)⁻¹).val * column 0 =
      column 0 * Matrix.BinaryTwoTrace.pairBlock t s := by
  rw [root_inv]
  ext i k
  rcases i with i | i <;> fin_cases i <;> fin_cases k <;>
    simp [rootElement,rootMatrix,column,Submonoid.coe_mul,Matrix.mul_apply,
      Fintype.sum_sum_type,Fin.sum_univ_two,Matrix.BinaryTwoTrace.pairBlock,Matrix.single] <;> ring_nf <;> simp

private theorem short_product_block (t s:F) :
    (rootElement 4 t*rootElement 5 s*rootElement 4 t*(rootElement 5 s)⁻¹).val * column 1 =
      column 1 * Matrix.BinaryTwoTrace.pairBlock t s := by
  rw [root_inv]
  ext i k
  rcases i with i | i <;> fin_cases i <;> fin_cases k <;>
    simp [rootElement,rootMatrix,column,Submonoid.coe_mul,Matrix.mul_apply,
      Fintype.sum_sum_type,Fin.sum_univ_two,Matrix.BinaryTwoTrace.pairBlock,Matrix.single] <;> ring_nf <;> simp

private theorem mixed_product_block (s:F) :
    (c2Representative F*rootElement 1 s*c2Representative F*(rootElement 1 s)⁻¹).val * column 0 =
      column 0 * Matrix.BinaryTwoTrace.pairBlock 1 s := by
  rw [root_inv]
  ext i k
  rcases i with i | i <;> fin_cases i <;> fin_cases k <;>
    simp [c2Representative,rootElement,rootMatrix,column,Submonoid.coe_mul,Matrix.mul_apply,
      Fintype.sum_sum_type,Fin.sum_univ_two,Matrix.BinaryTwoTrace.pairBlock,Matrix.single] <;> ring_nf <;> simp
end Theory.SpecificGroups.SymplecticFour.InvolutionPairs
namespace Theory.SpecificGroups.SymplecticFour.InvolutionPairs
open Representation.OneCohomology.SymplecticFour InvolutionCentralizers
variable {F:Type*} [Field F] [CharP F 2]
private theorem product_obstruction_of_block (t x:Sp F) (j:Fin 2) (a b:F)
    (h0:a*b≠0) (h1:a*b≠1)
    (hblock:(t*x*t*x⁻¹).val*column j=column j*Matrix.BinaryTwoTrace.pairBlock a b) :
    (∀n:ℕ,(t*x*t*x⁻¹)^(2^n)≠1) ∧ (t*x*t*x⁻¹)^6≠1 := by
  have hp (n:ℕ) (h:(t*x*t*x⁻¹)^n=1) : Matrix.BinaryTwoTrace.pairBlock a b^n=1 := by
    apply pow_eq_one_of_block _ _ (column j) (column j)ᵀ hblock (column_left_inverse j) n
    exact congrArg Subtype.val h
  constructor
  · intro n h
    exact Matrix.BinaryTwoTrace.not_pow_two _ (by
      rw [Matrix.BinaryTwoTrace.pairBlock_trace]
      exact pow_ne_zero _ h0) n (hp _ h)
  · intro h
    exact Matrix.BinaryTwoTrace.pairBlock_not_six a b h0 h1 (hp _ h)
end Theory.SpecificGroups.SymplecticFour.InvolutionPairs
namespace Theory.SpecificGroups.SymplecticFour.InvolutionPairs
open Representation.OneCohomology.SymplecticFour InvolutionCentralizers InvolutionTypes
variable {F:Type*} [Field F] [CharP F 2]
omit [CharP F 2] in
private theorem conjugate_obstruction (t x h:Sp F)
    (hp:(∀n:ℕ,(t*x*t*x⁻¹)^(2^n)≠1) ∧ (t*x*t*x⁻¹)^6≠1) :
    (∀n:ℕ,((h*t*h⁻¹)*(h*x*h⁻¹)*(h*t*h⁻¹)*(h*x*h⁻¹)⁻¹)^(2^n)≠1) ∧
      ((h*t*h⁻¹)*(h*x*h⁻¹)*(h*t*h⁻¹)*(h*x*h⁻¹)⁻¹)^6≠1 := by
  have hf (m:ℕ) (hn:(t*x*t*x⁻¹)^m≠1) :
      ((h*t*h⁻¹)*(h*x*h⁻¹)*(h*t*h⁻¹)*(h*x*h⁻¹)⁻¹)^m≠1 := by
    intro he
    apply hn
    apply (MulAut.conj h).injective
    simpa only [map_pow,map_mul,map_inv,MulAut.conj_apply,map_one] using he
  exact ⟨fun n=>hf _ (hp.1 n),hf _ hp.2⟩

variable [Finite F]
/-- Every native binary symplectic involution has a conjugate whose product
has neither two-power order nor sixth power one. -/
theorem exists_product_obstruction (hF:2<Nat.card F) (t:Sp F) (ht:orderOf t=2) :
    ∃x:Sp F, (∀n:ℕ,(t*x*t*x⁻¹)^(2^n)≠1) ∧ (t*x*t*x⁻¹)^6≠1 := by
  classical
  let := Fintype.ofFinite F
  have hcard : 3≤ENat.card F := by
    rw [ENat.card_eq_coe_fintype_card]
    have hh : 3≤Fintype.card F := by rw [←Nat.card_eq_fintype_card]; omega
    exact_mod_cast hh
  obtain ⟨a,ha0,ha1⟩ := ENat.exists_ne_ne_of_three_le hcard (0:F) 1
  have hroot (u:F) (hu:u≠0) : u*(a/u)=a := by field_simp
  rcases involution_types t ht with hb | ha | hc
  · obtain ⟨h,u,hu,he⟩ := isB1_conjugate_root0 t hb
    have hp := product_obstruction_of_block (rootElement 0 u) (rootElement 1 (a/u))
      0 u (a/u) (by rwa [hroot u hu]) (by rwa [hroot u hu]) (long_product_block _ _)
    refine ⟨h*rootElement 1 (a/u)*h⁻¹,?_⟩
    rw [he]
    exact conjugate_obstruction (rootElement 0 u) (rootElement 1 (a/u)) h hp
  · obtain ⟨h,u,hu,he⟩ := isA2_conjugate_root4 t ha
    have hp := product_obstruction_of_block (rootElement 4 u) (rootElement 5 (a/u))
      1 u (a/u) (by rwa [hroot u hu]) (by rwa [hroot u hu]) (short_product_block _ _)
    refine ⟨h*rootElement 5 (a/u)*h⁻¹,?_⟩
    rw [he]
    exact conjugate_obstruction (rootElement 4 u) (rootElement 5 (a/u)) h hp
  · obtain ⟨h,he⟩ := isC2_conjugate_c2 t hc
    have hp := product_obstruction_of_block (c2Representative F) (rootElement 1 a)
      0 1 a (by simpa using ha0) (by simpa using ha1) (mixed_product_block _)
    refine ⟨h*rootElement 1 a*h⁻¹,?_⟩
    rw [he]
    exact conjugate_obstruction (c2Representative F) (rootElement 1 a) h hp

/-- The exact pair convention used in the original 13.5.21 source. -/
theorem exists_bad_pair (hF:2<Nat.card F) (t:Sp F) (ht:orderOf t=2) :
    ∃x:Sp F,
      ¬IsPGroup 2 (zpowers t⊔(zpowers t).map (MulAut.conj x).toMonoidHom:Subgroup (Sp F)) ∧
      ¬Nonempty ((zpowers t⊔(zpowers t).map (MulAut.conj x).toMonoidHom:Subgroup (Sp F))≃*
        Equiv.Perm (Fin 3)) := by
  obtain ⟨x,hp,h6⟩ := exists_product_obstruction hF t ht
  let B := zpowers t⊔(zpowers t).map (MulAut.conj x).toMonoidHom
  have hy : t*x*t*x⁻¹∈B := by
    have hh : x*t*x⁻¹∈B := mem_sup_right (mem_map_of_mem _ (mem_zpowers t))
    simpa only [mul_assoc] using B.mul_mem (mem_sup_left (mem_zpowers t)) hh
  let y:B := ⟨t*x*t*x⁻¹,hy⟩
  refine ⟨x,?_,?_⟩
  · intro hB
    obtain ⟨n,hn⟩ := hB.exists_pow_pow_eq_one y
    exact hp n (congrArg Subtype.val hn)
  · rintro ⟨e⟩
    have hc : Nat.card B=6 := by
      rw [Nat.card_congr e.toEquiv,Nat.card_eq_fintype_card,Fintype.card_perm]
      norm_num
    have hh := pow_card_eq_one' (x:=y)
    rw [hc] at hh
    exact h6 (congrArg Subtype.val hh)
end Theory.SpecificGroups.SymplecticFour.InvolutionPairs
