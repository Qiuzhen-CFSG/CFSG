module
public import Theory.Representation.HermitianTensorThree.ParabolicTorus.Determinant
import all Theory.Representation.HermitianTensorThree.ParabolicTorus.Determinant
public import Theory.Representation.HermitianTensorThree.UnipotentRadicals.LargeActors
import all Theory.Representation.HermitianTensorThree.UnipotentRadicals.LargeActors
import all Theory.Representation.HermitianTensorThree.UnipotentRadicals

/-!
# The split exponent from a large Hermitian fixed space

Two independent root coordinates inject a large point actor's fixed space
into three copies of the fixed field. Thus an inner elementary actor of
rank greater than 2n fixing more than 3n dimensions has the fixed space of
a marked plane radical. An odd congruence whose fixed space lies inside
it and exceeds 3n fixes that entire plane: restriction of scalars makes
the dimension divisible by n, and the plane has dimension 4n.

Pointwise fixation of the two diagonal matrices makes the congruence matrix
upper triangular with only two possible off-diagonal entries. Its odd order
therefore divides 2^(2n)-1. This strengthens the general parabolic exponent
only under the additional, proved fixed-space conditions. The Chapter 8
HermitianSourceGeometricTorus application uses it to remove the actor-degree
premise from the intermediate selected-torus exclusion.

Source: Aschbacher–Smith H.4.2–4 and the Hermitian argument in 8.2.3,
printed pp.380–381 and715–716 (1 March 2004 manuscript, refs/quasithin.pdf).
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup Representation Representation.BinaryOffender
open Representation.HermitianTensorThree Representation.HermitianTensorThree.ImageOuter
open Matrix.PSL3Even.UnipotentGeometry
open scoped IsMulCommutative
namespace Representation.HermitianTensorThree.LargeActors
variable (n : ℕ) [NeZero n]

/-- Two independent root coordinates bound the point fixed space by 3n. -/
theorem point_fixed_rank_le_three_mul (B : Subgroup (U (E n)))
    (hB : B ≤ V₁ (E n)) (hr : 2*n < rank B) :
    Module.finrank (ZMod 2) (fixedSpace (UnipotentRadicals.ambientAction n)
      (B.map (UnipotentRadicals.unipotentHom n))) ≤ 3*n := by
  obtain ⟨b,hb⟩ : ∃ b : B, b.val.x ≠ 0 := by
    by_contra hn
    push Not at hn
    have hi : Function.Injective (fun b : B => b.val.c) := by
      intro a b h
      exact point_coordinates_injective n B hB (Prod.ext ((hn a).trans (hn b).symm) h)
    exact (not_le_of_gt (card_gt_field n B hr)) (Nat.card_le_card_of_injective _ hi)
  obtain ⟨c,hc⟩ : ∃ c : B, b.val.x * c.val.c - c.val.x * b.val.c ≠ 0 := by
    by_contra hn
    push Not at hn
    have hi : Function.Injective (fun c : B => c.val.x) := by
      intro c d h
      apply point_coordinates_injective n B hB
      refine Prod.ext h ?_
      apply mul_left_cancel₀ hb
      linear_combination hn c - hn d + b.val.c * h
    exact (not_le_of_gt (card_gt_field n B hr)) (Nat.card_le_card_of_injective _ hi)
  let W := fixedSpace (UnipotentRadicals.ambientAction n) (B.map (UnipotentRadicals.unipotentHom n))
  have htrace (a : B) (X : W) :
      sigma n (a.val.x * X.val.val 1 0 + a.val.c * X.val.val 2 0) =
        a.val.x * X.val.val 1 0 + a.val.c * X.val.val 2 0 := by
    obtain ⟨h11,h21,h12,h22⟩ := point_fixed_conditions n B hB hr X
    have hy := (mem_V₁ _ _).mp (hB a.property)
    have he := congrArg (fun Y : Mat n => Y 0 0) (fixed_equation n B X a)
    simp [matrix,adjoint,Matrix.mul_apply,Matrix.vecMul,dotProduct,Fin.sum_univ_three,
      hy,h11,h21,h12,h22] at he
    apply (CharTwo.add_eq_zero.mp ?_).symm
    rw [map_add,map_mul,map_mul,entry_conjugate,entry_conjugate]
    linear_combination he
  let f : W → F n × F n × F n := fun X =>
    (⟨X.val.val 0 0,entry_conjugate n X.val 0 0⟩,
      ⟨b.val.x * X.val.val 1 0 + b.val.c * X.val.val 2 0,htrace b X⟩,
      ⟨c.val.x * X.val.val 1 0 + c.val.c * X.val.val 2 0,htrace c X⟩)
  have hi : Function.Injective f := by
    intro X Y he
    have h00 := congrArg (fun z : F n × F n × F n => z.1.val) he
    have hb' := congrArg (fun z : F n × F n × F n => z.2.1.val) he
    have hc' := congrArg (fun z : F n × F n × F n => z.2.2.val) he
    change X.val.val 0 0 = Y.val.val 0 0 at h00
    change b.val.x * X.val.val 1 0 + b.val.c * X.val.val 2 0 =
      b.val.x * Y.val.val 1 0 + b.val.c * Y.val.val 2 0 at hb'
    change c.val.x * X.val.val 1 0 + c.val.c * X.val.val 2 0 =
      c.val.x * Y.val.val 1 0 + c.val.c * Y.val.val 2 0 at hc'
    have h10 : X.val.val 1 0 = Y.val.val 1 0 := by
      apply sub_eq_zero.mp
      apply (mul_eq_zero.mp ?_).resolve_left hc
      linear_combination c.val.c * hb' - b.val.c * hc'
    have h20 : X.val.val 2 0 = Y.val.val 2 0 := by
      apply sub_eq_zero.mp
      apply (mul_eq_zero.mp ?_).resolve_left hc
      linear_combination b.val.x * hc' - c.val.x * hb'
    have h01 : X.val.val 0 1 = Y.val.val 0 1 := by
      rw [←entry_conjugate n X.val 0 1,←entry_conjugate n Y.val 0 1,h10]
    have h02 : X.val.val 0 2 = Y.val.val 0 2 := by
      rw [←entry_conjugate n X.val 0 2,←entry_conjugate n Y.val 0 2,h20]
    obtain ⟨hx11,hx21,hx12,hx22⟩ := point_fixed_conditions n B hB hr X
    obtain ⟨hy11,hy21,hy12,hy22⟩ := point_fixed_conditions n B hB hr Y
    apply Subtype.ext
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [hx11,hx21,hx12,hx22,hy11,hy21,hy12,hy22,h00,h01,h02,h10,h20]
  have hc := Nat.card_le_card_of_injective f hi
  rw [Nat.card_prod,Nat.card_prod,card_F,←pow_add,←pow_add,
    Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod] at hc
  have hh := (pow_le_pow_iff_right₀ Nat.one_lt_two).mp hc
  change Module.finrank (ZMod 2) W ≤ 3*n
  omega

/-- A large inner actor with more than 3n fixed dimensions fixes exactly
one marked Hermitian plane, even without maximal actor rank. -/
theorem inner_fixed_plane_of_large_fixed
    (A : Subgroup (Space n ≃ₗ[ZMod 2] Space n)) [IsElementaryAbelian 2 A]
    (hA : A ≤ binaryImage n) (hr : 2*n < rank A)
    (hfixed : 3*n < Module.finrank (ZMod 2)
      (fixedSpace (UnipotentRadicals.ambientAction n) A)) :
    ∃ c : Cover n,
      fixedSpace (UnipotentRadicals.ambientAction n)
        (A.map (MulAut.conj (binaryActionHom n c)).toMonoidHom) =
      fixedSpace (UnipotentRadicals.ambientAction n) (UnipotentRadicals.plane n) := by
  obtain ⟨c,hc⟩ := UnipotentRadicals.two_subgroup_conjugate_le_unipotent n A
    (IsElementaryAbelian.isPGroup 2 A) hA
  let f := (MulAut.conj (binaryActionHom n c)).toMonoidHom
  let B := (A.map f).comap (UnipotentRadicals.unipotentHom n)
  let : IsElementaryAbelian 2 (A.map f) := IsElementaryAbelian.map f
  have hi : Function.Injective ((UnipotentRadicals.unipotentHom n).subgroupComap (A.map f)) :=
    fun a b h => Subtype.ext (UnipotentRadicals.unipotentHom_injective n (congrArg Subtype.val h))
  let : IsElementaryAbelian 2 B := IsElementaryAbelian.of_injective _ hi
  have hm : B.map (UnipotentRadicals.unipotentHom n) = A.map f := map_comap_eq_self hc
  have hBr : 2*n < rank B := by
    rw [←rank_map_injective (UnipotentRadicals.unipotentHom n)
      (UnipotentRadicals.unipotentHom_injective n),hm,rank_map_conj]
    exact hr
  have hd := (fixedSpaceConjEquiv (UnipotentRadicals.ambientAction n) A
    (binaryActionHom n c)).finrank_eq
  rcases elementary_le_plane (E n) B with hB | hB
  · have hb := point_fixed_rank_le_three_mul n B hB hBr
    rw [hm,←hd] at hb
    omega
  · refine ⟨c,?_⟩
    change fixedSpace _ (A.map f) = _
    rw [←hm]
    apply le_antisymm
    · intro X hX
      exact (UnipotentRadicals.mem_plane_fixed_iff n X).mpr
        (plane_fixed_conditions n B hB hBr ⟨X,hX⟩)
    · intro X hX a
      exact hX ⟨a.val, map_mono hB a.property⟩
end Representation.HermitianTensorThree.LargeActors

open Matrix Subgroup Representation Representation.BinaryOffender
open Representation.HermitianTensorThree Representation.HermitianTensorThree.ImageOuter
open Representation.HermitianTensorThree.ImageOuter.FieldSections
namespace Representation.HermitianTensorThree.ParabolicTorus
variable (n : ℕ) [NeZero n]

/-- Fixing the plane pointwise gives the split parabolic exponent, even
when the determinant norm is not one. -/
theorem plane_fixed_odd_order_dvd
    (g : GeneralLinearGroup (Fin 3) (E n))
    (hfix : ∀ X ∈ fixedSpace (UnipotentRadicals.ambientAction n) (UnipotentRadicals.plane n),
      binaryCongruence n g X = X)
    (ho : Odd (orderOf (binaryCongruence n g))) :
    orderOf (binaryCongruence n g) ∣ 2^(2*n)-1 := by
  have hd (j : Fin 3) (hj : j = 0 ∨ j = 1) :
      binaryCongruence n g (diagonalUnit n j) = diagonalUnit n j := by
    apply hfix
    apply (UnipotentRadicals.mem_plane_fixed_iff n _).mpr
    rcases hj with rfl | rfl <;> simp [diagonalUnit]
  obtain ⟨_,hc0⟩ := column_of_fixed_diagonal n g 0 (hd 0 (Or.inl rfl))
  obtain ⟨_,hc1⟩ := column_of_fixed_diagonal n g 1 (hd 1 (Or.inr rfl))
  have h10 := hc0 1 (by decide)
  have h20 := hc0 2 (by decide)
  have h01 := hc1 0 (by decide)
  have h21 := hc1 2 (by decide)
  have hdet : g.val.det = g.val 0 0 * g.val 1 1 * g.val 2 2 := by
    simp [Matrix.det_fin_three,h10,h20,h01,h21]
  have hne (i : Fin 3) : g.val i i ≠ 0 := by
    have hh := g.det_ne_zero
    rw [hdet] at hh
    fin_cases i <;> aesop
  have hp (i : Fin 3) : (g.val i i) ^ (2^(2*n)-1) = 1 := by
    let := Fintype.ofFinite (E n)
    have hh := FiniteField.pow_card_sub_one_eq_one (g.val i i) (hne i)
    rwa [←Nat.card_eq_fintype_card,card_E] at hh
  let q := 2^(2*n)-1
  let a := g.val ^ q
  obtain ⟨ha10,ha20,ha01,ha21,hadiag⟩ := two_columns_pow g.val h10 h20 h01 h21 q
  have ha (i : Fin 3) : a i i = 1 := (hadiag i).trans (hp i)
  have hs : a^2 = 1 := by
    rw [pow_two]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply,Fin.sum_univ_three,show a 1 0 = 0 from ha10,
        show a 2 0 = 0 from ha20,show a 0 1 = 0 from ha01,
        show a 2 1 = 0 from ha21,ha,CharTwo.add_self_eq_zero]
  have hg : g^(2*q) = 1 := by
    apply Units.ext
    change g.val ^ (2*q) = 1
    rw [Nat.mul_comm 2 q,pow_mul]
    exact hs
  have hx : binaryCongruence n g ^ (2*q) = 1 := by rw [←map_pow,hg,map_one]
  exact ho.coprime_two_right.dvd_of_dvd_mul_left (orderOf_dvd_of_pow_eq_one hx)
end Representation.HermitianTensorThree.ParabolicTorus

namespace Representation.HermitianTensorThree.ParabolicTorus
variable (n : ℕ) [NeZero n]

/-- An odd congruence with more than 3n fixed dimensions inside a large
inner actor's fixed space has the split exponent. -/
theorem odd_order_dvd_of_large_fixed_inside_inner_actor
    (A : Subgroup (BinaryAut n)) [IsElementaryAbelian 2 A]
    (hA : A ≤ binaryImage n) (hr : 2*n < rank A)
    (g : GeneralLinearGroup (Fin 3) (E n))
    (ho : Odd (orderOf (binaryCongruence n g)))
    (hle : fixedSpace (UnipotentRadicals.ambientAction n) (zpowers (binaryCongruence n g)) ≤
      fixedSpace (UnipotentRadicals.ambientAction n) A)
    (hlarge : 3*n < Module.finrank (ZMod 2)
      (fixedSpace (UnipotentRadicals.ambientAction n) (zpowers (binaryCongruence n g)))) :
    orderOf (binaryCongruence n g) ∣ 2^(2*n)-1 := by
  have hbound := (Submodule.finrank_mono hle).trans (LargeActors.inner_fixed_rank_le n A hA hr)
  have hdiv : n ∣ Module.finrank (ZMod 2)
      (fixedSpace (UnipotentRadicals.ambientAction n) (zpowers (binaryCongruence n g))) := by
    let : Module (ZMod 2) (F n) := Algebra.toModule
    have hF : Module.finrank (ZMod 2) (F n) = n := by
      apply Nat.pow_right_injective (by decide : 2 ≤ 2)
      exact (FiniteField.pow_finrank_eq_natCard 2 (F n)).trans (card_F n)
    simpa only [hF] using
      (FiniteFieldSemilinearDisplacement.field_degree_dvd_fixedSpace (F := F n)
        (UnipotentRadicals.ambientAction n) (binaryCongruence n g)
        (fun a v => (congruence n g).map_smul a v))
  have hfour : Module.finrank (ZMod 2)
      (fixedSpace (UnipotentRadicals.ambientAction n) (zpowers (binaryCongruence n g))) = 4*n := by
    obtain ⟨d,hd⟩ := hdiv
    have hn := NeZero.pos n
    have hlo : 4 ≤ d := by nlinarith
    nlinarith
  obtain ⟨c,hc⟩ := LargeActors.inner_fixed_plane_of_large_fixed n A hA hr
    (hlarge.trans_le (Submodule.finrank_mono hle))
  let u := binaryActionHom n c
  let f := (MulAut.conj u).toMonoidHom
  let g' := (MulAut.conj (Matrix.SpecialLinearGroup.toGL c)) g
  have hg : binaryCongruence n g' = f (binaryCongruence n g) := by
    change binaryCongruence n (Matrix.SpecialLinearGroup.toGL c * g *
      (Matrix.SpecialLinearGroup.toGL c)⁻¹) = _
    rw [map_mul,map_mul,map_inv,binaryCongruence_toGL]
    rfl
  have he (a : BinaryAut n) (v : Space n) :
      u (UnipotentRadicals.ambientAction n a v) =
        UnipotentRadicals.ambientAction n (f a) (u v) := by
    change u (a v) = u (a (u.symm (u v)))
    rw [u.symm_apply_apply]
  have hm (B : Subgroup (BinaryAut n)) := fixedSpace_map_equivariant
    (UnipotentRadicals.ambientAction n) (UnipotentRadicals.ambientAction n) f u he B
  have hz : (zpowers (binaryCongruence n g)).map f = zpowers (binaryCongruence n g') := by
    rw [MonoidHom.map_zpowers,hg]
  have hle' : fixedSpace (UnipotentRadicals.ambientAction n) (zpowers (binaryCongruence n g')) ≤
      fixedSpace (UnipotentRadicals.ambientAction n) (UnipotentRadicals.plane n) := by
    rw [←hc,←hz,←hm,←hm]
    exact Submodule.map_mono hle
  have hd' : Module.finrank (ZMod 2) (fixedSpace (UnipotentRadicals.ambientAction n)
      (zpowers (binaryCongruence n g'))) = 4*n := by
    rw [←hz,←hm,LinearEquiv.finrank_map_eq,hfour]
  have heq : fixedSpace (UnipotentRadicals.ambientAction n) (zpowers (binaryCongruence n g')) =
      fixedSpace (UnipotentRadicals.ambientAction n) (UnipotentRadicals.plane n) :=
    Submodule.eq_of_le_of_finrank_eq hle' (hd'.trans (UnipotentRadicals.finrank_plane_fixed n).symm)
  have hord : orderOf (binaryCongruence n g') = orderOf (binaryCongruence n g) := by
    rw [hg,orderOf_injective f (MulAut.conj u).injective]
  have hfix : ∀ X ∈ fixedSpace (UnipotentRadicals.ambientAction n) (UnipotentRadicals.plane n),
      binaryCongruence n g' X = X := by
    intro X hX
    rw [←heq] at hX
    exact (mem_fixedSpace_zpowers_iff _ _ _).mp hX
  have ho' : Odd (orderOf (binaryCongruence n g')) := by
    rw [hord]
    exact ho
  have hh := plane_fixed_odd_order_dvd n g' hfix ho'
  rwa [hord] at hh
end Representation.HermitianTensorThree.ParabolicTorus
