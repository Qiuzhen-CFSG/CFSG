module
public import Theory.GroupTheory.WreathTwoSubgroups
public import Theory.GroupTheory.SpecificGroups.SLTwoPermThree
public import Theory.GroupTheory.OrderThreeNormalizer

/-!
# Cubic normalizers in the two-plane wreath group

A subgroup of SL₂(2) wreath C₂ with a normal subgroup of order three
embeds in S₃ × S₃. Thus an order bound of 36 makes it that product.

Use the six-element dihedral coordinates for SL₂(2). Cubics supported on
one coordinate have the base product as normalizer. Cubics supported on
both coordinates have, after a coordinate inversion, the product of the
diagonal and antidiagonal dihedral factors as normalizer. The two explicit
product embeddings and this coverage are checked on the finite carrier;
the original subgroup then maps into their actual ranges. Cardinality
supplies surjectivity, retaining an actual group equivalence.

Source application: Aschbacher--Smith 14.3.23(2)(i), printed p.1000.
The original dotted L₁ supplies the normal cubic, and G.9.4(4) supplies
the order bound. The flag-specific application is kept in CFSG.
-/

open Subgroup
namespace Theory.GroupTheory.WreathCubicRecognition
private abbrev D := DihedralGroup 3
private abbrev C2 := Multiplicative (ZMod 2)
private abbrev W := RegularWreathProduct D C2
private abbrev P := D × D
private instance : Fintype W := Fintype.ofEquiv ((C2 → D) × C2)
  (RegularWreathProduct.equivProd D C2).symm
private instance : DecidableEq W := fun a b => decidable_of_iff
  (a.left=b.left ∧ a.right=b.right) RegularWreathProduct.ext_iff.symm
private def rot (diag : Bool) : W :=
  ⟨fun i => if diag || i=1 then .r 1 else .r (-1),1⟩
private def refl (diag : Bool) : W :=
  ⟨fun _ => if diag then .sr 0 else 1,Multiplicative.ofAdd 1⟩
private def diagonalMap (diag : Bool) : D →* W where
  toFun x := match x with
    | .r i => rot diag ^ i.val
    | .sr i => refl diag * rot diag ^ i.val
  map_one' := by cases diag <;> decide +kernel
  map_mul' := by cases diag <;> decide +kernel
private def pairFun (diag : Bool) (a : P) : W :=
  if diag then diagonalMap true a.1 * diagonalMap false a.2
  else ⟨fun i => if i=1 then a.1 else a.2,1⟩
private def pairMap (diag : Bool) : P →* W where
  toFun := pairFun diag
  map_one' := by cases diag <;> decide +kernel
  map_mul' := by cases diag <;> decide +kernel
private theorem pair_injective (diag : Bool) : Function.Injective (pairMap diag) := by
  cases diag <;> decide +kernel
private def twist (b : Bool) : W := ⟨fun i => if b && i=1 then .sr 0 else 1,1⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
private theorem coverage : ∀ x : W, x^3=1 → x≠1 →
    ∃ b diag : Bool, ∀ y : W,
      (y*x*y⁻¹=x ∨ y*x*y⁻¹=x⁻¹) →
        ∃ z : P, twist b * y * (twist b)⁻¹ = pairMap diag z := by
  decide +kernel
private abbrev SL := Matrix.SpecialLinearGroup (Fin 2) (ZMod 2)
private def toSL : D →* SL :=
  let a : SL := ⟨!![0,1;1,1],by decide⟩
  let t : SL := ⟨!![1,1;0,1],by decide⟩
  { toFun x := match x with
      | .r i => a ^ i.val
      | .sr i => t * a ^ i.val
    map_one' := by decide +kernel
    map_mul' := by decide +kernel }
private theorem toSL_injective : Function.Injective toSL := by decide +kernel
private noncomputable def smallEquiv : D ≃* SL :=
  MulEquiv.ofBijective toSL (toSL_injective.bijective_of_nat_card_le (by
    rw [DihedralGroup.nat_card,Nat.card_eq_fintype_card]
    decide +kernel))

private theorem normal_three_conjugate {A : Type*} [Group A]
    (N : Subgroup A) [N.Normal] (hN : Nat.card N=3)
    (x : N) (hx : orderOf x=3) (y : A) :
    y*(x:A)*y⁻¹=(x:A) ∨ y*(x:A)*y⁻¹=(x:A)⁻¹ := by
  classical
  have hz : zpowers x=⊤ := by
    apply zpowers_eq_top_of_prime_card hN
    intro hh
    simp [hh] at hx
  have hh : (⟨y*(x:A)*y⁻¹,(inferInstance : N.Normal).conj_mem x x.property y⟩ : N)∈zpowers x := by rw [hz]; trivial
  have hf : IsOfFinOrder x := orderOf_pos_iff.mp (by omega)
  rw [hf.mem_zpowers_iff_mem_range_orderOf,hx] at hh
  obtain ⟨i,hi,he⟩ := Finset.mem_image.mp hh
  have hi3 := Finset.mem_range.mp hi
  have he' := congrArg Subtype.val he
  have hp : (x:A)^3=1 := congrArg Subtype.val (show x^3=1 by rw [←hx]; exact pow_orderOf_eq_one x)
  have hs : (x:A)^2=(x:A)⁻¹ := by
    apply mul_right_cancel (b := (x:A))
    simpa only [←pow_succ,inv_mul_cancel] using hp
  interval_cases i
  · have hone : (x:A)=1 := (MulAut.conj y).injective (by simpa using he'.symm)
    have hxone : x=1 := Subtype.ext hone
    simp [hxone] at hx
  · exact .inl (by simpa using he'.symm)
  · exact .inr (by simpa only [coe_pow,hs] using he'.symm)

/-- A subgroup of the two-plane wreath group with a normal cubic and
order at least 36 is literally a symmetric-three product. -/
public theorem equiv_pair_of_injective_of_normal_cubic
    {A : Type*} [Group A] [Finite A]
    (f : A →* WreathTwoResidual.Actor) (hf : Function.Injective f)
    (N : Subgroup A) [N.Normal] (hN : Nat.card N=3)
    (hc : 36≤Nat.card A) :
    Nonempty (A ≃* (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3))) := by
  let E : WreathTwoResidual.Actor ≃* W :=
    RegularWreathProduct.congr smallEquiv.symm (MulEquiv.refl C2)
  let j := E.toMonoidHom.comp f
  have hj : Function.Injective j := E.injective.comp hf
  obtain ⟨x,hx⟩ := exists_prime_orderOf_dvd_card' (G := N) 3 (by rw [hN])
  have hxo : orderOf (x:A)=3 := (orderOf_injective N.subtype Subtype.val_injective x).trans hx
  have hjx : orderOf (j (x:A))=3 := (orderOf_injective j hj _).trans hxo
  have hjp : j (x:A)^3=1 := by simpa only [hjx] using pow_orderOf_eq_one (j (x:A))
  have hjne : j (x:A)≠1 := by intro he; simp [he] at hjx
  obtain ⟨b,diag,hcover⟩ := coverage (j (x:A)) hjp hjne
  let k := (MulAut.conj (twist b)).toMonoidHom.comp j
  have hk : Function.Injective k := (MulAut.conj _).injective.comp hj
  have hkr (a : A) : k a∈(pairMap diag).range := by
    have hh : j a*j (x:A)*(j a)⁻¹=j (x:A) ∨ j a*j (x:A)*(j a)⁻¹=(j (x:A))⁻¹ := by
      rcases normal_three_conjugate N hN x hx a with hh | hh
      · left
        simpa only [map_mul,map_inv] using congrArg j hh
      · right
        simpa only [map_mul,map_inv] using congrArg j hh
    obtain ⟨z,hz⟩ := hcover (j a) hh
    exact ⟨z,hz.symm⟩
  let q := (MonoidHom.ofInjective (pair_injective diag)).symm.toMonoidHom.comp
    (k.codRestrict (pairMap diag).range hkr)
  have hq : Function.Injective q := (MonoidHom.ofInjective (pair_injective diag)).symm.injective.comp
    (by intro a b hh; exact hk (congrArg Subtype.val hh))
  have hp : Nat.card P=36 := by rw [Nat.card_prod,DihedralGroup.nat_card]
  let e := MulEquiv.ofBijective q (hq.bijective_of_nat_card_le (hp ▸ hc))
  let c := smallEquiv.trans (Classical.choice SLTwoPermThree.sl2Two_equiv_perm_three)
  exact ⟨e.trans (MulEquiv.prodCongr c c)⟩

end Theory.GroupTheory.WreathCubicRecognition
