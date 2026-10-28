module
public import Theory.GroupAction.SixteenOddComplements.InvariantPlanes
public import Theory.GroupAction.SixteenOddComplements.AffineProduct
public import Theory.SpecificGroups.SymmetricThreeProduct.Parabolics.Structure
/-!
# Recognizing the sixteen by symmetric-three-product extension

A self-centralizing normal elementary sixteen with quotient S₃×S₃ is
S₄×S₄ when its conjugation action contains a transvection. The normal-nine
normalizer supplies a complement, and the transvection forces the two
normal cubic factors to have complementary invariant fixed planes.
The resulting two affine actions on four-point quotients identify the group.

Source: Aschbacher--Smith F.5.7, printed p.303. The transvection premise is
essential: the quotient and order alone do not determine the binary action.
-/
open Subgroup
open scoped IsMulCommutative
namespace SixteenOddComplements
public theorem symmetric_four_product_of_symmetric_three_pair_quotient
    {G : Type*} [Group G] [Finite G]
    (A : Subgroup G) [A.Normal] [IsElementaryAbelian 2 A]
    (hA : Nat.card A=16) (hC : centralizer (A : Set G)≤A)
    (e : (G ⧸ A) ≃* Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3))
    (g : G) (hg : Nat.card (MulAut.conjNormal (H:=A) g).fixedSubgroup=8) :
    Nonempty (G ≃* Equiv.Perm (Fin 4) × Equiv.Perm (Fin 4)) := by
  have hQ : Nat.card (G ⧸ A)=36 := by
    rw [Nat.card_congr e.toEquiv,Nat.card_prod,Nat.card_perm,Nat.card_fin]
    decide
  have hcore : pCore 2 (G ⧸ A)=⊥ := by
    apply map_injective (f:=e.toMonoidHom) e.injective
    rw [Subgroup.map_bot,pCore_map_iso 2 e]
    exact SymmetricThreeProduct.twoCore_eq_bot
  obtain ⟨B,hB⟩ := exists_complement_of_quotient_thirty_six A hA hC hQ hcore
  let eB : B ≃* Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3) :=
    hB.symm.QuotientMulEquiv.symm.trans e
  let ρ : B →* MulAut A := A.normalizerMonoidHom.comp
    (inclusion (show B≤normalizer (A : Set G) by rw [normalizer_eq_top];exact le_top))
  have hρb (b:B) : ρ b = MulAut.conjNormal (H:=A) (b:G) := by
    ext a
    rfl
  have hρ : Function.Injective ρ := by
    apply (injective_iff_map_eq_one ρ).mpr
    intro b hb
    apply Subtype.ext
    apply hB.disjoint.le_bot
    refine ⟨hC ?_,b.property⟩
    intro a ha
    have he := congrArg (fun k : MulAut A => (k ⟨a,ha⟩).val) hb
    change (b:G)*a*(b:G)⁻¹=a at he
    exact (mul_inv_eq_iff_eq_mul.mp he).symm
  obtain ⟨⟨a,b⟩,hab⟩ := hB.surjective g
  change (a:G)*(b:G)=g at hab
  have haa : MulAut.conjNormal (H:=A) (a:G)=1 := by
    rw [MulAut.conjNormal_val]
    apply MulEquiv.ext
    intro x
    change a*x*a⁻¹=x
    rw [mul_comm a x,mul_inv_cancel_right]
  have hgb : MulAut.conjNormal (H:=A) g=ρ b := by
    rw [←hab,map_mul,haa,one_mul,←hρb]
  have ht : Nat.card (ρ b).fixedSubgroup=8 := hgb ▸ hg
  have hBc : Nat.card B=36 := by
    rw [Nat.card_congr eB.toEquiv,Nat.card_prod,Nat.card_perm,Nat.card_fin]
    decide
  obtain ⟨U,W,hU,hW,hd,hu,hw⟩ := invariant_planes_of_symmetric_three_pair hA eB ρ hρ b ht
  obtain ⟨eaff⟩ := affine_product_equiv_of_invariant_planes ρ hA hBc hρ U W hU hW hd hu hw
  exact ⟨(SemidirectProduct.mulEquivSubgroup hB).symm.trans eaff⟩
end SixteenOddComplements
