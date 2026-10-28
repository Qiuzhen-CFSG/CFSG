module
public import Theory.ElementaryAbelian.Basic
public import Mathlib.GroupTheory.SemidirectProduct
public import Mathlib.Data.Finite.Perm
/-!
# Affine recognition from two invariant binary planes

A faithful actor of order36 on binary16 preserving two disjoint planes has
its semidirect product isomorphic to S₄×S₄. The product acts on the two
four-element quotient sets by affine permutations. The joint kernel is
trivial, and equality of orders gives surjectivity.

This is the final faithful action step in Aschbacher--Smith F.5.7, p.303.
The affine quotient construction follows the existing elementary-nine by
four recognition, specialized here to the two binary quotient planes.
-/
open scoped IsMulCommutative Pointwise
namespace SixteenOddComplements
variable {E D : Type*} [Group E] [Group D] [Finite E] [Finite D]
  [IsElementaryAbelian 2 E]
private def quotientAction (ρ : D →* MulAut E) (L : Subgroup E)
    (hL : ∀ d : D, ∀ x ∈ L, ρ d x ∈ L) : D →* MulAut (E ⧸ L) := by
  let f (d : D) : E ⧸ L →* E ⧸ L :=
    QuotientGroup.map L L (ρ d).toMonoidHom (hL d)
  refine {
    toFun := fun d => { f d with
      invFun := f d⁻¹
      left_inv := ?_
      right_inv := ?_ }
    map_one' := ?_
    map_mul' := ?_ }
  · intro q
    induction q using QuotientGroup.induction_on with
    | H x =>
      change QuotientGroup.mk (ρ d⁻¹ (ρ d x)) = QuotientGroup.mk x
      rw [← MulAut.mul_apply, ← map_mul, inv_mul_cancel, map_one]
      rfl
  · intro q
    induction q using QuotientGroup.induction_on with
    | H x =>
      change QuotientGroup.mk (ρ d (ρ d⁻¹ x)) = QuotientGroup.mk x
      rw [← MulAut.mul_apply, ← map_mul, mul_inv_cancel, map_one]
      rfl
  · ext q
    induction q using QuotientGroup.induction_on with
    | H x => change QuotientGroup.mk (ρ 1 x) = QuotientGroup.mk x; simp
  · intro d e
    ext q
    induction q using QuotientGroup.induction_on with
    | H x =>
      change QuotientGroup.mk (ρ (d * e) x) = QuotientGroup.mk (ρ d (ρ e x))
      rw [map_mul, MulAut.mul_apply]

private def affineHom {N A : Type*} [Group N] [Group A] (φ : A →* MulAut N) :
    N ⋊[φ] A →* Equiv.Perm N where
  toFun g := Equiv.mulLeft g.left * (φ g.right).toEquiv
  map_one' := by ext x; simp
  map_mul' g h := by
    ext x
    change (g.left * φ g.right h.left) * φ (g.right * h.right) x =
      g.left * φ g.right (h.left * φ h.right x)
    simp only [map_mul, MulAut.mul_apply, mul_assoc]

private def affineQuotientHom (ρ : D →* MulAut E) (L : Subgroup E)
    (hL : ∀ d : D, ∀ x ∈ L, ρ d x ∈ L) : E ⋊[ρ] D →* Equiv.Perm (E ⧸ L) :=
  (affineHom (quotientAction ρ L hL)).comp
    (SemidirectProduct.map (QuotientGroup.mk' L) (MonoidHom.id D)
      (fun _ => MonoidHom.ext fun _ => rfl))

omit [Finite E] [Finite D] in
private theorem affineQuotientHom_apply (ρ : D →* MulAut E) (L : Subgroup E)
    (hL : ∀ d : D, ∀ x ∈ L, ρ d x ∈ L) (g : E ⋊[ρ] D) (x : E) :
    affineQuotientHom ρ L hL g (QuotientGroup.mk x) =
      QuotientGroup.mk (g.left * ρ g.right x) := rfl


omit [Finite E] [Finite D] in
private theorem quotient_pair_injective (ρ : D →* MulAut E)
    (hρ : Function.Injective ρ) (L M : Subgroup E) (hd : Disjoint L M)
    (hL : ∀ d : D, ∀ x ∈ L, ρ d x ∈ L)
    (hM : ∀ d : D, ∀ x ∈ M, ρ d x ∈ M) :
    Function.Injective ((affineQuotientHom ρ L hL).prod (affineQuotientHom ρ M hM)) := by
  apply (injective_iff_map_eq_one _).mpr
  intro g hg
  have heL (x : E) : (QuotientGroup.mk (g.left * ρ g.right x) : E ⧸ L) =
      QuotientGroup.mk x := by
    rw [← affineQuotientHom_apply ρ L hL]
    have hh := congrArg (fun z : Equiv.Perm (E ⧸ L) × Equiv.Perm (E ⧸ M) =>
      z.1 (QuotientGroup.mk x)) hg
    exact hh
  have heM (x : E) : (QuotientGroup.mk (g.left * ρ g.right x) : E ⧸ M) =
      QuotientGroup.mk x := by
    rw [← affineQuotientHom_apply ρ M hM]
    exact congrArg (fun z : Equiv.Perm (E ⧸ L) × Equiv.Perm (E ⧸ M) =>
      z.2 (QuotientGroup.mk x)) hg
  have hn : g.left = 1 := Subgroup.disjoint_def.mp hd
    ((QuotientGroup.eq_one_iff _).mp (by simpa using heL 1))
    ((QuotientGroup.eq_one_iff _).mp (by simpa using heM 1))
  have hr : g.right = 1 := by
    apply hρ
    rw [map_one]
    ext x
    change ρ g.right x = x
    apply mul_inv_eq_one.mp
    apply Subgroup.disjoint_def.mp hd
    · apply (QuotientGroup.eq_one_iff _).mp
      have hx := heL x
      simp only [hn, one_mul] at hx
      simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv, hx, mul_inv_cancel]
    · apply (QuotientGroup.eq_one_iff _).mp
      have hx := heM x
      simp only [hn, one_mul] at hx
      simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv, hx, mul_inv_cancel]
  exact SemidirectProduct.ext hn hr


omit [Finite D] in
public theorem affine_product_equiv_of_invariant_planes (ρ : D →* MulAut E)
    (hE : Nat.card E = 16) (hD : Nat.card D = 36) (hρ : Function.Injective ρ)
    (L M : Subgroup E) (hLcard : Nat.card L = 4) (hMcard : Nat.card M = 4)
    (hd : Disjoint L M)
    (hL : ∀ d : D, ∀ x ∈ L, ρ d x ∈ L)
    (hM : ∀ d : D, ∀ x ∈ M, ρ d x ∈ M) :
    Nonempty ((E ⋊[ρ] D) ≃* (Equiv.Perm (Fin 4) × Equiv.Perm (Fin 4))) := by
  classical
  have hQL : Nat.card (E ⧸ L) = 4 := by
    have hh := L.card_eq_card_quotient_mul_card_subgroup
    rw [hE,hLcard] at hh
    omega
  have hQM : Nat.card (E ⧸ M) = 4 := by
    have hh := M.card_eq_card_quotient_mul_card_subgroup
    rw [hE,hMcard] at hh
    omega
  let f := (affineQuotientHom ρ L hL).prod (affineQuotientHom ρ M hM)
  have hf : Function.Bijective f := by
    rw [Nat.bijective_iff_injective_and_card]
    refine ⟨quotient_pair_injective ρ hρ L M hd hL hM, ?_⟩
    rw [Nat.card_congr (SemidirectProduct.equivProd : (E ⋊[ρ] D) ≃ E × D),
      Nat.card_prod, hE, hD, Nat.card_prod, Nat.card_perm, Nat.card_perm, hQL, hQM]
    decide
  let eL := Finite.equivFinOfCardEq hQL
  let eM := Finite.equivFinOfCardEq hQM
  exact ⟨(MulEquiv.ofBijective f hf).trans
    (MulEquiv.prodCongr eL.permCongrHom eM.permCongrHom)⟩
end SixteenOddComplements
