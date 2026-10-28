module
public import Theory.GroupTheory.C4SquareSymmetricThreeSplit
public import Theory.GroupAction.C4SquareSymmetricThreeActions
public import Mathlib.GroupTheory.SemidirectProduct
/-!
# Recognition of the abelian-core order-ninety-six vertex

Two order-96 groups with self-centralizing normal C₄ × C₄ subgroups and
symmetric-three quotients are isomorphic. Each is split by the original
cubic normalizer. Transport to its quotient marking gives a faithful S₃
action on the homocyclic square, and the proved action uniqueness gives
an isomorphism of the actual semidirect products.

Source: Aschbacher–Smith F.1.12(I)(8), printed p.263.
-/
public section
open Subgroup
namespace C4SquareExtension
private theorem normal_form {G : Type*} [Group G] [Finite G]
    (Q : Subgroup G) [Q.Normal] (e : Q ≃* Model)
    (hG : Nat.card G=96) (hself : centralizer (Q : Set G) ≤ Q)
    (eQ : G ⧸ Q ≃* Equiv.Perm (Fin 3)) :
    ∃ρ : Equiv.Perm (Fin 3) →* MulAut Model, Function.Injective ρ ∧
      Nonempty (G ≃* Model ⋊[ρ] Equiv.Perm (Fin 3)) := by
  obtain ⟨c,_,hs,⟨d⟩⟩ := exists_symmetric_three_complement Q e hG hself eQ
  let N := normalizer (zpowers c : Set G)
  let r : N →* MulAut Q := Q.normalizerMonoidHom.comp
    (inclusion (Q.normalizer_eq_top ▸ le_top))
  have hr : Function.Injective r := by
    apply r.ker_eq_bot_iff.mp
    apply le_bot_iff.mp
    intro n hn
    have hnC : (n:G)∈centralizer (Q : Set G) := by
      rw [mem_centralizer_iff]
      intro q hq
      have hh := congrArg Subtype.val (DFunLike.congr_fun (show r n=1 from hn) (⟨q,hq⟩ : Q))
      have he : (n:G)*q*(n:G)⁻¹=q := hh
      exact ((mul_inv_eq_iff_eq_mul).mp he).symm
    apply Subtype.ext
    exact (disjoint_iff_inf_le.mp hs.disjoint) ⟨hself hnC,n.property⟩
  let ρ : Equiv.Perm (Fin 3) →* MulAut Model :=
    (MulAut.congr e).toMonoidHom.comp (r.comp d.symm.toMonoidHom)
  have hρ : Function.Injective ρ := (MulAut.congr e).injective.comp (hr.comp d.symm.injective)
  refine ⟨ρ,hρ,?_⟩
  exact ⟨(SemidirectProduct.mulEquivSubgroup hs).symm.trans
    (SemidirectProduct.congr' e d)⟩

theorem equiv_of_selfCentralizing_c4_square
    {G H : Type*} [Group G] [Finite G] [Group H] [Finite H]
    (Q : Subgroup G) (R : Subgroup H) [Q.Normal] [R.Normal]
    (e : Q ≃* Model) (f : R ≃* Model)
    (hG : Nat.card G=96) (hH : Nat.card H=96)
    (hQ : centralizer (Q : Set G) ≤ Q) (hR : centralizer (R : Set H) ≤ R)
    (eQ : G ⧸ Q ≃* Equiv.Perm (Fin 3)) (eR : H ⧸ R ≃* Equiv.Perm (Fin 3)) :
    Nonempty (G ≃* H) := by
  obtain ⟨ρ,hρ,⟨eG⟩⟩ := normal_form Q e hG hQ eQ
  obtain ⟨σ,hσ,⟨eH⟩⟩ := normal_form R f hH hR eR
  obtain ⟨φ,hφ⟩ := SymmetricThreeActions.exists_equivariant ρ σ hρ hσ
  have hc (s : Equiv.Perm (Fin 3)) :
      (ρ s).trans φ=φ.trans (σ ((MulEquiv.refl _) s)) := by
    apply MulEquiv.ext
    exact hφ s
  exact ⟨eG.trans ((SemidirectProduct.congr φ (MulEquiv.refl _) hc).trans eH.symm)⟩
end C4SquareExtension
