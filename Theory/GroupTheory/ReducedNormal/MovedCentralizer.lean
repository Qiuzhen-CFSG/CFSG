module
public import Theory.Representation.BinaryOffender.MovedFaithfulness
public import Theory.Representation.NormalElementaryQuotient
public import Theory.GroupTheory.ReducedNormal.Defs
public import Theory.GroupTheory.GeneralizedFitting.ResidualCentralizer
public import Theory.GroupTheory.PResidual.FiniteImage
public import Theory.ElementaryAbelian.AbelianNormalClosure
/-!
# The moved subgroup retains the full centralizer of a reduced module

Let U be reduced normal elementary abelian and W=[U,O²(G)]. The actual
quotient G/C_G(U) acts faithfully on U and has trivial two-core. Its residual
is self-centralizing, so the displacement-kernel theorem makes its action
on W faithful. Thus C_G(W)=C_G(U), and W is reduced as well.
This preserves original Thompson movement without requiring a splitting
U=W+C_U(O²(G)). It supplies the common moved-module source reduction in
Aschbacher–Smith B.6.10 and E.2.3, printed pp.117 and216–217.
-/
public section
open Subgroup
open scoped IsMulCommutative
open scoped commutatorElement
namespace Theory.GroupTheory
open Representation
variable {G A : Type*} [Group G] [Group A]

theorem centralizer_commutator_eq_of_coreFree_image
    (U : Subgroup G) [U.Normal] [IsElementaryAbelian 2 U]
    (q : G →* A) (hq : Function.Surjective q)
    (hker : q.ker = centralizer (U : Set G)) (hcore : pCore 2 A = ⊥)
    (K : Subgroup G) [K.Normal]
    (hK : centralizer (K.map q : Set A) ≤ K.map q) :
    centralizer ((⁅U,K⁆ : Subgroup G) : Set G) = centralizer (U : Set G) := by
  let W := ⁅U,K⁆
  let N := (centralizer (W : Set G)).map q
  let ρ := NormalElementaryQuotient.representation U q hq hker
  let : N.Normal := Normal.map inferInstance q hq
  let : (K.map q).Normal := Normal.map inferInstance q hq
  have hN : N = ⊥ := by
    apply BinaryOffender.normal_eq_bot_of_fixes_displacements (G := A) (V := Additive U) ρ
      (NormalElementaryQuotient.representation_injective U q hq hker) hcore
      (K.map q) N hK
    rintro _ ⟨n,hn,rfl⟩ _ ⟨k,hk,rfl⟩ v
    let w := ρ (q k) v - v
    have hw : (w.toMul : G) ∈ W := by
      have he : (w.toMul : G) = ⁅k,(v.toMul : G)⁆ := by
        dsimp only [w]
        rw [toMul_sub,Subgroup.coe_div,div_eq_mul_inv,
          NormalElementaryQuotient.representation_apply U q hq hker]
        rfl
      rw [he]
      change ⁅k,(v.toMul : G)⁆ ∈ ⁅U,K⁆
      rw [commutator_comm U K]
      exact commutator_mem_commutator hk v.toMul.property
    apply Additive.toMul.injective
    apply Subtype.ext
    change ((ρ (q n) w).toMul : G) = w.toMul
    rw [NormalElementaryQuotient.representation_apply U q hq hker,
      ← hn w.toMul hw,mul_inv_cancel_right]
  apply le_antisymm ?_ (centralizer_le (commutator_le_left U K))
  intro g hg
  rw [← hker]
  have hh : q g ∈ N := mem_map_of_mem q hg
  exact mem_bot.mp (hN ▸ hh)

theorem IsPReduced.centralizer_commutator_eq
    (U : Subgroup G) [U.Normal] [IsElementaryAbelian 2 U] (hU : IsPReduced 2 U)
    (q : G →* A) (hq : Function.Surjective q)
    (hker : q.ker = centralizer (U : Set G))
    (K : Subgroup G) [K.Normal]
    (hK : centralizer (K.map q : Set A) ≤ K.map q) :
    centralizer ((⁅U,K⁆ : Subgroup G) : Set G) = centralizer (U : Set G) := by
  apply centralizer_commutator_eq_of_coreFree_image U q hq hker _ K hK
  let e := (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective q hq)
  rw [← pCore_map_iso 2 e,hU.quotient_pCore_eq_bot,Subgroup.map_bot]
end Theory.GroupTheory

namespace Theory.GroupTheory
variable {G : Type*} [Group G] [Finite G]
theorem IsPReduced.centralizer_moved_eq
    (U : Subgroup G) [U.Normal] [IsElementaryAbelian 2 U] (hU : IsPReduced 2 U) :
    centralizer ((⁅U,pResidual 2 G⁆ : Subgroup G) : Set G) = centralizer (U : Set G) := by
  let q := QuotientGroup.mk' (centralizer (U : Set G))
  apply centralizer_commutator_eq_of_coreFree_image U q
    (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _) hU.quotient_pCore_eq_bot
  rw [map_pResidual_of_surjective 2 q (QuotientGroup.mk'_surjective _)]
  exact centralizer_pResidual_le_of_pCore_eq_bot hU.quotient_pCore_eq_bot

theorem IsPReduced.moved
    (U : Subgroup G) [U.Normal] [IsElementaryAbelian 2 U] (hU : IsPReduced 2 U) :
    IsPReduced 2 (⁅U,pResidual 2 G⁆ : Subgroup G) := by
  refine ⟨inferInstance,IsElementaryAbelian.of_le (commutator_le_left U _),?_⟩
  let e := QuotientGroup.quotientMulEquivOfEq (hU.centralizer_moved_eq U)
  apply (map_eq_bot_iff_of_injective _ (f := e.toMonoidHom) e.injective).mp
  rw [pCore_map_iso 2 e]
  exact hU.quotient_pCore_eq_bot
end Theory.GroupTheory
