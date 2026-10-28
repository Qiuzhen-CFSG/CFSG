module

public import Theory.ElementaryAbelian.VectorSpace
public import Mathlib.Algebra.Group.Equiv.TypeTags
public import Mathlib.FieldTheory.Finiteness
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs

/-!
# Matrix embeddings of elementary abelian automorphism groups

If an elementary abelian p-group E has order at most pⁿ, its full
multiplicative automorphism group embeds in GLₙ(p). Multiplicative
automorphisms are linear on Additive E. Extend each by the identity on
a complementary coordinate space and choose a basis of the resulting
n-dimensional space. This construction includes E = 1 and n = 0.

This is the vector-space step in Aschbacher–Smith, *The Classification of
Quasithin Groups*, A.1.25(2), printed p.25.
-/

open scoped IsMulCommutative

namespace IsElementaryAbelian

/-- Automorphisms of an elementary abelian group of order at most pⁿ
embed in the concrete n-dimensional matrix group over the prime field. -/
public theorem exists_injective_mulAut_generalLinear_of_card_le {p n : ℕ} [Fact p.Prime] (E : Type*) [Group E] [Finite E]
    [IsElementaryAbelian p E] (hcard : Nat.card E ≤ p ^ n) :
    ∃ f : MulAut E →* Matrix.GeneralLinearGroup (Fin n) (ZMod p),
      Function.Injective f := by
  classical
  have hdim : Module.finrank (ZMod p) (Additive E) ≤ n := by
    apply (Nat.pow_le_pow_iff_right (Fact.out : p.Prime).one_lt).mp
    have hc := Module.natCard_eq_pow_finrank (K := ZMod p) (V := Additive E)
    change Nat.card E = _ at hc
    simp only [Nat.card_zmod] at hc
    rwa [← hc]
  let V := Additive E × (Fin (n - Module.finrank (ZMod p) (Additive E)) → ZMod p)
  have hv : Module.finrank (ZMod p) V = n := by
    dsimp [V]
    rw [Module.finrank_prod, Module.finrank_pi, Fintype.card_fin]
    exact Nat.add_sub_of_le hdim
  let autLinear : MulAut E →* (Additive E ≃ₗ[ZMod p] Additive E) :=
    { toFun := fun a => { a.toAdditive with map_smul' := ZMod.map_smul a.toAdditive }
      map_one' := by ext; rfl
      map_mul' := by intros; ext; rfl }
  let pad : (Additive E ≃ₗ[ZMod p] Additive E) →* (V ≃ₗ[ZMod p] V) :=
    { toFun := fun a => a.prodCongr (LinearEquiv.refl _ _)
      map_one' := by ext <;> rfl
      map_mul' := by intros; ext <;> rfl }
  let b := Module.finBasisOfFinrankEq (ZMod p) V hv
  let e := (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod p) V).symm.trans
    (Matrix.GeneralLinearGroup.toLin' b).symm
  refine ⟨e.toMonoidHom.comp (pad.comp autLinear), ?_⟩
  apply e.injective.comp
  intro a c hac
  ext x
  exact congrArg (fun z : V ≃ₗ[ZMod p] V => (z (Additive.ofMul x, 0)).1) hac

end IsElementaryAbelian
