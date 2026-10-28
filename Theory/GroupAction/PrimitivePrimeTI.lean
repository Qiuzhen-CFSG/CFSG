module
public import Theory.ElementaryAbelian.AutomorphismLinearEmbedding
public import Theory.ElementaryAbelian.Injective
public import Theory.Representation.BinaryPrimeDegree
public import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic

/-!
# Primitive-prime actors and trivial intersections

A prime-order actor with trivial fixed subgroup acts faithfully on every
nonzero invariant subgroup of an elementary abelian group. The binary
prime-degree bound makes that subgroup the whole group when the binary
order of the prime is the ambient dimension.

An irreducible subgroup is TI under the normalizer of its actor: the
intersection with a conjugate is invariant under the same actor.
The application uses the literal Cartan action in the odd-field argument
of Aschbacher–Smith 5.1.17, printed p.640 (refs/quasithin.pdf).
-/

public noncomputable section
open scoped IsMulCommutative
namespace Subgroup
variable {G : Type*} [Group G] [Finite G]

theorem primitive_prime_invariant_eq_bot_or_self
    (Z C : Subgroup G) [IsElementaryAbelian 2 Z]
    {p n : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hC : Nat.card C = p) (hord : orderOf (2 : ZMod p) = n)
    (hZ : Nat.card Z = 2 ^ n) (hfix : Z ⊓ centralizer (C : Set G) = ⊥)
    (X : Subgroup G) (hXZ : X ≤ Z) (hCX : C ≤ normalizer (X : Set G)) :
    X = ⊥ ∨ X = Z := by
  by_cases hx : X = ⊥
  · exact Or.inl hx
  right
  let : IsElementaryAbelian 2 X := IsElementaryAbelian.of_injective
    (inclusion hXZ) (inclusion_injective hXZ)
  let : Fact (Nat.card C).Prime := ⟨hC.symm ▸ hp⟩
  let f : C →* MulAut X := X.normalizerMonoidHom.comp (inclusion hCX)
  have hf : Function.Injective f := by
    apply (MonoidHom.ker_eq_bot_iff f).mp
    apply f.ker.eq_bot_or_eq_top_of_prime_card.resolve_right
    intro he
    apply hx
    apply bot_unique
    intro x hxx
    apply hfix.le
    refine ⟨hXZ hxx,?_⟩
    intro c hc
    have hm : (⟨c,hc⟩ : C) ∈ f.ker := he ▸ mem_top _
    have heq : f ⟨c,hc⟩ ⟨x,hxx⟩ = ⟨x,hxx⟩ := by
      rw [show f ⟨c,hc⟩ = 1 from hm]
      rfl
    have hh := congrArg Subtype.val heq
    change c*x*c⁻¹=x at hh
    exact mul_inv_eq_iff_eq_mul.mp hh
  obtain ⟨k,hk⟩ := (IsElementaryAbelian.isPGroup 2 X).exists_card_eq
  obtain ⟨e,he⟩ := IsElementaryAbelian.exists_injective_mulAut_generalLinear_of_card_le X hk.le
  have hdiv : p ∣ Nat.card (Matrix.GeneralLinearGroup (Fin k) (ZMod 2)) := by
    rw [←hC]
    exact card_dvd_of_injective (e.comp f) (he.comp hf)
  have hn : n ≤ k := hord ▸ Representation.BinaryPrimeDegree.orderOf_le_of_dvd_card_GL hp hp2 hdiv
  apply eq_of_le_of_card_ge hXZ
  rw [hk,hZ]
  exact Nat.pow_le_pow_right (by decide) hn

/-- An invariant subgroup with no proper nonzero invariant subgroups is TI
under the normalizer of its actor. -/
theorem ti_under_actor_normalizer
    (Z P : Subgroup G) (hPZ : P ≤ normalizer (Z : Set G))
    (hirr : ∀ X : Subgroup G, X ≤ Z → P ≤ normalizer (X : Set G) → X = ⊥ ∨ X = Z)
    {g : G} (hg : g ∈ normalizer (P : Set G)) :
    Z ⊓ Z.map (MulAut.conj g).toMonoidHom = ⊥ ∨
      Z.map (MulAut.conj g).toMonoidHom = Z := by
  have hPZg : P ≤ normalizer (Z.map (MulAut.conj g).toMonoidHom : Set G) := by
    rw [←map_equiv_normalizer_eq Z (MulAut.conj g)]
    have hm := map_mono (f := (MulAut.conj g).toMonoidHom) hPZ
    have he : P.map (MulAut.conj g).toMonoidHom = P := mem_normalizer_iff_map_conj_eq.mp hg
    rwa [he] at hm
  rcases hirr (Z ⊓ Z.map (MulAut.conj g).toMonoidHom) inf_le_left
    ((le_inf hPZ hPZg).trans inf_normalizer_le_normalizer_inf) with hz | he
  · exact Or.inl hz
  · right
    have hle : Z ≤ Z.map (MulAut.conj g).toMonoidHom := he.ge.trans inf_le_right
    exact (eq_of_le_of_card_ge hle (by rw [card_map_of_injective (MulAut.conj g).injective])).symm
end Subgroup
