module

public import Theory.Representation.PrimeFixedPointCentralization.Defs
public import Mathlib.GroupTheory.GroupAction.ConjAct
public import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic

/-!
# From semidirect fixed vectors to relative centralization

If a prime-order element does not centralize a normal subgroup of different
prime-power order, its conjugation action is faithful. The two subgroups have
trivial intersection, so their semidirect product embeds in the actual ambient
group. A faithful representation therefore stays faithful on this product.
A nonzero actor-fixed vector contradicts the original fixed-point-free action.

This supplies the subgroup transport in Aschbacher, *Finite Group Theory*,
36.2, printed p.194. The fixed-vector premise is explicit until the minimal
counterexample argument has been supplied.
-/

universe u
namespace Representation.PrimeFixedPointCentralization

/-- A faithful binary representation transfers the semidirect-product
fixed-vector theorem to centralization inside its own ambient group. -/
public theorem commute_of_prime_action_fixed_vectors
    {q r : ℕ} [Fact q.Prime] [Fact r.Prime] (hqr : q ≠ r)
    (hfixed : PrimeActionFixedVectorStatement.{u} q r)
    {G W : Type u} [Group G] [Finite G]
    [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]
    (ρ : Representation (ZMod 2) G W) (hfaith : Function.Injective ρ)
    (N : Subgroup G) [N.Normal] (hN : IsPGroup q N)
    (x : G) (hx : orderOf x = r)
    (hfree : ∀ v : W, ρ x v = v → v = 0) (z : N) : Commute x (z : G) := by
  classical
  by_contra hcomm
  let A := Subgroup.zpowers x
  have hA : Nat.card A = r := (Nat.card_zpowers x).trans hx
  let φ : A →* MulAut N := (MulAut.conjNormal : G →* MulAut N).comp A.subtype
  have hφ : Function.Injective φ := by
    apply (MonoidHom.ker_eq_bot_iff φ).mp
    let : Fact (Nat.card A).Prime := ⟨hA ▸ (Fact.out : r.Prime)⟩
    rcases φ.ker.eq_bot_or_eq_top_of_prime_card with hk | hk
    · exact hk
    · exfalso
      apply hcomm
      have hxker : (⟨x, Subgroup.mem_zpowers x⟩ : A) ∈ φ.ker := hk ▸ Subgroup.mem_top _
      have he := DFunLike.congr_fun (show φ ⟨x, Subgroup.mem_zpowers x⟩ = 1 from hxker) z
      have he' : x * (z : G) * x⁻¹ = z := congrArg Subtype.val he
      exact mul_inv_eq_iff_eq_mul.mp he'
  have hNA : Disjoint N A :=
    IsPGroup.disjoint_of_ne q r hqr N A hN (IsPGroup.of_card (n := 1) (by simpa using hA))
  let f : SemidirectProduct N A φ →* G :=
    SemidirectProduct.lift N.subtype A.subtype (by intro a; ext n; rfl)
  have hf : Function.Injective f := by
    intro a b hab
    apply SemidirectProduct.equivProd.injective
    exact Subgroup.mul_injective_of_disjoint hNA hab
  obtain ⟨v, hv, hvA⟩ := hfixed N A W hN hA φ hφ (ρ.comp f) (hfaith.comp hf)
  exact hv (hfree v (by simpa [f] using hvA ⟨x, Subgroup.mem_zpowers x⟩))

end Representation.PrimeFixedPointCentralization
