module
public import Theory.GroupAction.FixedQuotientCentralizer
public import Mathlib.GroupTheory.Commutator.Basic

/-!
# Restriction of a fixed-kernel model to its commutator subgroup

If one actor has surjective displacement, every coefficient is represented by
a commutator. Restricting the coefficient map therefore retains the same
quotient model and actor. The source application is the natural binary SL₃
module on the moved center in Aschbacher--Smith 13.6.22.
-/

public section
namespace Representation.ConjugationQuotientModel
open Subgroup
variable {G A V : Type*} [Group G] [Group A] [AddCommGroup V] [Module (ZMod 2) V]
  {K U : Subgroup G} {ρ : Representation (ZMod 2) A V}
@[expose] def moved (m : ConjugationQuotientModel K U ρ)
    (hf : Function.Surjective m.actor)
    (hm : ∃ g : A, Function.Surjective (fun v => ρ g v - v)) :
    ConjugationQuotientModel K ⁅U,K⁆ ρ := by
  have hle : ⁅U,K⁆ ≤ U := le_normalizer_iff_commutator_le_left.mp m.normalizes
  let q := m.quotient.comp (inclusion hle)
  refine { normalizes := normalizer_commutator_ge_right U K
           actor := m.actor
           quotient := q
           surjective := ?_
           kernel := ?_
           equivariant := ?_ }
  · intro w
    obtain ⟨g,hg⟩ := hm
    obtain ⟨v,hv⟩ := hg w.toAdd
    obtain ⟨u,hu⟩ := m.surjective (Multiplicative.ofAdd v)
    obtain ⟨k,hk⟩ := hf g
    let u' := U.normalizerMonoidHom ⟨k,m.normalizes k.property⟩ u
    have he : (u' : G) * (u : G)⁻¹ ∈ ⁅U,K⁆ := by
      rw [commutator_comm]
      exact commutator_mem_commutator k.property u.property
    refine ⟨⟨(u' : G) * (u : G)⁻¹,he⟩,?_⟩
    change m.quotient (u' * u⁻¹) = w
    rw [map_mul,map_inv]
    apply Multiplicative.toAdd.injective
    simp only [toAdd_mul, toAdd_inv, ← sub_eq_add_neg]
    rw [show (m.quotient u').toAdd = ρ (m.actor k) (m.quotient u).toAdd from
      congrArg Multiplicative.toAdd (m.equivariant k u), hk, hu]
    exact hv
  · ext x
    change inclusion hle x ∈ m.quotient.ker ↔ _
    rw [m.kernel]
    rfl
  · intro k x
    exact m.equivariant k (inclusion hle x)

@[simp] theorem moved_actor (m : ConjugationQuotientModel K U ρ)
    (hf : Function.Surjective m.actor)
    (hm : ∃ g : A, Function.Surjective (fun v => ρ g v - v)) :
    (m.moved hf hm).actor = m.actor := rfl
end Representation.ConjugationQuotientModel
