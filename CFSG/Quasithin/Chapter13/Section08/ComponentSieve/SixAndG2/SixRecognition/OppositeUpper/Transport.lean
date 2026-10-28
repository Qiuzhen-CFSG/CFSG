module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.SixAndG2.SixRecognition.Strict
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.SixAndG2.NaturalSix.Extensions

/-!
# Moving both marked actions by the same source conjugator

The conjugator taking the critical actor at γ to the actor at α must also
move the lower section's projection and the upper quotient map. Precomposing
both projections by their original actions does this without changing either
module. The resulting actor marking is `f ∘ conj h` in both actions.

The strong-offender calculation applies to a genuine subquotient and, when
its image contains A₆, also forces the actor map to be onto S₆. This supplies
the actor equivalence needed by the independent permutation-quotient step.

Source: Aschbacher–Smith 13.8.26, printed p.962, and B.3.4(2)(i).
-/

@[expose] public section

open Representation Representation.BinaryOffender Subgroup
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.SixAndG2.SixRecognition
open NaturalSix

variable {J E F : Type*} [Group J]
  [AddCommGroup E] [Module (ZMod 2) E]
  [AddCommGroup F] [Module (ZMod 2) F]

private theorem move_action {X : Type*} [AddCommGroup X] [Module (ZMod 2) X]
    (ρ : Representation (ZMod 2) J X) (h a : J) (v : X) :
    ρ h (ρ a v) = ρ (MulAut.conj h a) (ρ h v) := by
  simp only [MulAut.conj_apply, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel_right]

namespace NaturalSection

/-- Relabel the six letters, transporting the natural projection by the
same permutation. This does not apply the exceptional outer automorphism. -/
def relabel {σ : Representation (ZMod 2) J E}
    (m : NaturalSection σ) (g : Symmetric) : NaturalSection σ where
  actor := (MulAut.conj g).toMonoidHom.comp m.actor
  injective := (MulAut.conj g).injective.comp m.injective
  space := m.space
  projection := (symmetricAction g).comp m.projection
  surjective := (symmetricAction.apply_bijective g).surjective.comp m.surjective
  intertwines a v := by
    change symmetricAction g (m.projection (m.space.toRepresentation a v)) = _
    rw [m.intertwines, move_action]
    rfl

/-- Change the actor marking by the specified inner automorphism, moving the
projection by the action of that same element. -/
def conjugateMarking {σ : Representation (ZMod 2) J E}
    (m : NaturalSection σ) (h : J) : NaturalSection σ where
  actor := m.actor.comp (MulAut.conj h).toMonoidHom
  injective := m.injective.comp (MulAut.conj h).injective
  space := m.space
  projection := m.projection.comp (m.space.toRepresentation h)
  surjective := m.surjective.comp (m.space.toRepresentation.apply_bijective h).surjective
  intertwines a v := by
    change m.projection (m.space.toRepresentation h (m.space.toRepresentation a v)) = _
    rw [move_action, m.intertwines]
    rfl

theorem conjugateMarking_actor_map {σ : Representation (ZMod 2) J E}
    (m : NaturalSection σ) (h : J) (A : Subgroup J) :
    A.map (m.conjugateMarking h).actor =
      (A.map (MulAut.conj h).toMonoidHom).map m.actor := (map_map _ _ _).symm

variable [FiniteDimensional (ZMod 2) E]

/-- A strong offender stays strong on the faithful natural subquotient. -/
theorem strong_image {σ : Representation (ZMod 2) J E}
    (m : NaturalSection σ) {B : Subgroup J} (hB : IsStrongOffender σ B) :
    IsStrongOffender symmetricAction (B.map m.actor) := by
  let : IsElementaryAbelian 2 B := hB.1.2
  refine ⟨⟨fun hb => hB.1.1
    ((Subgroup.map_eq_bot_iff_of_injective B m.injective).mp hb),
    IsElementaryAbelian.map m.actor⟩, ?_⟩
  rw [rank_map_injective m.actor m.injective]
  exact (m.fixedCodim_le B).trans_lt hB.2

/-- In the source Sylow marking the strong actor is the distinguished cube. -/
theorem strong_image_eq_cube {σ : Representation (ZMod 2) J E}
    (m : NaturalSection σ) {A B : Subgroup J} (hBA : B ≤ A)
    (hB : IsStrongOffender σ B)
    (hT : A.map m.actor ≤ ChapterB.Offenders.Six.sylowCarrier) :
    B.map m.actor = Theory.SpecificGroups.SymmetricSix.BinaryFlags.D :=
  Marked.strong_in_sylow_eq_D (m.strong_image hB) ((map_mono hBA).trans hT)

/-- A natural actor containing A₆ becomes all of S₆ in the strong branch;
the equivalence has exactly the original actor map. -/
theorem symmetric_of_strong {σ : Representation (ZMod 2) J E}
    (m : NaturalSection σ) (ha : alternatingGroup (Fin 6) ≤ m.actor.range)
    {B : Subgroup J} (hB : IsStrongOffender σ B) :
    ∃ e : J ≃* Symmetric, ∀ a, e a = m.actor a := by
  rcases extension_equiv_of_embedding m.actor m.injective ha with ⟨e, he⟩ | he
  · exfalso
    obtain ⟨g, hg⟩ := (Marked.strong_iff _).mp (m.strong_image hB)
    have hm : MulAut.conj g Theory.SpecificGroups.SymmetricSix.BinaryFlags.swap01 ∈
        B.map m.actor := by
      rw [hg]
      exact mem_map_of_mem _ Theory.SpecificGroups.SymmetricSix.BinaryFlags.swap01_mem_D
    obtain ⟨a, _, hx⟩ := hm
    have hn : MulAut.conj g Theory.SpecificGroups.SymmetricSix.BinaryFlags.swap01 ∈
        alternatingGroup (Fin 6) := hx ▸ (he a ▸ (e a).property)
    have ht : Theory.SpecificGroups.SymmetricSix.BinaryFlags.swap01 ∈
        alternatingGroup (Fin 6) := by
      have := (inferInstance : (alternatingGroup (Fin 6)).Normal).conj_mem _ hn g⁻¹
      simpa only [MulAut.conj_apply, inv_inv, mul_assoc, inv_mul_cancel_left,
        inv_mul_cancel, mul_one] using this
    exact (by decide : Theory.SpecificGroups.SymmetricSix.BinaryFlags.swap01 ∉
      alternatingGroup (Fin 6)) ht
  · exact he

/-- Once the strong branch forces S₆, Sylow conjugacy supplies a natural
section whose marking carries the prescribed source Sylow to the canonical
one. In particular no order-sixteen marking is assumed in the A₆ case. -/
theorem exists_sylow_marking {σ : Representation (ZMod 2) J E}
    (m : NaturalSection σ) (ha : alternatingGroup (Fin 6) ≤ m.actor.range)
    (T : Sylow 2 J) {B : Subgroup J} (hB : IsStrongOffender σ B) :
    ∃ n : NaturalSection σ, Function.Surjective n.actor ∧
      (T : Subgroup J).map n.actor = ChapterB.Offenders.Six.sylowCarrier := by
  obtain ⟨e, he⟩ := m.symmetric_of_strong ha hB
  let : Finite J := Finite.of_equiv Symmetric e.symm.toEquiv
  have hf : Function.Surjective m.actor := by
    intro x
    obtain ⟨a, rfl⟩ := e.surjective x
    exact ⟨a, (he a).symm⟩
  let U : Sylow 2 Symmetric := T.mapSurjective hf
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq Symmetric U ChapterB.Offenders.Six.sylow
  refine ⟨m.relabel g, (MulAut.conj g).surjective.comp hf, ?_⟩
  change (T : Subgroup J).map ((MulAut.conj g).toMonoidHom.comp m.actor) = _
  rw [← map_map]
  exact congrArg (fun Q : Sylow 2 Symmetric => (Q : Subgroup Symmetric)) hg

end NaturalSection

namespace OppositeUpper
variable {σ : Representation (ZMod 2) J E}

/-- Assemble the witness at γ from the quotient constructed in the marking
at α. Both maps use the given conjugator, including in the opposite action. -/
def of_conjugate_quotient (m : NaturalSection σ)
    (τ : Representation (ZMod 2) J F) (A : Subgroup J) (h : J)
    (hT : (A.map (MulAut.conj h).toMonoidHom).map m.actor ≤
      ChapterB.Offenders.Six.sylowCarrier)
    (q : F →ₗ[ZMod 2] Natural) (hq : Function.Surjective q)
    (he : ∀ a v, q (τ a v) = Marked.oppositeAction (m.actor a) (q v)) :
    OppositeUpper σ τ A where
  lower := m.conjugateMarking h
  sylow := by rw [m.conjugateMarking_actor_map]; exact hT
  upper := q.comp (τ h)
  surjective := hq.comp (τ.apply_bijective h).surjective
  intertwines a v := by
    change q (τ h (τ a v)) = _
    rw [move_action, he]
    rfl

/-- The conjugated construction is consumed by the existing cube exclusion. -/
theorem no_strong_of_conjugate_quotient [FiniteDimensional (ZMod 2) E]
    (m : NaturalSection σ) (τ : Representation (ZMod 2) J F)
    (A : Subgroup J) (h : J) (hquad : IsQuadratic τ A)
    (hT : (A.map (MulAut.conj h).toMonoidHom).map m.actor ≤
      ChapterB.Offenders.Six.sylowCarrier)
    (q : F →ₗ[ZMod 2] Natural) (hq : Function.Surjective q)
    (he : ∀ a v, q (τ a v) = Marked.oppositeAction (m.actor a) (q v)) :
    ¬ ∃ B ≤ A, IsStrongOffender σ B := by
  let o := of_conjugate_quotient m τ A h hT q hq he
  exact no_strong_of_opposite_quotient _ o.lower τ A hquad o.sylow o.upper
    o.surjective o.intertwines

end OppositeUpper
end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.SixAndG2.SixRecognition
end
