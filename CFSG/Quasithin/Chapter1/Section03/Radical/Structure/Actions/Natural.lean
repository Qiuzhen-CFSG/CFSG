module

public import CFSG.Quasithin.Chapter1.Section03.Radical.Structure.Actions.Natural.Matrix
public import CFSG.Quasithin.Chapter1.Section03.Radical.Structure.Actions.Natural.Coordinates

/-!
# The natural radical action restricted to a Sylow two-subgroup

The actual quotient map from A.3.6(3) sends a Sylow two-subgroup of K onto a
Sylow two-subgroup of SL₂(p). The matrix quaternion subgroup proves both
irreducibility on the natural plane and an injective quaternion subgroup in
the faithful natural-action image. The equivariant omega–Frattini coordinates
transport both conclusions to the original conjugation action.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, A.3.6(3),
pp.43–45, the proof of 1.3.3 on p.509, and the quaternion action on p.513.
No Ξ-membership or additional action hypothesis is used.
-/

@[expose] public section

open Subgroup Theory.GroupTheory
open CFSG.Quasithin.Chapter1.Section02
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter1.RadicalActions
variable {K : Type*} [Group K] [Finite K] {p : ℕ} [Fact p.Prime]

/-- Both action clauses for the natural alternative, on the actual omega–Frattini quotient. -/
theorem natural_sylow_actions (h : A36Natural K)
    (hp : p ∣ Nat.card (fittingSubgroup K)) (S : Sylow 2 K) :
    (∀ A : Subgroup (omegaCore p K ⧸ frattini (omegaCore p K)),
      (∀ (s : S) x, x ∈ A → omegaFrattiniAction p K s x ∈ A) → A = ⊥ ∨ A = ⊤) ∧
    ∃ f : QuaternionGroup 2 →*
        ((omegaFrattiniAction p K).comp (S : Subgroup K).subtype).range,
      Function.Injective f := by
  obtain ⟨F, hField, hFin, hcard, e, q, hq, he⟩ := natural_coordinates h hp
  have hp3 := (RadicalStructure.natural_core h hp).1
  let S' : Sylow 2 SL(2,F) := S.mapSurjective hq
  let ρ := (omegaFrattiniAction p K).comp (S : Subgroup K).subtype
  constructor
  · intro A hA
    have hB : ∀ (g : S') x, x ∈ A.map e.toMonoidHom →
        Matrix.SL2.naturalAction F g x ∈ A.map e.toMonoidHom := by
      intro g x hx
      obtain ⟨s, hs, hsg⟩ := g.property
      obtain ⟨a, ha, rfl⟩ := hx
      refine ⟨omegaFrattiniAction p K s a, hA ⟨s, hs⟩ a ha, ?_⟩
      change e (omegaFrattiniAction p K s a) = Matrix.SL2.naturalAction F g (e a)
      rw [he, hsg]
    rcases Natural.sylow_irreducible (by omega : 2 < p) hcard S'
        (A.map e.toMonoidHom) hB with hb | ht
    · exact Or.inl ((A.map_eq_bot_iff_of_injective e.injective).mp hb)
    · right
      apply Subgroup.map_injective (f := e.toMonoidHom) e.injective
      rw [map_top_of_surjective e.toMonoidHom e.surjective]
      exact ht
  · obtain ⟨f₀, hf₀, _⟩ := Natural.sylow_quaternion (by omega : 2 < p) hcard S'
    let c := MulAut.congr e
    let f : QuaternionGroup 2 →* MulAut (omegaCore p K ⧸ frattini (omegaCore p K)) :=
      c.symm.toMonoidHom.comp
        (((Matrix.SL2.naturalAction F).comp (S' : Subgroup SL(2,F)).subtype).comp f₀)
    have hf : Function.Injective f :=
      c.symm.injective.comp ((Matrix.SL2.naturalAction_injective F).comp
        ((S' : Subgroup SL(2,F)).subtype_injective.comp hf₀))
    have hm (x : QuaternionGroup 2) : f x ∈ ρ.range := by
      obtain ⟨s, hs, hsq⟩ := (f₀ x).property
      refine ⟨⟨s, hs⟩, ?_⟩
      apply c.injective
      change c (omegaFrattiniAction p K s) =
        c (c.symm (Matrix.SL2.naturalAction F (f₀ x)))
      rw [c.apply_symm_apply]
      ext v : 1
      change e (omegaFrattiniAction p K s (e.symm v)) =
        Matrix.SL2.naturalAction F (f₀ x) v
      rw [he, e.apply_symm_apply, hsq]
    exact ⟨f.codRestrict ρ.range hm, fun x y heq => hf (congrArg Subtype.val heq)⟩

/-- The Sylow two-subgroup is irreducible on the actual radical omega–Frattini quotient. -/
theorem natural_sylow_irreducible (h : A36Natural K)
    (hp : p ∣ Nat.card (fittingSubgroup K)) (S : Sylow 2 K)
    (A : Subgroup (omegaCore p K ⧸ frattini (omegaCore p K)))
    (hA : ∀ (s : S) x, x ∈ A → omegaFrattiniAction p K s x ∈ A) : A = ⊥ ∨ A = ⊤ :=
  (natural_sylow_actions h hp S).1 A hA

/-- The actual Sylow action image contains an injective copy of Q₈. -/
theorem natural_sylow_quaternion (h : A36Natural K)
    (hp : p ∣ Nat.card (fittingSubgroup K)) (S : Sylow 2 K) :
    ∃ f : QuaternionGroup 2 →*
        ((omegaFrattiniAction p K).comp (S : Subgroup K).subtype).range,
      Function.Injective f :=
  (natural_sylow_actions h hp S).2

end CFSG.Quasithin.Chapter1.RadicalActions
