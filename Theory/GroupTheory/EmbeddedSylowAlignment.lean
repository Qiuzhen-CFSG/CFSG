module

public import Mathlib.GroupTheory.Sylow

/-!
# Aligning a Sylow while retaining an embedded component

An equivalence of whole overgroups and a compatible equivalence of their
embedded subgroups can be adjusted by the same inner conjugation. Sylow
conjugacy in the component then sends any supplied Sylow to the chosen model
Sylow. The compatibility square is retained pointwise, so this works equally
for split and nonsplit extensions.

Source: Sylow conjugacy; the compatible Borel marking used in
Aschbacher–Smith, proof of 13.6.6, printed p.927.
-/

public section
open Subgroup
namespace Theory.GroupTheory.EmbeddedSylowAlignment

variable {G H M : Type*} [Group G] [Group H] [Group M]
variable [Finite G] [Finite M] {p : ℕ} [Fact p.Prime]

/-- Adjust the whole-overgroup marking by an element of the model component.
The original component inclusion is retained in the displayed square. -/
theorem exists_compatible_marking (K J : Subgroup G) (hKJ : K ≤ J)
    (i : M →* H) (e : J ≃* H) (k : K ≃* M)
    (hcompat : ∀ x : K, e ⟨x.val, hKJ x.property⟩ = i (k x))
    (P : Sylow p K) (Q : Sylow p M) :
    ∃ (m : M) (e' : J ≃* H) (k' : K ≃* M),
      e' = e.trans (MulAut.conj (i m)) ∧
      k' = k.trans (MulAut.conj m) ∧
      (∀ x : K, e' ⟨x.val, hKJ x.property⟩ = i (k' x)) ∧
      (P : Subgroup K).map k'.toMonoidHom = Q ∧
      (((P : Subgroup K).map K.subtype).subgroupOf J).map e'.toMonoidHom =
        (Q : Subgroup M).map i := by
  obtain ⟨m, hm⟩ := MulAction.exists_smul_eq M
    (P.mapSurjective (f := k.toMonoidHom) k.surjective) Q
  let e' := e.trans (MulAut.conj (i m))
  let k' := k.trans (MulAut.conj m)
  have hs : (P : Subgroup K).map k'.toMonoidHom = Q := by
    have hh := congrArg (fun R : Sylow p M => (R : Subgroup M)) hm
    change ((P : Subgroup K).map k.toMonoidHom).map
      (MulAut.conj m).toMonoidHom = Q at hh
    have hk' : k'.toMonoidHom =
        (MulAut.conj m).toMonoidHom.comp k.toMonoidHom := by
      ext x
      rfl
    rw [hk', ← Subgroup.map_map]
    exact hh
  have hc (x : K) : e' ⟨x.val, hKJ x.property⟩ = i (k' x) := by
    change i m * e ⟨x.val, hKJ x.property⟩ * (i m)⁻¹ = i (m * k x * m⁻¹)
    rw [hcompat, map_mul, map_mul, map_inv]
  refine ⟨m, e', k', rfl, rfl, hc, hs, ?_⟩
  rw [← hs, Subgroup.map_map]
  ext y
  constructor
  · rintro ⟨x, ⟨z, hz, hzx⟩, rfl⟩
    refine ⟨z, hz, ?_⟩
    change i (k' z) = e' x
    rw [← hc]
    exact congrArg e' (Subtype.ext hzx)
  · rintro ⟨z, hz, rfl⟩
    refine ⟨⟨z.val, hKJ z.property⟩, ⟨z, hz, rfl⟩, hc z⟩

end Theory.GroupTheory.EmbeddedSylowAlignment
