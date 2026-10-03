module

public import Mathlib.GroupTheory.PGroup
public import Mathlib.GroupTheory.Subgroup.Centralizer

/-!
# Transporting local centralizer control

The property that every two-subgroup containing a subgroup A and centralizing
one of its nonidentity elements centralizes all of A is invariant under group
isomorphisms. Pull the two-subgroup back along the isomorphism and transport
the resulting commutation identities forward.

This supplies conjugation transport for the local conclusion of
Janko–Thompson, Math. Z. 113 (1970), Lemma 5.1, p.394.
-/

open Subgroup

namespace Subgroup

/-- Transport two-subgroup centralizer control along a group isomorphism. -/
public theorem centralizes_map_of_two_subgroup_control
    {G H : Type*} [Group G] [Group H]
    (A : Subgroup G)
    (hcontrol : ∀ w : G, w ∈ A → w ≠ 1 →
      ∀ Q : Subgroup G, IsPGroup 2 Q → A ≤ Q →
        Q ≤ centralizer ({w} : Set G) → Q ≤ centralizer (A : Set G))
    (e : G ≃* H) (w : H) (hw : w ∈ A.map e.toMonoidHom) (hw1 : w ≠ 1)
    (Q : Subgroup H) (hQ : IsPGroup 2 Q) (hAQ : A.map e.toMonoidHom ≤ Q)
    (hQC : Q ≤ centralizer ({w} : Set H)) :
    Q ≤ centralizer (A.map e.toMonoidHom : Set H) := by
  obtain ⟨v, hv, rfl⟩ := hw
  have hv1 : v ≠ 1 := by intro h; exact hw1 (by simp [h])
  let R := Q.comap e.toMonoidHom
  have hAR : A ≤ R := by
    intro a ha
    exact hAQ (mem_map_of_mem e.toMonoidHom ha)
  have hRC : R ≤ centralizer ({v} : Set G) := by
    intro r hr
    apply mem_centralizer_singleton_iff.mpr
    apply e.injective
    have hh := mem_centralizer_singleton_iff.mp (hQC hr)
    change e r * e v = e v * e r at hh
    simpa only [map_mul] using hh
  have hlocal := hcontrol v hv hv1 R
    (hQ.comap_of_injective e.toMonoidHom e.injective) hAR hRC
  intro q hq a ha
  obtain ⟨b, hb, rfl⟩ := ha
  have hr : e.symm q ∈ R := by
    change e (e.symm q) ∈ Q
    simpa only [e.apply_symm_apply] using hq
  have he := congrArg e (hlocal hr b hb)
  change e b * q = q * e b
  simpa only [map_mul, e.apply_symm_apply] using he

end Subgroup
