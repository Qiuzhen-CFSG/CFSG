module

public import Mathlib.GroupTheory.Subgroup.Centralizer

/-!
# Centralizing conjugates through a fused intersection

Suppose the normalizer of V controls fusion to z inside V, and every
conjugate of V containing z centralizes V. Then any conjugate whose
intersection with V meets the class of z centralizes V. Conjugate the
intersection point to z by an element normalizing V and transport the
commutation relation back.

This is the fusion transport in Aschbacher--Smith, combined manuscript
(1 March 2004), Lemma 8.3.13, printed p.727. Left conjugation is used
throughout; inversion of the conjugator gives the source convention.
-/

namespace Subgroup

variable {G : Type*} [Group G]

/-- Fusion controlled by N(V) transports a centralization assertion at z
to every intersection point in its ambient conjugacy class. -/
public theorem conjugate_le_centralizer_of_fused_intersection
    (V : Subgroup G) (z : G)
    (hcontrol : ∀ x ∈ V, IsConj x z →
      ∃ m ∈ normalizer (V : Set G), (MulAut.conj m) x = z)
    (hpoint : ∀ g : G, z ∈ V.map (MulAut.conj g).toMonoidHom →
      V.map (MulAut.conj g).toMonoidHom ≤ centralizer (V : Set G))
    (g x : G) (hxV : x ∈ V)
    (hxg : x ∈ V.map (MulAut.conj g).toMonoidHom) (hxz : IsConj x z) :
    V.map (MulAut.conj g).toMonoidHom ≤ centralizer (V : Set G) := by
  obtain ⟨m, hm, hmx⟩ := hcontrol x hxV hxz
  have hVV := mem_normalizer_iff_map_conj_eq.mp hm
  have hcompose : (V.map (MulAut.conj g).toMonoidHom).map
      (MulAut.conj m).toMonoidHom = V.map (MulAut.conj (m * g)).toMonoidHom := by
    rw [map_map]
    congr 1
    ext v
    simp [MulAut.conj_apply, mul_assoc]
  have hz : z ∈ V.map (MulAut.conj (m * g)).toMonoidHom := by
    rw [← hcompose, ← hmx]
    exact mem_map_of_mem _ hxg
  have hc := hpoint (m * g) hz
  rw [← hcompose] at hc
  intro w hw
  apply mem_centralizer_iff.mpr
  intro v hv
  apply (MulAut.conj m).injective
  simpa only [map_mul, MulEquiv.coe_toMonoidHom] using
    mem_centralizer_iff.mp (hc (mem_map_of_mem _ hw)) ((MulAut.conj m) v)
      (hVV.le (mem_map_of_mem _ hv))

end Subgroup
