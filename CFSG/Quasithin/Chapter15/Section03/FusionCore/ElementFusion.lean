module

public import CFSG.Quasithin.Chapter15.Section03.Constructions
public import Theory.GroupTheory.ElementFusionTransport

/-!
# Fusion separation in the orthogonal local configuration

The two orbits on the nonidentity elements of the natural orthogonal
four-space have representatives with different Sylow-centrality. Transporting
an ambient Sylow group into a centralizer proves they cannot fuse. Correcting
conjugators inside the normalizer then proves uniqueness of a conjugate
containing a vector whose full centralizer lies in that normalizer.

These are the group-theoretic implications in Lemma 15.3.46(1–2). The natural
module must supply its two orbits and the local Sylow orders; 15.3.45 supplies
the full-centralizer containment. None of those inputs is asserted here.
Conjugation is on the left, so replace a source right-conjugator by its inverse.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), printed p.1141.
-/

@[expose] public section

open Subgroup
open scoped Pointwise

namespace CFSG.Quasithin.Chapter15.Section03.FusionCore

variable {G : Type*} [Group G]

/-- Conjugacy by an element of the indicated subgroup. -/
def ConjugateBy (M : Subgroup G) (x y : G) : Prop :=
  ∃ m ∈ M, MulAut.conj m x = y

theorem ConjugateBy.refl (M : Subgroup G) (x : G) : ConjugateBy M x x :=
  ⟨1, M.one_mem, by simp⟩

theorem ConjugateBy.symm {M : Subgroup G} {x y : G}
    (h : ConjugateBy M x y) : ConjugateBy M y x := by
  obtain ⟨m, hm, rfl⟩ := h
  exact ⟨m⁻¹, M.inv_mem hm, by simp [MulAut.conj_apply, mul_assoc]⟩

theorem ConjugateBy.trans {M : Subgroup G} {x y z : G}
    (hxy : ConjugateBy M x y) (hyz : ConjugateBy M y z) : ConjugateBy M x z := by
  obtain ⟨a, ha, rfl⟩ := hxy
  obtain ⟨b, hb, rfl⟩ := hyz
  exact ⟨b * a, M.mul_mem hb ha, by simp [MulAut.conj_apply, mul_assoc]⟩

theorem ConjugateBy.isConj {M : Subgroup G} {x y : G}
    (h : ConjugateBy M x y) : IsConj x y := by
  obtain ⟨m, _, hm⟩ := h
  exact isConj_iff.mpr ⟨m, hm⟩

/-- A Sylow-central element cannot fuse to an element whose centralizer has
a strictly smaller Sylow subgroup. The Sylow hypothesis is relative to the
full centralizer. -/
theorem not_isConj_of_smaller_centralizer_sylow [Finite G]
    (T : Sylow 2 G) (z v : G)
    (hTz : (T : Subgroup G) ≤ centralizer ({z} : Set G))
    (S : Sylow 2 (centralizer ({v} : Set G)))
    (hsmall : Nat.card S < Nat.card T) : ¬ IsConj z v := by
  intro hconj
  obtain ⟨a, ha⟩ := isConj_iff.mp hconj
  have hTa : (a • T : Sylow 2 G) ≤ centralizer ({v} : Set G) := by
    rintro x ⟨t, ht, rfl⟩
    apply mem_centralizer_singleton_iff.mpr
    change MulAut.conj a t * v = v * MulAut.conj a t
    change MulAut.conj a z = v at ha
    rw [← ha]
    simpa only [map_mul] using
      congrArg (MulAut.conj a) (mem_centralizer_singleton_iff.mp (hTz ht))
  let P := (a • T : Sylow 2 G).subtype hTa
  have hcard : Nat.card T = Nat.card S := by
    exact Nat.card_congr ((T.equivSMul a).trans
      ((subgroupOfEquivOfLe hTa).symm.trans (P.equiv S))).toEquiv
  omega

/-- Two local orbits remain distinct globally when their representatives
have different Sylow-centrality. This proves fusion control, rather than
assuming separation of the orbits. -/
theorem controlsFusion_of_two_orbits [Finite G]
    (M V : Subgroup G) (T : Sylow 2 G) (z v : G)
    (hTz : (T : Subgroup G) ≤ centralizer ({z} : Set G))
    (S : Sylow 2 (centralizer ({v} : Set G)))
    (hsmall : Nat.card S < Nat.card T)
    (horbits : ∀ x ∈ V, x ≠ 1 → ConjugateBy M z x ∨ ConjugateBy M v x) :
    ∀ x ∈ V, ∀ g : G, MulAut.conj g x ∈ V →
      ConjugateBy M x (MulAut.conj g x) := by
  have hsep := not_isConj_of_smaller_centralizer_sylow T z v hTz S hsmall
  intro x hx g hg
  by_cases hx1 : x = 1
  · subst x
    simpa using ConjugateBy.refl M (1 : G)
  have hg1 : MulAut.conj g x ≠ 1 := by
    exact fun h => hx1 ((MulAut.conj g).injective (h.trans (map_one _).symm))
  have hconj : IsConj x (MulAut.conj g x) := isConj_iff.mpr ⟨g, rfl⟩
  rcases horbits x hx hx1 with hz | hv <;>
    rcases horbits (MulAut.conj g x) hg hg1 with hzg | hvg
  · exact hz.symm.trans hzg
  · exact (hsep (hz.isConj.trans (hconj.trans hvg.isConj.symm))).elim
  · exact (hsep (hzg.isConj.trans (hconj.symm.trans hv.isConj.symm))).elim
  · exact hv.symm.trans hvg

/-- The centralizer correction of A.1.7 makes a conjugate containing the
specified element equal to `V`. -/
theorem conjugate_eq_of_fusion_of_centralizer_le
    {M V : Subgroup G} (hM : M = normalizer (V : Set G)) (x g : G)
    (hfusion : ∀ a : G, MulAut.conj a x ∈ V → ConjugateBy M x (MulAut.conj a x))
    (hcentral : centralizer ({x} : Set G) ≤ M)
    (hxg : x ∈ V.map (MulAut.conj g).toMonoidHom) :
    V.map (MulAut.conj g).toMonoidHom = V := by
  obtain ⟨c, hc⟩ := exists_centralizer_conjugator_of_element_fusion
    (fun a ha => by simpa only [ConjugateBy, hM] using hfusion a ha) hxg
  rw [← hc]
  exact mem_normalizer_iff_map_conj_eq.mp (hM ▸ hcentral c.property)

end CFSG.Quasithin.Chapter15.Section03.FusionCore
