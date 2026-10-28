module

public import Theory.GroupTheory.SaturatedCentralizerTransport

/-!
# Fusion controlled by a common Sylow centralizer

Suppose S is a Sylow p-subgroup of C_G(x), and its ambient image also
centralizes a conjugate y of x. Sylow conjugacy inside C_G(x) adjusts an
ambient conjugator from y to x so that it normalizes the image of S.
Cardinality turns the resulting subgroup containment into equality. Inverting
the conjugator gives the requested orientation from x to y.

This is the Burnside fusion step in GLS IV, Chapter 2, Lemma 16.4(c).
The subgroup need only be Sylow in the element centralizer.
-/

namespace Subgroup
open Subgroup

/-- Ambient fusion between two elements centralized by the image of a Sylow
of one element centralizer is realized in that image's normalizer. -/
public theorem exists_normalizer_conjugator_of_centralizer_sylow
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (x y : G) (S : Sylow p (centralizer ({x} : Set G)))
    (hy : (S : Subgroup (centralizer ({x} : Set G))).map
      (centralizer ({x} : Set G)).subtype ≤ centralizer ({y} : Set G))
    (hxy : IsConj x y) :
    ∃ g ∈ normalizer ((S : Subgroup (centralizer ({x} : Set G))).map
      (centralizer ({x} : Set G)).subtype : Set G), MulAut.conj g x = y := by
  let C := centralizer ({x} : Set G)
  let T := (S : Subgroup C).map C.subtype
  have hTC : T ≤ C := map_subtype_le _
  have hT : IsPGroup p T := S.isPGroup'.map C.subtype
  have hmax (V : Subgroup G) (hpV : IsPGroup p V) (hTV : T ≤ V) (hVC : V ≤ C) : V = T := by
    have hSV : (S : Subgroup C) ≤ V.subgroupOf C := by
      intro a ha
      exact hTV (mem_map_of_mem C.subtype ha)
    have he : V.subgroupOf C = (S : Subgroup C) :=
      S.is_maximal' (hpV.comap_subtype) hSV
    have hh := congrArg (Subgroup.map C.subtype) he
    rw [map_subgroupOf_eq_of_le hVC] at hh
    exact hh
  obtain ⟨g, hg, hmap⟩ := exists_conj_into_saturated_centralizer x y T T
    hT hT hTC hy hmax hxy.symm
  have heq : T.map (MulAut.conj g).toMonoidHom = T :=
    eq_of_le_of_card_ge hmap (card_map_of_injective
      (K := T) (f := (MulAut.conj g).toMonoidHom) (MulAut.conj g).injective).ge
  have hgN : g ∈ normalizer (T : Set G) := mem_normalizer_iff_map_conj_eq.mpr heq
  refine ⟨g⁻¹, (normalizer (T : Set G)).inv_mem hgN, ?_⟩
  apply (MulAut.conj g).injective
  simpa only [MulAut.conj_apply, inv_inv, mul_assoc, inv_mul_cancel_left,
    mul_inv_cancel_right, mul_inv_cancel, mul_one, mul_inv_cancel_left] using hg.symm

end Subgroup
