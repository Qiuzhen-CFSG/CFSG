module
public import Theory.SpecificGroups.Tits.MinimumIndex.ThirteenOvergroups.Seeds

/-!
# Pair generation is invariant under thirteen-normalizer double cosets

Right multiplication by the marked cyclic subgroup's normalizer preserves its
conjugate. Left multiplication conjugates the whole generated pair. Therefore a
finite double-coset cover and generation for its representatives suffice for
arbitrary pairs. The representative checks remain explicit here.

Conjugation is Lean's left conjugation. In particular, transferring a recovery
conjugator `g` across a left factor `a` gives `g * a⁻¹`.
Source: the actual ATLAS carrier and subgroup conventions in `Seeds`.
-/

namespace Tits.MinimumIndexThirteen.PairGeneration
open Subgroup

private theorem map_conj_comp (H : Subgroup Atlas1600Group) (a b : Atlas1600Group) :
    (H.map (MulAut.conj a).toMonoidHom).map (MulAut.conj b).toMonoidHom =
      H.map (MulAut.conj (b * a)).toMonoidHom := by
  rw [Subgroup.map_map]
  congr 1

public theorem pairSubgroup_mul_normalizer (x b : Atlas1600Group)
    (hb : b ∈ thirteenNormalizer) : pairSubgroup (x * b) = pairSubgroup x := by
  have hb' : thirteenSubgroup.map (MulAut.conj b).toMonoidHom = thirteenSubgroup :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp hb
  unfold pairSubgroup
  rw [← map_conj_comp, hb']

public theorem pairSubgroup_normalizer_mul (a x : Atlas1600Group)
    (ha : a ∈ thirteenNormalizer) :
    pairSubgroup (a * x) = (pairSubgroup x).map (MulAut.conj a).toMonoidHom := by
  have ha' : thirteenSubgroup.map (MulAut.conj a).toMonoidHom = thirteenSubgroup :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp ha
  simp only [pairSubgroup, Subgroup.map_sup, ha', map_conj_comp]

public theorem pairSubgroup_doubleCoset (a b x : Atlas1600Group)
    (ha : a ∈ thirteenNormalizer) (hb : b ∈ thirteenNormalizer) :
    pairSubgroup (a * x * b) = (pairSubgroup x).map (MulAut.conj a).toMonoidHom := by
  rw [pairSubgroup_mul_normalizer _ _ hb, pairSubgroup_normalizer_mul _ _ ha]

public theorem generation_of_doubleCoset {x r a b : Atlas1600Group}
    (ha : a ∈ thirteenNormalizer) (hb : b ∈ thirteenNormalizer)
    (hx : x = a * r * b)
    (hr : ∃ (i : Fin 3) (g : Atlas1600Group),
      candidateDerived i ≤ (pairSubgroup r).map (MulAut.conj g).toMonoidHom) :
    ∃ (i : Fin 3) (g : Atlas1600Group),
      candidateDerived i ≤ (pairSubgroup x).map (MulAut.conj g).toMonoidHom := by
  obtain ⟨i, g, hg⟩ := hr
  refine ⟨i, g * a⁻¹, ?_⟩
  rw [hx, pairSubgroup_doubleCoset _ _ _ ha hb, map_conj_comp, inv_mul_cancel_right]
  exact hg

public theorem generation_of_doubleCoset_cover {ι : Type*} (rep : ι → Atlas1600Group)
    (hcover : ∀ x : Atlas1600Group, ∃ (a b : thirteenNormalizer) (k : ι),
      x = a.val * rep k * b.val)
    (hrep : ∀ k, rep k ∈ thirteenNormalizer ∨
      ∃ (i : Fin 3) (g : Atlas1600Group),
        candidateDerived i ≤ (pairSubgroup (rep k)).map (MulAut.conj g).toMonoidHom)
    (x : Atlas1600Group) (hx : x ∉ thirteenNormalizer) :
    ∃ (i : Fin 3) (g : Atlas1600Group),
      candidateDerived i ≤ (pairSubgroup x).map (MulAut.conj g).toMonoidHom := by
  obtain ⟨a, b, k, hk⟩ := hcover x
  rcases hrep k with hn | hg
  · exact (hx (hk ▸ thirteenNormalizer.mul_mem
      (thirteenNormalizer.mul_mem a.property hn) b.property)).elim
  · exact generation_of_doubleCoset a.property b.property hk hg

end Tits.MinimumIndexThirteen.PairGeneration
