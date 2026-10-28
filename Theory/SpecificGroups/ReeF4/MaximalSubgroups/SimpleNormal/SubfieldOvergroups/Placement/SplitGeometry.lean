module

public import Theory.SpecificGroups.ReeF4.MaximalSubgroups.SimpleNormal.SubfieldOvergroups.Placement.SplitGeometry.Basic

/-!
# Reduction of split F4 conjugacy to binary and anchored geometry

Embed the binary derived group into the supplied socle using coefficient maps
and the given equivalence. Binary conjugacy places its image. For positive
parameters, the anchored-rigidity obligation identifies the whole conjugated
socle; at parameter zero binary conjugacy already gives the required equality.
Mapping that equality into split F4 gives precisely `SplitConjugacy`.

This is a conditional assembly. The root calculations in Malle's Proposition
2.13 and the torus-generation argument in §2.12 remain to be proved; no
unconditional `splitConjugacy` is asserted here. The stronger Ree conjugator
comes from that source route, without invoking field descent or the separate
binary split-centralizer theorem.

Source: Malle, J. Algebra 139 (1991), 52–69,
DOI 10.1016/0021-8693(91)90283-E; author manuscript
https://agag-malle.math.rptu.de/~malle/download/sub2f4.dvi, pp.12–13.
-/

public section

namespace ReeF4.MaximalSubgroups.SimpleNormal.Placement

open Subgroup ReeF4.Subfield SplitGeometry

private theorem split_image_eq_of_ree_image_eq {m k : ℕ} (H : Subgroup (Model m))
    (hdiv : (2 * k + 1) ∣ (2 * m + 1))
    (f : CoefficientField k →+* CoefficientField m) (g : Model m)
    (h : H.map (MulAut.conj g).toMonoidHom =
      (_root_.commutator (Model k)).map (reeMap hdiv f)) :
    (H.map (toSplitGroup m)).map (MulAut.conj (toSplitGroup m g)).toMonoidHom =
      (_root_.commutator (Model k)).map ((splitMap f).comp (toSplitGroup k)) := by
  have hc : (MulAut.conj (toSplitGroup m g)).toMonoidHom.comp (toSplitGroup m) =
      (toSplitGroup m).comp (MulAut.conj g).toMonoidHom := by
    apply MonoidHom.ext
    intro x
    simp [MulAut.conj_apply]
  have hf : (toSplitGroup m).comp (reeMap hdiv f) =
      (splitMap f).comp (toSplitGroup k) := by
    apply MonoidHom.ext
    intro x
    exact toSplitGroup_reeMap hdiv f x
  rw [map_map, hc, ← map_map, h, map_map, hf]


/-- The binary conjugacy and anchored positive-parameter geometry together imply
the exact split-conjugacy contract. Both geometric premises remain explicit. -/
theorem splitConjugacy_of_binaryConjugacy_of_anchoredRigidity
    (hb : BinaryConjugacy) (hr : AnchoredRigidity) : SplitConjugacy := by
  intro m hm M hM hsolv hR S hSn hSs hSa hCS k hlt hdiv e
  by_cases hk : k = 0
  · subst k
    obtain ⟨g, hg⟩ := hb m hm (socleEmbedding e) (socleEmbedding_injective e)
    rw [socleEmbedding_range] at hg
    exact ⟨binaryCoefficientHom m, toSplitGroup m g,
      split_image_eq_of_ree_image_eq _ hdiv (binaryCoefficientHom m) g hg⟩
  · obtain ⟨g, hg⟩ := hb m hm (binarySocleEmbedding e) (binarySocleEmbedding_injective e)
    have hanchor : binaryDerivedImage m ≤
        (S.map M.subtype).map (MulAut.conj g).toMonoidHom := by
      rw [← hg]
      exact map_mono (binarySocleEmbedding_range_le e)
    obtain ⟨f, hf⟩ := hr m hm M hM hsolv hR S hSn hSs hSa hCS k
      (Nat.one_le_iff_ne_zero.mpr hk) hlt hdiv e g hanchor
    exact ⟨f, toSplitGroup m g, split_image_eq_of_ree_image_eq _ hdiv f g hf⟩

end ReeF4.MaximalSubgroups.SimpleNormal.Placement

