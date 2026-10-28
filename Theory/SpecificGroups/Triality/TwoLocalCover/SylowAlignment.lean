module

public import Theory.SpecificGroups.Triality.TwoLocalCover
public import Theory.SpecificGroups.Triality.ConcreteBruhat.CartanNormalizer
public import Theory.GroupTheory.SylowNormalizerOvergroupAlignment

/-!
# Simultaneous normalizer coverage in the genuine binary triality carrier

The hexagon covers the two-subgroup normalizer by a conjugate full root
parabolic. The positive-root Sylow normalizer is the Borel. Conjugating Sylow
subgroups inside that parabolic aligns the prescribed Sylow subgroup without
losing coverage, so both full normalizers generate a proper subgroup.

The carrier is the graph-field D₄ construction modulo the center of its
elementary fixed subgroup. No auxiliary matrix-model identification is used.
Source: Aschbacher--Smith 15.3.43(e), p.1140, and A.2.4, p.33.
-/

public section

namespace Triality.Standard.TwoLocalCover

open Subgroup Parabolics

/-- Both normalizers lie in a common proper overgroup of the genuine carrier. -/
theorem normalizer_sup_lt_top (n : ℕ) (hn : 0 < n)
    (P : Sylow 2 (Carrier (binaryParameters n hn)))
    (R : Subgroup (Carrier (binaryParameters n hn)))
    (hR : R ≠ ⊥) (hp : IsPGroup 2 R)
    (hP : (P : Subgroup (Carrier (binaryParameters n hn))) ≤
      normalizer (R : Set (Carrier (binaryParameters n hn)))) :
    normalizer (P : Set (Carrier (binaryParameters n hn))) ⊔
      normalizer (R : Set (Carrier (binaryParameters n hn))) < ⊤ := by
  obtain ⟨g, a, hg⟩ := normalizer_cover n hn R hR hp
  refine Sylow.normalizer_sup_lt_top_of_map_le
    (unipotentSylow (binaryParameters n hn) rfl) P _
    (parabolic (binaryParameters n hn) a) (MulAut.conj g) hP hg ?_
    (lt_top_iff_ne_top.mpr (parabolic_ne_top_binary _ rfl a))
  change normalizer (unipotent (binaryParameters n hn) :
    Set (Carrier (binaryParameters n hn))) ≤ _
  rw [ConcreteBruhat.normalizer_unipotent_eq_borel _ rfl]
  exact borel_le_parabolic _ a

end Triality.Standard.TwoLocalCover
