module

public import Theory.SpecificGroups.ReeF4.ConverseParabolics.Coverage
public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.Geometry
public import Theory.GroupTheory.SylowNormalizerOvergroupAlignment

/-!
# Simultaneous normalizer coverage in the large Ree groups

The octagon places every nonidentity two-subgroup normalizer in a conjugate
proper full parabolic. The two concrete parabolic conventions agree, including
their torus words. The positive-root Sylow normalizer is the Borel in each
parabolic. Sylow conjugacy inside the selected parabolic therefore aligns the
prescribed Sylow subgroup and covers its full normalizer as well.

Source: Aschbacher--Smith 15.3.43(e), p.1140, and A.2.4, p.33. The parameter
is the literal Ree carrier over the field of order `2^(2*m+1)`, with `1 ≤ m`.
-/

public section

namespace ReeF4.ConverseParabolics

open Subgroup MaximalSubgroups.AbelianCharacteristic.TwoLocalGeometry

/-- Both normalizers in the large Ree carrier generate a proper subgroup. -/
theorem normalizer_sup_lt_top {m : ℕ} (hm : 1 ≤ m)
    (P : Sylow 2 (Model m)) (R : Subgroup (Model m))
    (hR : R ≠ ⊥) (hp : IsPGroup 2 R)
    (hP : (P : Subgroup (Model m)) ≤ normalizer (R : Set (Model m))) :
    normalizer (P : Set (Model m)) ⊔ normalizer (R : Set (Model m)) < ⊤ := by
  obtain ⟨g, s, hs, hg⟩ := normalizer_cover_proper hm R hR hp
  obtain ⟨U, hU⟩ := exists_sylow_eq_unipotent m
  refine Sylow.normalizer_sup_lt_top_of_map_le U P _ (parabolic m s)
    (MulAut.conj g) hP hg ?_ (lt_top_iff_ne_top.mpr hs)
  change normalizer ((U : Subgroup (Model m)) : Set (Model m)) ≤ _
  rw [hU, unipotent_eq_rootUnipotent, parabolic_eq_rootParabolic,
    Parabolics.unipotent_normalizer_eq_borel]
  exact Parabolics.borel_le_parabolic m s

end ReeF4.ConverseParabolics
