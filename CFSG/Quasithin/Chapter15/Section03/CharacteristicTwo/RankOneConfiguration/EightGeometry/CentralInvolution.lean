module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.EightGeometry.LocalControl

/-!
# The central involution avoids both definite planes

A nonidentity vector supported on one coordinate plane can be fixed only
by an orthogonal wreath actor whose coordinate shift is trivial. If all
central involutions of `T` lay in one definite plane, compatibility would
therefore make all of `T` stabilize both planes. This contradicts the
index-two definition of `S`.

Thus the central-involution avoidance required for the conjugate-pair
argument follows from the actual orthogonal coordinates and `|Z| = 2`;
it is not an additional geometric hypothesis.

Source: Aschbacher–Smith, combined manuscript (1 March 2004),
15.3.2(2), the definite-plane decomposition on pp.1121–1122, and
15.3.32(5), printed p.1133.
-/

public section

open Subgroup
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.EightGeometry
variable {G : Type*} [Group G]

private theorem shift_eq_one_of_fixed_supported
    (i : OrthogonalPlaneIndex) (g : OrthogonalActor) (v : OrthogonalVector)
    (hs : v ∈ orthogonalCoordinatePlane i) (hne : v ≠ 1) :
    letI := orthogonalAction
    g • v = v → g.right = 1 := by
  let _ := FourGroupMatrixCoordinates.naturalAction
  let _ := orthogonalAction
  intro hfix
  have hvi : v i ≠ 1 := by
    intro hi
    apply hne
    funext j
    by_cases hj : j = i
    · exact hj ▸ hi
    · exact hs j hj
  have hi : g.right⁻¹ * i = i := by
    by_contra hi
    have he := congrFun hfix i
    change g.left i • v (g.right⁻¹ * i) = v i at he
    rw [hs _ hi, smul_one] at he
    exact hvi he.symm
  exact inv_eq_one.mp (mul_right_cancel (hi.trans (one_mul i).symm))

private theorem supported_of_shift_eq_one
    (i : OrthogonalPlaneIndex) (g : OrthogonalActor) (hg : g.right = 1)
    (v : OrthogonalVector) (hv : v ∈ orthogonalCoordinatePlane i) :
    letI := orthogonalAction
    g • v ∈ orthogonalCoordinatePlane i := by
  let _ := FourGroupMatrixCoordinates.naturalAction
  let _ := orthogonalAction
  intro j hj
  change g.left j • v (g.right⁻¹ * j) = 1
  rw [hg, inv_one, one_mul, hv j hj, smul_one]

/-- The central involution is supported on neither of the two definite planes. -/
theorem centralInvolutions_not_le_plane (d : LocalData G)
    (hindex : (d.S.subgroupOf (d.T : Subgroup G)).index = 2)
    (hZ : Nat.card d.Z = 2) (i : OrthogonalPlaneIndex) :
    ¬ d.Z ≤ d.action.plane i := by
  let _ := orthogonalAction
  intro hZi
  have hZne : d.Z ≠ ⊥ := by
    intro hz
    rw [hz, Subgroup.card_bot] at hZ
    contradiction
  obtain ⟨z, hz, hzne⟩ := (d.Z.nontrivial_iff_exists_ne_one).mp
    ((d.Z.nontrivial_iff_ne_bot).mpr hZne)
  obtain ⟨zv, hzi, he⟩ := hZi hz
  change (zv : G) = z at he
  have hzcoord : d.action.coordinates zv ≠ 1 := by
    intro h
    have hv : zv = 1 := d.action.coordinates.injective (h.trans (map_one _).symm)
    exact hzne (he.symm.trans (congrArg Subtype.val hv))
  have hshift (t : G) (ht : t ∈ (d.T : Subgroup G)) :
      (d.action.actor ⟨t, d.sylow_le ht⟩).right = 1 := by
    apply shift_eq_one_of_fixed_supported i _ _ hzi hzcoord
    change d.action.actor ⟨t, d.sylow_le ht⟩ • d.action.coordinates zv = d.action.coordinates zv
    rw [← d.action.compatible]
    congr 1
    apply Subtype.ext
    change t * (zv : G) * t⁻¹ = (zv : G)
    have hcomm := centralInvolutions_le_centralizer_sylow d.T hz t ht
    rw [he, hcomm, mul_inv_cancel_right]
  have hTnorm : (d.T : Subgroup G) ≤ normalizer (d.V₁ : Set G) := by
    apply Subgroup.le_normalizer_iff.mpr
    intro t ht u hu
    obtain ⟨uv, huv, rfl⟩ := hu
    let tv := d.V.normalizerMonoidHom ⟨t, d.action.normalizes (d.sylow_le ht)⟩ uv
    have hp : d.action.coordinates tv ∈ orthogonalCoordinatePlane 1 := by
      rw [show d.action.coordinates tv =
        (letI := orthogonalAction; d.action.actor ⟨t, d.sylow_le ht⟩ • d.action.coordinates uv) from
        d.action.compatible ⟨t, d.sylow_le ht⟩ uv]
      exact supported_of_shift_eq_one 1 _ (hshift t ht) _ huv
    exact ⟨tv, hp, rfl⟩
  have hTS : (d.T : Subgroup G) ≤ d.S := le_inf le_rfl hTnorm
  have htop : d.S.subgroupOf (d.T : Subgroup G) = ⊤ := subgroupOf_eq_top.mpr hTS
  rw [htop, Subgroup.index_top] at hindex
  contradiction

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.EightGeometry

end
