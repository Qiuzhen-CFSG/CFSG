module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankTwo.Containment.FactorGeometry.PlaneActors.FullAction.Lifting
public import CFSG.Quasithin.Chapter15.Section03.Preliminaries.ComponentIntersection.Basic
public import Theory.GroupTheory.PResidual.NormalSubgroup.TwoGroupKernel

/-!
# The centralizer line in the CaseTwo quotient

If an actor X fixes one definite plane, the centralizer in X of the other
plane is exactly the kernel of the compatible action on V. An action image
of order three and a two-core quotient of order nine therefore give an
order-three image of this centralizer in X/O₂(X). The two-residual still
surjects onto that odd line. Its two-group kernel preserves its three-part.

All centralizers and kernels are taken relative to X; no ambient normality,
identification of the rank-two shadow, or complementary actor is assumed.
The coordinate calculation must supply the order-three action image.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), CaseTwo in
15.3.10 and 15.3.11(5), printed pp.1123–1124, and the plane actors used in
15.3.39–40, printed pp.1137–1138.
-/

public section

open Subgroup
namespace CFSG.Quasithin.Chapter15.Section03.RankTwo

private theorem core_le_ker_of_range_three {H K : Type*}
    [Group H] [Finite H] [Group K] (f : H →* K)
    (hr : Nat.card f.range = 3) : pCore 2 H ≤ f.ker := by
  have hp := (pCore_isPGroup (p := 2) (G := H)).map f
  have hd : Nat.card ((pCore 2 H).map f) ∣ 3 :=
    hr ▸ card_dvd_of_le (map_le_range _ _)
  have hb : (pCore 2 H).map f = ⊥ := by
    apply card_eq_one.mp
    rcases hp.card_eq_or_dvd with he | he
    · exact he
    · have : 2 ∣ 3 := he.trans hd
      norm_num at this
  exact (Subgroup.map_eq_bot_iff _).mp hb

private theorem kernel_image_card_three {H K : Type*}
    [Group H] [Finite H] [Group K] (f : H →* K)
    (hr : Nat.card f.range = 3) (hq : Nat.card (H ⧸ pCore 2 H) = 9) :
    Nat.card (f.ker.map (QuotientGroup.mk' (pCore 2 H))) = 3 := by
  let q := QuotientGroup.mk' (pCore 2 H)
  have hi : (f.ker.map q).index = 3 := by
    rw [index_map_eq _ (QuotientGroup.mk'_surjective _) (by
      rw [QuotientGroup.ker_mk']
      exact core_le_ker_of_range_three f hr), index_ker, hr]
  have hc := (f.ker.map q).card_mul_index
  rw [hi, hq] at hc
  dsimp only [q] at hc
  omega

private theorem residual_threePart_of_range_three {H K : Type*}
    [Group H] [Finite H] [Group K] (f : H →* K)
    (hk : IsPGroup 2 f.ker) (hr : Nat.card f.range = 3) :
    3 ^ (Nat.card (pResidual 2 H)).factorization 3 = 3 := by
  have hp : IsPGroup 3 f.range := IsPGroup.of_card (n := 1) (by simpa using hr)
  have he : pResidual 2 f.range = ⊤ := by
    apply top_unique
    intro x _
    exact mem_pResidual_of_orderOf_coprime
      (hp.orderOf_coprime (by decide : Nat.Coprime 3 2) x).symm
  have hm : (pResidual 2 H).map f = f.range := by
    change (pResidual 2 H).map (f.range.subtype.comp f.rangeRestrict) = _
    rw [← map_map, map_pResidual_of_surjective 2 _ f.rangeRestrict_surjective,
      he, ← MonoidHom.range_eq_map, range_subtype]
  rw [← threePart_map_of_twoGroup_kernel f hk, hm, hr]
  norm_num

variable {G : Type*} [Group G]

/-- Fixing one of the two definite planes identifies the remaining plane
centralizer with the kernel of the full vector action. -/
theorem natural_other_plane_centralizer_kernel {M V X : Subgroup G}
    (d : NaturalOrthogonalAction M V) (hXM : X ≤ M)
    {i j : OrthogonalPlaneIndex} (hij : i ≠ j)
    (hXi : X ≤ centralizer (d.plane i : Set G)) :
    (d.actor.comp (inclusion hXM)).ker =
      (X ⊓ centralizer (d.plane j : Set G)).subgroupOf X := by
  rw [natural_restricted_actor_ker]
  ext x
  constructor
  · intro hx
    exact ⟨x.property, centralizer_le (d.plane_le j) hx⟩
  · rintro ⟨_, hx⟩
    have hc : X ⊓ centralizer (d.plane j : Set G) ≤ centralizer (V : Set G) := by
      apply le_centralizer_iff.mpr
      apply (natural_planes_sup d hij).ge.trans
      exact sup_le (le_centralizer_iff.mp (inf_le_left.trans hXi))
        (le_centralizer_iff.mp inf_le_right)
    exact hc ⟨x.property, hx⟩

/-- An order-three plane image leaves exactly a line in the order-nine
quotient by the two-core. The centralizer is taken inside the actor X. -/
theorem natural_other_plane_centralizer_quotient_card [Finite G]
    {M V X : Subgroup G} (d : NaturalOrthogonalAction M V) (hXM : X ≤ M)
    {i j : OrthogonalPlaneIndex} (hij : i ≠ j)
    (hXi : X ≤ centralizer (d.plane i : Set G))
    (himage : Nat.card (d.image X) = 3)
    (h9 : Nat.card (X ⧸ pCore 2 X) = 9) :
    Nat.card (((X ⊓ centralizer (d.plane j : Set G)).subgroupOf X).map
      (QuotientGroup.mk' (pCore 2 X))) = 3 := by
  rw [← natural_other_plane_centralizer_kernel d hXM hij hXi]
  apply kernel_image_card_three _ _ h9
  rwa [natural_restricted_actor_range]

/-- Passing to the literal two-residual retains the odd line through the
two-group kernel, so its exact three-part is three. -/
theorem natural_other_plane_centralizingFactor_threePart [Finite G]
    {M V X : Subgroup G} (d : NaturalOrthogonalAction M V) (hXM : X ≤ M)
    {i j : OrthogonalPlaneIndex} (hij : i ≠ j)
    (hXi : X ≤ centralizer (d.plane i : Set G))
    (himage : Nat.card (d.image X) = 3)
    (h9 : Nat.card (X ⧸ pCore 2 X) = 9) :
    3 ^ (Nat.card (centralizingFactor X (d.plane j))).factorization 3 = 3 := by
  let C := X ⊓ centralizer (d.plane j : Set G)
  let q := QuotientGroup.mk' (pCore 2 X)
  let f : C →* X ⧸ pCore 2 X := q.comp (inclusion inf_le_left)
  have hk : f.ker = (pCore 2 X).comap (inclusion (show C ≤ X from inf_le_left)) := by
    change ((QuotientGroup.mk' (pCore 2 X)).comp (inclusion inf_le_left)).ker = _
    rw [← MonoidHom.comap_ker, QuotientGroup.ker_mk']
  have hp : IsPGroup 2 f.ker := by
    rw [hk]
    exact pCore_isPGroup.comap_of_injective _ (inclusion_injective _)
  have hr : f.range = (C.subgroupOf X).map q := by
    ext x
    constructor
    · rintro ⟨c, rfl⟩
      exact ⟨inclusion inf_le_left c, c.property, rfl⟩
    · rintro ⟨c, hc, rfl⟩
      exact ⟨⟨c, hc⟩, rfl⟩
  have h3 : Nat.card f.range = 3 := by
    rw [hr]
    exact natural_other_plane_centralizer_quotient_card d hXM hij hXi himage h9
  rw [centralizingFactor, ComponentIntersection.twoResidualAmbient_eq_map_pResidual,
    card_map_of_injective (X ⊓ centralizer (d.plane j : Set G)).subtype_injective]
  exact residual_threePart_of_range_three f hp h3

end CFSG.Quasithin.Chapter15.Section03.RankTwo
