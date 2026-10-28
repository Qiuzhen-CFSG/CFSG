module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankOne.Basic
public import CFSG.Quasithin.Chapter15.Section03.Preliminaries.ComponentIntersection.Basic
public import Theory.GroupTheory.GeneralizedFitting.RelativeComponent
public import Theory.GroupTheory.SylowSubnormalIntersection

/-!
# The canonical component projection in the rank-one reduction

The preimage in `L` of the action of `Y` is `L ∩ (Y C_G(L))`.
Its two-residual is the canonical projection used here; taking the
residual avoids choosing representatives modulo the central two-core.
Every simultaneous normalizer of `Y` and `L` preserves this construction.
In particular `N_S(L)` preserves it, and subnormal Sylow restriction
gives the required Sylow intersection with `S`.

Source: Aschbacher--Smith, combined manuscript (1 March 2004),
the inner-action paragraph of 15.3.43, printed p.1139.
-/

@[expose] public section

open Subgroup
namespace CFSG.Quasithin.Chapter15.Section03.RankOne.ComponentProjection
variable {G : Type*} [Group G]

/-- Full preimage in the component of the inner action image of `Y`. -/
def preimage (Y L : Subgroup G) : Subgroup G :=
  L ⊓ (Y ⊔ centralizer (L : Set G))

/-- The canonical two-perfect component projection, without a chosen splitting. -/
def projection (Y L : Subgroup G) : Subgroup G :=
  (pResidual 2 (preimage Y L)).map (preimage Y L).subtype

theorem projection_le_preimage (Y L : Subgroup G) :
    projection Y L ≤ preimage Y L := map_subtype_le _

theorem projection_le_component (Y L : Subgroup G) : projection Y L ≤ L :=
  (projection_le_preimage Y L).trans inf_le_left

theorem projection_isPPerfect [Finite G] (Y L : Subgroup G) :
    IsPPerfect 2 (projection Y L) := isPPerfect_embedded_pResidual 2 _

/-- The construction is preserved by simultaneous normalizers. -/
theorem normalizes_projection {X Y L : Subgroup G}
    (hY : X ≤ normalizer (Y : Set G)) (hL : X ≤ normalizer (L : Set G)) :
    X ≤ normalizer (projection Y L : Set G) := by
  have hC : X ≤ normalizer (centralizer (L : Set G) : Set G) :=
    hL.trans (normalizer_le_normalizer_centralizer L)
  have hsup := (le_inf hY hC).trans
    (normalizer_inf_normalizer_le_normalizer_sup Y (centralizer (L : Set G)))
  have hpre : X ≤ normalizer (preimage Y L : Set G) :=
    (le_inf hL hsup).trans inf_normalizer_le_normalizer_inf
  exact hpre.trans
    (normalizer_le_normalizer_characteristic_image (preimage Y L)
      (pResidual 2 (preimage Y L)))

/-- In particular, the source subgroup `N_S(L)` preserves the actual projection. -/
theorem sylow_normalizer_normalizes_projection {S Y L : Subgroup G}
    (hSY : S ≤ normalizer (Y : Set G)) :
    S ⊓ normalizer (L : Set G) ≤ normalizer (projection Y L : Set G) :=
  normalizes_projection (inf_le_left.trans hSY) inf_le_right

private theorem sylow_restrict_normalized [Finite G] (T : Sylow 2 G)
    (A : Subgroup G) (hTA : (T : Subgroup G) ≤ normalizer (A : Set G)) :
    ∃ Q : Sylow 2 A, (Q : Subgroup A) = (T : Subgroup G).subgroupOf A := by
  let N := normalizer (A : Set G)
  obtain ⟨Q, hQ⟩ := (T.subtype hTA).exists_subgroupOf_eq_of_normal (A.subgroupOf N)
  let e := subgroupOfEquivOfLe A.le_normalizer
  refine ⟨Q.mapSurjective (f := e.toMonoidHom) e.surjective, ?_⟩
  change (Q : Subgroup (A.subgroupOf N)).map e.toMonoidHom = _
  rw [hQ]
  ext a
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact hx
  · intro ha
    exact ⟨⟨⟨a, A.le_normalizer a.property⟩, a.property⟩, ha, rfl⟩

/-- A subgroup of a component normalized by `N_S(L)` has the required
Sylow intersection. Only the genuine subnormality of the component is used. -/
theorem sylow_intersection [Finite G] {S I L A : Subgroup G}
    (P : Sylow 2 I) (hP : (P : Subgroup I).map I.subtype = S)
    (hLI : L ≤ I) (hL : Theory.GroupTheory.IsComponent I (L.subgroupOf I))
    (hAL : A ≤ L)
    (hn : S ⊓ normalizer (L : Set G) ≤ normalizer (A : Set G)) :
    ∃ Q : Sylow 2 A, (Q : Subgroup A).map A.subtype = S ⊓ A := by
  obtain ⟨T₀, hT₀⟩ := P.exists_subgroupOf_eq_of_subnormal (L.subgroupOf I) hL.1
  let eL := subgroupOfEquivOfLe hLI
  let T : Sylow 2 L := T₀.mapSurjective (f := eL.toMonoidHom) eL.surjective
  have hT : (T : Subgroup L) = S.subgroupOf L := by
    ext l
    rw [← hP]
    constructor
    · rintro ⟨x, hx, he⟩
      rw [hT₀] at hx
      exact ⟨x.val, hx, congrArg Subtype.val he⟩
    · rintro ⟨x, hx, he⟩
      have hxL : (x : G) ∈ L := by
        change (x : G) = (l : G) at he
        rw [he]
        exact l.property
      refine ⟨⟨x, hxL⟩, ?_, ?_⟩
      · rwa [hT₀]
      · exact Subtype.ext he
  have hTA : (T : Subgroup L) ≤ normalizer (A.subgroupOf L : Set L) := by
    rw [← subgroupOf_normalizer_eq hAL, hT]
    intro l hl
    exact hn ⟨hl, L.le_normalizer l.property⟩
  obtain ⟨Q₀, hQ₀⟩ := sylow_restrict_normalized T (A.subgroupOf L) hTA
  let eA := subgroupOfEquivOfLe hAL
  refine ⟨Q₀.mapSurjective (f := eA.toMonoidHom) eA.surjective, ?_⟩
  change ((Q₀ : Subgroup (A.subgroupOf L)).map eA.toMonoidHom).map A.subtype = _
  rw [hQ₀, hT]
  ext a
  constructor
  · rintro ⟨x, ⟨z, hz, rfl⟩, rfl⟩
    exact ⟨hz, z.property⟩
  · rintro ⟨haS, haA⟩
    exact ⟨⟨a, haA⟩, ⟨⟨⟨a, hAL haA⟩, haA⟩, haS, rfl⟩, rfl⟩

/-- The Sylow conclusion for the canonical projection. -/
theorem projection_sylow_intersection [Finite G] {Y S I L : Subgroup G}
    (P : Sylow 2 I) (hP : (P : Subgroup I).map I.subtype = S)
    (hLI : L ≤ I) (hL : Theory.GroupTheory.IsComponent I (L.subgroupOf I))
    (hSY : S ≤ normalizer (Y : Set G)) :
    ∃ Q : Sylow 2 (projection Y L),
      (Q : Subgroup (projection Y L)).map (projection Y L).subtype =
        S ⊓ projection Y L :=
  sylow_intersection P hP hLI hL (projection_le_component Y L)
    (sylow_normalizer_normalizes_projection hSY)

end CFSG.Quasithin.Chapter15.Section03.RankOne.ComponentProjection
