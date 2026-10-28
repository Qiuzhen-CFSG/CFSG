module

public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.ResidualOrbits.Normalizers.Geometry

/-!
# Lifting block normalizers through the actual actor quotient

A normalizer of `B*` preserves its common fixed subgroup, hence the full
lift `E`. The equality `B=C_H(E)` then makes it normalize `B`. Conversely,
normalization of `B` preserves its actor image. This proves an exact
preimage equality and surjectivity on relative normalizers, tracking the
kernel rather than assigning the ambient normalizer the model's order.

Moving the literal image of `V` therefore gives an ambient element moving
`V`. The model action supplying such motion remains separate.
Source: Aschbacher–Smith, combined manuscript (1 March 2004), p.1151.
-/

@[expose] public section
open Subgroup
namespace CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.ResidualOrbits.Normalizers
open Recognition
variable {G : Type*} [Group G]
variable (Z ZS : Subgroup G) [(Z.subgroupOf (closureU Z ZS)).Normal]

omit [(Z.subgroupOf (closureU Z ZS)).Normal] in
/-- Ambient normalization gives normalization of the literal actor image. -/
theorem actorImage_normalized (B : Subgroup G) (hBH : B ≤ centralizerH Z)
    (h : centralizerH Z) (hn : (h : G) ∈ normalizer (B : Set G)) :
    actorProjection Z h ∈ normalizer (actorImage Z B : Set (ActorQuotient Z)) := by
  have hi : h ∈ normalizer (B.subgroupOf (centralizerH Z) : Set (centralizerH Z)) := by
    rw [← subgroupOf_normalizer_eq hBH]
    exact hn
  exact (le_normalizer_map (actorProjection Z)) ⟨h, hi, rfl⟩

omit [(Z.subgroupOf (closureU Z ZS)).Normal] in
/-- The centralizer description makes `B` invariant under `N_H(E)`.
Normality here is relative to `H`, and no normalization of `T_K` is used. -/
theorem intersection_normalizer_le_block (B : Subgroup G)
    (hcentral : B = centralizerH Z ⊓
      centralizer ((B ⊓ closureU Z ZS : Subgroup G) : Set G)) :
    centralizerH Z ⊓ normalizer ((B ⊓ closureU Z ZS : Subgroup G) : Set G) ≤
      normalizer (B : Set G) := by
  intro h hh
  rw [hcentral]
  exact inf_normalizer_le_normalizer_inf
    ⟨(centralizerH Z).le_normalizer hh.1,
      normalizer_le_normalizer_centralizer (B ⊓ closureU Z ZS) hh.2⟩

omit [(Z.subgroupOf (closureU Z ZS)).Normal] in
/-- The relative normalizers of the actual intersection and block agree. -/
theorem intersection_normalizer_eq_block (B : Subgroup G)
    (hcentral : B = centralizerH Z ⊓
      centralizer ((B ⊓ closureU Z ZS : Subgroup G) : Set G)) :
    centralizerH Z ⊓ normalizer ((B ⊓ closureU Z ZS : Subgroup G) : Set G) =
      centralizerH Z ⊓ normalizer (B : Set G) := by
  apply le_antisymm
  · exact le_inf inf_le_left (intersection_normalizer_le_block Z ZS B hcentral)
  · intro h hh
    exact ⟨hh.1, inf_normalizer_le_normalizer_inf
      ⟨hh.2, H_normalizes_closureU Z ZS hh.1⟩⟩

/-- Every lift of a quotient actor normalizing `B*` normalizes `B`.
The fixed-space equality makes it normalize `E`, and the full `H`-centralizer
description then recovers `B`. -/
theorem actor_normalizer_lifts (B : Subgroup G)
    (hkernel : (quotientAction Z ZS).ker = pCore 2 (centralizerH Z))
    (hZU : Z ≤ closureU Z ZS) (hZB : Z ≤ B)
    (hfixed : vectorImage Z ZS (B ⊓ closureU Z ZS) =
      (actorAction Z ZS hkernel).commonFixed (actorImage Z B))
    (hcentral : B = centralizerH Z ⊓
      centralizer ((B ⊓ closureU Z ZS : Subgroup G) : Set G))
    (h : centralizerH Z)
    (hn : actorProjection Z h ∈ normalizer (actorImage Z B : Set (ActorQuotient Z))) :
    (h : G) ∈ normalizer (B : Set G) := by
  apply intersection_normalizer_le_block Z ZS B hcentral
  refine ⟨h.property, ?_⟩
  apply mem_normalizer_iff_map_conj_eq.mpr
  let E := B ⊓ closureU Z ZS
  let q := QuotientGroup.mk' (Z.subgroupOf (closureU Z ZS))
  have hlift := vectorImage_full_lift Z ZS E inf_le_right (le_inf hZB hZU)
  calc
    E.map (MulAut.conj (h : G)).toMonoidHom =
        (((vectorImage Z ZS E).comap q).map (closureU Z ZS).subtype).map
          (MulAut.conj (h : G)).toMonoidHom := congrArg _ hlift.symm
    _ = (((vectorImage Z ZS E).map (quotientAction Z ZS h).toMonoidHom).comap q).map
        (closureU Z ZS).subtype :=
      lift_support_conjugate (centralizerH Z) (closureU Z ZS) Z
        (H_normalizes_closureU Z ZS) (quotientAction Z ZS)
        (quotientAction_mk Z ZS) (vectorImage Z ZS E) h
    _ = ((vectorImage Z ZS E).comap q).map (closureU Z ZS).subtype := by
      change (((vectorImage Z ZS (B ⊓ closureU Z ZS)).map
        (quotientAction Z ZS h).toMonoidHom).comap q).map (closureU Z ZS).subtype = _
      rw [hfixed, ← actorAction_mk Z ZS hkernel h,
        MonoidHom.commonFixed_map_of_normalizes _ _ _ hn]
    _ = E := hlift

/-- The exact ambient witness used by the four-orbit census, lifted from a
moving actor. The actor calculation itself is a separate intrinsic obligation. -/
theorem moving_normalizer_of_actor_motion (B V : Subgroup G)
    (hVH : V ≤ centralizerH Z)
    (hkernel : (quotientAction Z ZS).ker = pCore 2 (centralizerH Z))
    (hZU : Z ≤ closureU Z ZS) (hZB : Z ≤ B)
    (hfixed : vectorImage Z ZS (B ⊓ closureU Z ZS) =
      (actorAction Z ZS hkernel).commonFixed (actorImage Z B))
    (hcentral : B = centralizerH Z ⊓
      centralizer ((B ⊓ closureU Z ZS : Subgroup G) : Set G))
    (hmotion : ∃ a ∈ normalizer (actorImage Z B : Set (ActorQuotient Z)),
      a ∉ normalizer (actorImage Z V : Set (ActorQuotient Z))) :
    ∃ h ∈ normalizer (B : Set G), h ∉ normalizer (V : Set G) := by
  obtain ⟨a, ha, hv⟩ := hmotion
  obtain ⟨h, rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 (centralizerH Z)) a
  refine ⟨h, actor_normalizer_lifts Z ZS B hkernel hZU hZB hfixed hcentral h ha, ?_⟩
  intro hn
  exact hv (actorImage_normalized Z V hVH h hn)

/-- The relative ambient normalizer is the full preimage of the actor
normalizer. Thus a model `S₄` concerns its quotient image, not this whole group. -/
theorem block_normalizer_preimage (B : Subgroup G) (hBH : B ≤ centralizerH Z)
    (hkernel : (quotientAction Z ZS).ker = pCore 2 (centralizerH Z))
    (hZU : Z ≤ closureU Z ZS) (hZB : Z ≤ B)
    (hfixed : vectorImage Z ZS (B ⊓ closureU Z ZS) =
      (actorAction Z ZS hkernel).commonFixed (actorImage Z B))
    (hcentral : B = centralizerH Z ⊓
      centralizer ((B ⊓ closureU Z ZS : Subgroup G) : Set G)) :
    (normalizer (B : Set G)).subgroupOf (centralizerH Z) =
      (normalizer (actorImage Z B : Set (ActorQuotient Z))).comap (actorProjection Z) := by
  ext h
  exact ⟨actorImage_normalized Z B hBH h,
    actor_normalizer_lifts Z ZS B hkernel hZU hZB hfixed hcentral h⟩

/-- The relative block normalizer surjects onto the full actor normalizer. -/
theorem block_normalizer_image (B : Subgroup G) (hBH : B ≤ centralizerH Z)
    (hkernel : (quotientAction Z ZS).ker = pCore 2 (centralizerH Z))
    (hZU : Z ≤ closureU Z ZS) (hZB : Z ≤ B)
    (hfixed : vectorImage Z ZS (B ⊓ closureU Z ZS) =
      (actorAction Z ZS hkernel).commonFixed (actorImage Z B))
    (hcentral : B = centralizerH Z ⊓
      centralizer ((B ⊓ closureU Z ZS : Subgroup G) : Set G)) :
    ((normalizer (B : Set G)).subgroupOf (centralizerH Z)).map (actorProjection Z) =
      normalizer (actorImage Z B : Set (ActorQuotient Z)) := by
  rw [block_normalizer_preimage Z ZS B hBH hkernel hZU hZB hfixed hcentral]
  exact map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _) _

end CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.ResidualOrbits.Normalizers
