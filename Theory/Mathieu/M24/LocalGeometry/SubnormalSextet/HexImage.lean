module

public import Theory.AtlasPort.OtherSporadic.Codes.HexacodeAutomorphismPackage
public import Theory.GroupTheory.PPerfectHom
public import Mathlib.GroupTheory.IsSubnormal
public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple

/-!
# Subnormal two-perfect hexacode images

Two-perfection kills the sign homomorphism. Subnormality then makes the
coordinate image in A₆ trivial or full. The kernel has prime order three;
a proper subgroup surjecting onto A₆ would give a section of the actual
nonsplit triple cover. Consequently the only possibilities are the trivial
subgroup, the cubic coordinate kernel, and the even hexacode group.

This is the quotient calculation used by the intrinsic sextet order theorem
in `SubnormalSextet`. Source: the local-group argument for Aschbacher–Smith
2.3.9(7), printed p.526, with the shape in GLS3 Table 5.3e. The actual
hexacode maps and nonsplitting proof are imported from Gerald Höhn and ATLAS
contributors, revision `8eabb35afe2b5e45bf913a2d05c53e558d2e2917`, under the
ATLAS Research and Attribution License 1.0; see `LICENSES/ATLAS.txt`.
The cubic kernel is central only in the even group; the proof does not
assume it is central in the full hexacode automorphism group.
-/

public section

open Subgroup
namespace Sporadic.Mathieu.M24LocalGeometry.SubnormalSextet
open Atlas.Codes

private theorem eq_bot_or_eq_of_le_prime {G : Type*} [Group G]
    (B K : Subgroup G) (h : B ≤ K) (hp : (Nat.card K).Prime) : B = ⊥ ∨ B = K := by
  let : Fact (Nat.card K).Prime := ⟨hp⟩
  rcases (B.subgroupOf K).eq_bot_or_eq_top_of_prime_card with hb | ht
  · left
    have he := congrArg (Subgroup.map K.subtype) hb
    simpa only [map_subgroupOf_eq_of_le h, Subgroup.map_bot] using he
  · right
    exact le_antisymm h (subgroupOf_eq_top.mp ht)

private theorem even_eq_top_of_coordinate_full (B : Subgroup HexEvenAutomorphisms)
    (hB : B.map hexEvenCoordinate = ⊤) : B = ⊤ := by
  have hp : (Nat.card hexEvenCoordinate.ker).Prime := by
    rw [hexEven_kernel_card]; decide
  rcases eq_bot_or_eq_of_le_prime (B ⊓ hexEvenCoordinate.ker)
      hexEvenCoordinate.ker inf_le_right hp with hb | hk
  · have hi : Function.Injective (hexEvenCoordinate.comp B.subtype) := by
      apply (MonoidHom.ker_eq_bot_iff _).mp
      apply bot_unique
      intro x hx
      apply Subtype.ext
      exact mem_bot.mp (show (x : HexEvenAutomorphisms) ∈ (⊥ : Subgroup _) from
        hb ▸ ⟨x.property, hx⟩)
    have hs : Function.Surjective (hexEvenCoordinate.comp B.subtype) := by
      apply MonoidHom.range_eq_top.mp
      rwa [MonoidHom.range_comp, range_subtype]
    let e := MulEquiv.ofBijective (hexEvenCoordinate.comp B.subtype) ⟨hi, hs⟩
    exfalso
    apply hexEven_no_section
    refine ⟨B.subtype.comp e.symm.toMonoidHom, ?_⟩
    apply MonoidHom.ext
    intro x
    exact e.apply_symm_apply x
  · apply map_injective_of_ker_le hexEvenCoordinate
      (hk ▸ inf_le_left : hexEvenCoordinate.ker ≤ B) le_top
    rw [hB, map_top_of_surjective _ hexEvenCoordinate_surjective]

/-- Subnormal two-perfect images in the actual hexacode automorphism group. -/
theorem hex_image_alternatives (B : Subgroup HexAutomorphisms)
    (hB : B.IsSubnormal) (hpB : IsPPerfect 2 B) :
    B = ⊥ ∨ B = hexCoordinateSixHom.ker ∨ B = hexSign.ker := by
  have hsign : B ≤ hexSign.ker := by
    have hp : IsPGroup 2 ℤˣ := IsPGroup.of_card (n := 1) (by simp [Nat.card_eq_fintype_card])
    have hf := hpB.hom_eq_one_of_isPGroup hp (hexSign.comp B.subtype)
    intro x hx
    exact DFunLike.congr_fun hf ⟨x,hx⟩
  let B' := B.subgroupOf hexSign.ker
  have hn : (B'.map hexEvenCoordinate).IsSubnormal :=
    hB.subgroupOf.map hexEvenCoordinate_surjective
  rcases hn.eq_bot_or_top_of_isSimpleGroup
      (alternatingGroup.isSimpleGroup (by simp : 5 ≤ Nat.card (Fin 6))) with hb | ht
  · have hk : B ≤ hexCoordinateSixHom.ker := by
      intro x hx
      have hm : hexEvenCoordinate ⟨x,hsign hx⟩ ∈ B'.map hexEvenCoordinate :=
        ⟨⟨x,hsign hx⟩, hx, rfl⟩
      rw [hb] at hm
      exact congrArg Subtype.val (mem_bot.mp hm)
    have hc : (Nat.card hexCoordinateSixHom.ker).Prime := by
      rw [hexCoordinateSix_kernel, Nat.card_zpowers, hexZ_order]
      decide
    exact (eq_bot_or_eq_of_le_prime B _ hk hc).imp_right Or.inl
  · right; right
    exact le_antisymm hsign (subgroupOf_eq_top.mp (even_eq_top_of_coordinate_full B' ht))

end Sporadic.Mathieu.M24LocalGeometry.SubnormalSextet
