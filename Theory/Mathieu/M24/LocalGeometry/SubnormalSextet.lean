module

public import Theory.Mathieu.M24.LocalGeometry.SubnormalSextet.HexImage
public import Theory.Mathieu.M24.LocalGeometry.SubnormalSextet.CubicTranslations
public import Theory.Mathieu.M24.LocalGeometry.SextetCore.Hexacode
public import Theory.GroupTheory.PGroup.NormalDirectPowerSection
public import Theory.Representation.MathieuCodeRestriction.CocodeLocal.Sextet.Layers.CoordinateTransport.Markings

/-!
# Subnormal two-perfect subgroups of native M₂₄ sextet stabilizers

For every native sextet and every subnormal two-perfect subgroup E of its
stabilizer, E is trivial, or E/O₂(E) has order three and |E| > 12, or E/O₂(E)
has order 1080. No ambient normality or irreducibility assumption is needed.

In the genuine affine hexacode model, the kernel is O₂ of the stabilizer.
A subnormal subgroup intersects this kernel in its own intrinsic two-core,
so its core quotient is exactly its hexacode image. The image calculation
leaves the trivial, cubic and even triple-cover cases. Two-perfection
eliminates a nontrivial translation-only subgroup. In the cubic case,
fixed-point-free scalar commutators and subnormal absorption force all
64 translations into E. Native sextet conjugacy transports both E and its
intrinsic core quotient through the actual stabilizer equivalence.

This supplies the intrinsic sextet calculation for the M₂₄ local-block
exclusion in Aschbacher–Smith 2.3.9(7), printed p.526; GLS3 Table 5.3e
records the local-group shape. It does not assert the whole source theorem.
The imported concrete hexacode and affine model are by Gerald Höhn and
ATLAS contributors, revision `8eabb35afe2b5e45bf913a2d05c53e558d2e2917`,
under the ATLAS Research and Attribution License 1.0; see `LICENSES/ATLAS.txt`.
-/

public section

open Subgroup
namespace Sporadic.Mathieu.M24LocalGeometry.SubnormalSextet
open Atlas.Codes

/-- The intrinsic quotient is the actual affine image, even for merely
subnormal subgroups of the sextet stabilizer. -/
noncomputable def coreQuotientImageEquiv (E : Subgroup SextetStabilizer)
    (hE : E.IsSubnormal) : (E ⧸ pCore 2 E) ≃* E.map sextetQuotient := by
  have hk : (sextetQuotient.subgroupMap E).ker = pCore 2 E := by
    rw [Subgroup.ker_subgroupMap, ← SextetCore.atlas_core_eq_kernel]
    exact hE.pCore_subgroupOf 2
  exact (QuotientGroup.quotientMulEquivOfEq hk.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective (sextetQuotient.subgroupMap E)
      (sextetQuotient.subgroupMap_surjective E))

/-- The three order alternatives in the genuine affine coordinates. -/
theorem atlas_orders (E : Subgroup SextetStabilizer)
    (hE : E.IsSubnormal) (hpE : IsPPerfect 2 E) :
    Nat.card E = 1 ∨
      (Nat.card (E ⧸ pCore 2 E) = 3 ∧ 12 < Nat.card E) ∨
        Nat.card (E ⧸ pCore 2 E) = 1080 := by
  have hc : Nat.card (E ⧸ pCore 2 E) = Nat.card (E.map sextetQuotient) :=
    Nat.card_congr (coreQuotientImageEquiv E hE).toEquiv
  have hn := hE.map sextetQuotient_surjective
  have hp := hpE.of_surjective (sextetQuotient.subgroupMap E)
    (sextetQuotient.subgroupMap_surjective E)
  rcases hex_image_alternatives (E.map sextetQuotient) hn hp with hb | hz | hf
  · left
    have heker : E ≤ sextetQuotient.ker := by
      intro x hx
      exact mem_bot.mp (hb ▸ (mem_map_of_mem sextetQuotient hx))
    have hp : IsPGroup 2 E := (SextetCore.atlas_kernel_elementary.isPGroup 2 _).to_le heker
    have hi := hpE.hom_eq_one_of_isPGroup hp (MonoidHom.id E)
    have he : E = ⊥ := by
      apply eq_bot_iff.mpr
      intro x hx
      exact congrArg Subtype.val (DFunLike.congr_fun hi ⟨x,hx⟩)
    simp [he]
  · right; left
    refine ⟨?_, twelve_lt_card_of_scalar_mem E hE ?_⟩
    · rw [hc, hz, hexCoordinateSix_kernel, Nat.card_zpowers, hexZ_order]
    · rw [hz, hexCoordinateSix_kernel]
      exact mem_zpowers hexZ
  · right; right
    rw [hc, hf]
    exact hexEven_card

end SubnormalSextet

/-- Every native M₂₄ sextet stabilizer has exactly the required intrinsic
subnormal two-perfect order alternatives. -/
theorem subnormal_sextet_orders (X : Sextet) (E : Subgroup (sextetStabilizer X))
    (hE : E.IsSubnormal) (hpE : IsPPerfect 2 E) :
    Nat.card E = 1 ∨
      (Nat.card (E ⧸ pCore 2 E) = 3 ∧ 12 < Nat.card E) ∨
        Nat.card (E ⧸ pCore 2 E) = 1080 := by
  let e := (MathieuCode.SextetLayers.CoordinateTransport.nativeStabilizerEquiv X).symm
  let D := E.map e.toMonoidHom
  let eE : E ≃* D := e.subgroupMap E
  have hn : D.IsSubnormal := hE.map e.surjective
  have hp : IsPPerfect 2 D := hpE.of_surjective eE.toMonoidHom eE.surjective
  have hc := Nat.card_congr eE.toEquiv
  have hq := Nat.card_congr (QuotientGroup.congr _ _ eE (pCore_map_iso 2 eE)).toEquiv
  rw [hc, hq]
  exact SubnormalSextet.atlas_orders D hn hp

end Sporadic.Mathieu.M24LocalGeometry
