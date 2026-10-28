module

public import CFSG.Quasithin.Chapter10.SourceA5PointQuasisimple
public import Theory.AtlasPort.LinearGroups.G2.LieCoreSpecialness
public import Theory.SpecificGroups.Triality.ParabolicLocalStructure

/-!
# Small-center parabolics in the original A5 point-centralizer argument

The original moved subgroup forces a central elementary subgroup of order at
least sixteen in the two-core of every central image of the local component.
This bound survives any specified identification of the containing central
quotient. The first G₂ parabolic and the arms triality parabolic have core
centers of order q, so neither can be this actual image when q = 4.

The statements retain the literal restriction of I → I/Z(I) and the marked
parabolic equality. These are the small-core-center eliminations in the
quasisimple inspection of Aschbacher–Smith 10.2.9, printed pp.750–751,
using A.3.12/A.3.14 and the parabolic calculations F.1.12.
-/

public section
open Subgroup
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)

include D

/-- The core-center bound in any specified coordinates on the containing
central quotient. The kernel is proved central from the literal quotient map. -/
theorem source_a5_marked_center_quotient_core_center_card
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    {I : Subgroup G} (hLI : L ≤ I) {H : Type*} [Group H] [Finite H]
    (eI : (I ⧸ center I) ≃* H) :
    16 ≤ Nat.card (center (pCore 2
      ((L.subgroupOf I).map (eI.toMonoidHom.comp (QuotientGroup.mk' (center I)))))) := by
  let A := L.subgroupOf I
  let q := eI.toMonoidHom.comp (QuotientGroup.mk' (center I))
  let k : L ≃* A := (subgroupOfEquivOfLe hLI).symm
  let f := (q.subgroupMap A).comp k.toMonoidHom
  have hf : Function.Surjective f := (q.subgroupMap_surjective A).comp k.surjective
  have hk : f.ker ≤ center L := by
    intro l hl
    have hh := congrArg Subtype.val (MonoidHom.mem_ker.mp hl)
    change eI (QuotientGroup.mk' (center I) (inclusion hLI l)) = 1 at hh
    have hc := (QuotientGroup.eq_one_iff (inclusion hLI l)).mp
      (eI.injective (hh.trans (map_one eI).symm))
    apply mem_center_iff.mpr
    intro m
    exact Subtype.ext (congrArg I.subtype (mem_center_iff.mp hc (inclusion hLI m)))
  exact source_a5_central_image_core_center_card D e f hf hk

/-- The first G₂(4) parabolic residual cannot be the actual central image. -/
theorem source_a5_point_not_g2_first_parabolic
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    {I : Subgroup G} (hLI : L ≤ I)
    {F : Type*} [Field F] [Finite F] [CharP F 2] (hF : Nat.card F = 4)
    (eI : (I ⧸ center I) ≃* Atlas.G2.Model F) :
    (L.subgroupOf I).map (eI.toMonoidHom.comp (QuotientGroup.mk' (center I))) ≠
      Atlas.G2.LieParabolicSetup.local₁ := by
  intro hmark
  have h := source_a5_marked_center_quotient_core_center_card D e hLI eI
  rw [hmark, Nat.card_congr
    (Atlas.G2.LieParabolicSetup.local₁CoreCenterEquiv (F := F)).toEquiv,
    Nat.card_congr (Multiplicative.toAdd : Multiplicative F ≃ F), hF] at h
  omega

/-- The arms triality parabolic at q = 4 cannot be the actual central image. -/
theorem source_a5_point_not_triality_arms_parabolic
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    {I : Subgroup G} (hLI : L ≤ I)
    (P : Triality.Standard.Parameters) (hp : P.prime = 2) (hq : P.q = 4)
    (eI : (I ⧸ center I) ≃* Triality.Standard.Carrier P) :
    (L.subgroupOf I).map (eI.toMonoidHom.comp (QuotientGroup.mk' (center I))) ≠
      Triality.Standard.Parabolics.localFactor P .arms := by
  intro hmark
  have h := source_a5_marked_center_quotient_core_center_card D e hLI eI
  rw [hmark, Triality.Standard.Parabolics.localFactor_arms_twoCore_center_card P hp,
    hq] at h
  omega

end CFSG.Quasithin.Chapter10
