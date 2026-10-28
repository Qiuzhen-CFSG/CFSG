module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.LocalCommutator.NaturalCase.Opposite.Quotient
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.LocalCommutator.NaturalCase.SeedBounds
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.PairingControl.FirstPairing.Orientation.QuotientApplication.Verification.NaturalGeneration
/-!
# The literal W-section in the fixed-core quotient

Coordinates on all of W = localZSpan descend through G_c/D_c with kernel
exactly image(W intersect B_c). The coordinate marking is unchanged. The
source triple bound puts [image(W),image(Q_c)] in that kernel, and the actual
component fixes it modulo image(Z_c).

Residual commutator idempotence shows that no residual-fixed element remains
in image(Q_c) after quotienting by D_c. Together these facts provide the
precise input for small cyclic localization, without a full-radius section.

Source: Meierfrankenfeld--Stellmacher (1993), (4.4.1), pp.890--891,
using the quotient and residual conventions in the application on p.883.
-/

@[expose] public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
open scoped commutatorElement
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.LocalCommutator.NaturalCase.Favorable
open RankOnePairing
open Escape.PairingControl.FirstPairing
open Orientation.QuotientApplication
open NaturalGeneration
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}
variable {source : LocalSource L R} {geometry : Geometry R} {a c : Vertex R}

/-- The image of the fixed part of W, not an unrelated abstract denominator. -/
noncomputable def fixedSpan (geometry : Geometry R) (a c : Vertex R) :
    Subgroup (LocalQuotient c) :=
  quotientImage c (localZSpan R a c ⊓ B R c (geometry.Z_normal c))

omit [Finite M] in
theorem fixedSpan_le : fixedSpan geometry a c ≤ quotientImage c (localZSpan R a c) :=
  map_mono (comap_mono inf_le_left)

omit [Finite M] in
theorem fixedSpan_normal : (fixedSpan geometry a c).Normal := by
  let := Opposite.fixed_normal (geometry := geometry) c
  let : ((localZSpan R a c).subgroupOf (stabilizer R c)).Normal :=
    normal_subgroupOf_of_le_normalizer (localZSpan_normalized R a c)
  exact Normal.map (inferInstanceAs
    (((localZSpan R a c).subgroupOf (stabilizer R c) ⊓
      (B R c (geometry.Z_normal c)).subgroupOf (stabilizer R c)).Normal))
    (quotientMap c) (QuotientGroup.mk'_surjective _)

/-- Whole-section coordinates descend through D_c without enlarging their kernel. -/
noncomputable def quotientNaturalW (source : LocalSource L R) (hc : color R c = false)
    (hd : (cosetGraph R).dist a c = 2) (hb : 2 < geometry.b R) (f : FrameAt a c) :
    NaturalFactor f.projection ⊤ (quotientImage c (localZSpan R a c))
      (fixedSpan geometry a c) := by
  let n := Opposite.spanNatural source hc hd hb f
  let S := stabilizer R c
  let W := (localZSpan R a c).subgroupOf S
  let N := (localZSpan R a c ⊓ B R c (geometry.Z_normal c)).subgroupOf S
  have nn : NaturalFactor f.sectionData.projection ⊤ W N := by
    refine { n with kernel := ?_ }
    rw [n.kernel]
    ext x
    exact ⟨fun hx => ⟨x.property, hx⟩, fun hx => hx.2⟩
  apply mapNaturalFactor nn (quotientMap c) (QuotientGroup.mk'_surjective _) rfl
    (comap_mono inf_le_left)
  rintro x ⟨hxW, hxD⟩
  exact ⟨hxW, denominator_inf_V_le_B (geometry := geometry)
    ⟨localZSpan_le_V R hd.le hxW, hxD⟩⟩

@[simp] theorem quotientNaturalW_marking (source : LocalSource L R) (hc : color R c = false)
    (hd : (cosetGraph R).dist a c = 2) (hb : 2 < geometry.b R) (f : FrameAt a c) :
    (quotientNaturalW source hc hd hb f).marking =
      f.sectionData.module_section.natural.marking := rfl

theorem component_eq_residual (source : LocalSource L R) (hc : color R c = false)
    (f : FrameAt a c) (flag : SL) : component f.projection flag =
      pResidual 2 (LocalQuotient c) := by
  rw [component, rankOne_parabolic_generation _
    (quotientProjection_surjective c _ f.sectionData.module_section.projection_surjective _)
    (quotientProjection_kernel_isPGroup source c hc _ _)]

theorem component_eq_image (source : LocalSource L R) (hc : color R c = false)
    (f : FrameAt a c) (flag : SL) : component f.projection flag =
      quotientImage c (Ltilde R c) := by
  let := finite_stabilizer R c
  rw [component_eq_residual source hc, quotientImage, Ltilde_subgroupOf, quotientMap,
    map_pResidual_of_surjective 2 _ (QuotientGroup.mk'_surjective _)]

theorem Z_le_fixedSpan (hc : color R c = false)
    (hd : (cosetGraph R).dist a c = 2) (hb : 2 < geometry.b R) :
    quotientImage c (Z R c) ≤ fixedSpan geometry a c :=
  map_mono (comap_mono (le_inf (center_Z_le_span hc hd) (Escape.EdgeTransfer.Z_le_B hb c hc)))

omit [Finite M] in
/-- The source triple bound controls the Q_c displacement on the whole W-image. -/
theorem span_commutator_le_fixedSpan (hd : (cosetGraph R).dist a c = 2) (f : FrameAt a c) :
    ⁅quotientImage c (localZSpan R a c), quotientImage c (Q R c)⁆ ≤ fixedSpan geometry a c := by
  let := geometry.Z_normal c
  let := f.sectionData.module_section.normal_group
  have hh : ⁅(localZSpan R a c).subgroupOf (stabilizer R c),
      (Q R c).subgroupOf (stabilizer R c)⁆ ≤
      centralizerModulo ((localZSpan R a c).subgroupOf (stabilizer R c))
        (pResidual 2 (stabilizer R c)) ((Z R c).subgroupOf (stabilizer R c)) := by
    intro x hx
    apply mem_centralizerModulo_iff.mpr
    refine ⟨commutator_le_left _ _ hx, ?_⟩
    intro l hl
    apply f.sectionData.module_section.triple_le
    rw [commutator_comm]
    exact commutator_mem_commutator hl hx
  rw [Opposite.span_fixed_eq (geometry := geometry) hd] at hh
  exact (map_commutator _ _ (quotientMap c)).ge.trans (map_mono hh)

/-- The fixed part is fixed by the literal source component modulo the Z-image. -/
theorem fixedSpan_commutator (source : LocalSource L R) (hc : color R c = false)
    (hd : (cosetGraph R).dist a c = 2) (f : FrameAt a c) (flag : SL) :
    ⁅fixedSpan geometry a c, component f.projection flag⁆ ≤ quotientImage c (Z R c) := by
  let := geometry.Z_normal c
  rw [component_eq_image source hc f flag, fixedSpan, quotientImage, quotientImage,
    Ltilde_subgroupOf, ← map_commutator, ← Opposite.span_fixed_eq (geometry := geometry) hd]
  apply map_mono
  rw [commutator_comm]
  apply commutator_le.mpr
  intro l hl x hx
  exact (mem_centralizerModulo_iff.mp hx).2 l hl

omit [Finite M] in
include geometry in
theorem Z_centralizes_kernel (hc : color R c = false) (f : FrameAt a c) :
    quotientImage c (Z R c) ≤ centralizer (f.projection.ker : Set (LocalQuotient c)) := by
  rw [FrameAt.projection, quotientProjection_kernel]
  apply commutator_eq_bot_iff_le_centralizer.mp
  rw [← quotientImage_commutator c _ _ (Z_le_stabilizer R c)
    (show Q R c ≤ stabilizer R c from fun _ hx => hx.1), geometry.centralizes c hc]
  simp [quotientImage]

/-- Central errors disappear under a finite two-residual acting on a two-group. -/
private theorem centralizes_of_central_error {G : Type*} [Group G] [Finite G]
    (P E D : Subgroup G) [D.Normal] (hp : IsPGroup 2 P)
    (he : IsPPerfect 2 E) (hDP : D ≤ P) (hDE : ⁅D,E⁆ = ⊥)
    (x : G) (hx : x ∈ P) (hcomm : ∀ y ∈ E, ⁅x,y⁆ ∈ D) :
    x ∈ centralizer (E : Set G) := by
  let N := commutatorPreimage P E D
  have hDN : D ≤ N := le_commutatorPreimage hDP (hDE.le.trans bot_le)
  have hNE : ⁅N,E⁆ ≤ D := commutator_commutatorPreimage_le P E D le_normalizer_of_normal
  have hn : E ≤ normalizer N :=
    le_normalizer_iff_commutator_le_left.mpr (hNE.trans hDN)
  have hz : ⁅N,E⁆ = ⊥ := by
    rw [← commutator_isPPerfect_idempotent E N he
      (hp.to_le (commutatorPreimage_le P E D)) hn]
    exact le_bot_iff.mp ((commutator_mono hNE le_rfl).trans hDE.le)
  apply commutator_eq_bot_iff_le_centralizer.mp hz
  change x ∈ commutatorPreimage P E D
  rw [commutatorPreimage_eq_inf_comap_centralizer]
  refine ⟨hx, ?_⟩
  rintro _ ⟨y,hy,rfl⟩
  have hc : ⁅QuotientGroup.mk' D x, QuotientGroup.mk' D y⁆ = 1 := by
    rw [← map_commutatorElement]
    exact (QuotientGroup.eq_one_iff _).mpr (hcomm y hy)
  exact (commutatorElement_eq_one_iff_mul_comm.mp hc).symm


/-- Passing to D_c removes every residual-fixed element of the kernel. -/
theorem kernel_fixed_eq_bot (source : LocalSource L R) (hc : color R c = false)
    (f : FrameAt a c) (flag : SL) :
    f.projection.ker ⊓ centralizer (component f.projection flag : Set (LocalQuotient c)) = ⊥ := by
  let := finite_stabilizer R c
  rw [FrameAt.projection, quotientProjection_kernel]
  change quotientImage c (Q R c) ⊓ centralizer (component f.projection flag : Set _) = ⊥
  rw [component_eq_image source hc f flag]
  apply bot_unique
  rintro x ⟨⟨q,hq,rfl⟩,hfix⟩
  have hDE : ⁅denominator c,pResidual 2 (stabilizer R c)⁆ = ⊥ := by
    apply commutator_eq_bot_iff_le_centralizer.mpr
    rw [denominator_eq]
    exact inf_le_right
  have hcomm : ∀ y ∈ pResidual 2 (stabilizer R c), ⁅q,y⁆ ∈ denominator c := by
    intro y hy
    apply (QuotientGroup.eq_one_iff _).mp
    change quotientMap c ⁅q,y⁆ = 1
    rw [map_commutatorElement]
    apply commutatorElement_eq_one_iff_mul_comm.mpr
    exact (hfix _ (mem_map_of_mem _ (show y ∈ (Ltilde R c).subgroupOf (stabilizer R c) by
      rw [Ltilde_subgroupOf]; exact hy))).symm
  have hfix := centralizes_of_central_error ((Q R c).subgroupOf (stabilizer R c))
    (pResidual 2 (stabilizer R c)) (denominator c)
    (Q_isPGroup R source.two_group source.core_le c hc).comap_subtype
    (isPPerfect_pResidual 2) (by rw [denominator_eq]; exact inf_le_left) hDE q hq hcomm
  apply (QuotientGroup.eq_one_iff q).mpr
  rw [denominator_eq]
  exact ⟨hq,hfix⟩

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.LocalCommutator.NaturalCase.Favorable
