module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.PairingControl.FirstPairing.StepThree.RankOne.Source
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.PairingControl.FirstPairing.StepThree.RankOne.SmallInvariant.Transport
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.PairingControl.FirstPairing.Orientation.QuotientApplication.Verification.CommutatorBounds.CyclicLocalization.Layer

/-!
# Residual localization in the actual fixed-core quotient

The natural U marking descends to G_alpha/D_alpha. Its line residual has
exactly the expected matrix image. For a small elementary K in B, the layer
KZ is a natural-by-trivial module in this quotient, and its residual-invariant
K-image lies in the natural Z-image. Relative normality and every quotient
map are retained. Source: MS93 (4.3.2)(3), printed p.884.
-/
@[expose] public section
open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.PairingControl.FirstPairing.StepThree.RankOne.SmallInvariant
open RankOnePairing Orientation Orientation.QuotientApplication
open Matrix.PSL3Two.MarkedAutomorphisms
variable {M : Type*} [Group M] {L R : Subgroup M} {a : Vertex R}

/-- The marked projection on the actual quotient, compatible with naturalProjection. -/
def markedQuotientProjection (o : MovingOrientationAt a) : LocalQuotient a →* SL :=
  o.naturalU.marking.toMonoidHom.comp
    (quotientProjection a o.projection o.natural_section.projection_kernel)

theorem markedQuotientProjection_comp (o : MovingOrientationAt a) :
    (markedQuotientProjection o).comp (quotientMap a) = naturalProjection o := rfl

theorem markedQuotientProjection_surjective (o : MovingOrientationAt a) :
    Function.Surjective (markedQuotientProjection o) :=
  o.naturalU.marking.surjective.comp
    (quotientProjection_surjective a _ o.natural_section.projection_surjective _)

theorem markedQuotientProjection_kernel (o : MovingOrientationAt a) :
    (markedQuotientProjection o).ker = quotientImage a (Q R a) := by
  rw [markedQuotientProjection, MonoidHom.ker_comp_of_injective _ _
    o.naturalU.marking.injective, quotientProjection_kernel]

variable [Finite M] {source : LocalSource L R} {geometry : Geometry R}

/-- The natural image with the U marking absorbed into the projection. -/
noncomputable def quotientNatural (modules : ModuleFacts source geometry)
    (ha : color R a = false) (o : MovingOrientationAt a) :
    NaturalFactor (markedQuotientProjection o) ⊤ (quotientImage a (Z R a)) ⊥ := by
  let f : FrameAt a := ⟨o.projection,o.naturalU,o.natural_section⟩
  let n := naturalZ modules a ha f
  exact {
    marking := MulEquiv.refl SL
    coordinates := n.coordinates
    surjective := n.surjective
    kernel := n.kernel
    normalized := n.normalized
    action := n.action }

theorem quotientNatural_marking (modules : ModuleFacts source geometry)
    (ha : color R a = false) (o : MovingOrientationAt a) :
    (quotientNatural modules ha o).marking = MulEquiv.refl SL := rfl

/-- The actual ordered residual maps onto the embedded model two-residual. -/
theorem lineResidual_image (source : LocalSource L R) (ha : color R a = false)
    (o : MovingOrientationAt a) (flag : SL) :
    ((lineResidual o flag).map (quotientMap a)).map (markedQuotientProjection o) =
      residual (modelParabolic flag true) := by
  let := finite_stabilizer R a
  rw [map_map, markedQuotientProjection_comp, lineResidual_eq source ha,
    map_embedded_pResidual]
  have he : (lineParabolic o flag).map (naturalProjection o) = modelParabolic flag true :=
    map_comap_eq_self_of_surjective (naturalProjection_surjective o) _
  rw [he]
  rfl

/-- No element of the natural Z-image is fixed by this line residual. -/
theorem quotient_line_fixed_eq_bot (modules : ModuleFacts source geometry)
    (ha : color R a = false) (o : MovingOrientationAt a) (flag : SL) :
    quotientImage a (Z R a) ⊓
      centralizer ((lineResidual o flag).map (quotientMap a) : Set (LocalQuotient a)) = ⊥ :=
  natural_line_residual_fixed_eq_bot (markedQuotientProjection o) _ _
    (quotientNatural modules ha o) (quotientNatural_marking modules ha o) flag
    (lineResidual_image source ha o flag)

/-- A small elementary subgroup of B, normalized by Q and the actual line
residual, has image in the natural subgroup of G_alpha/D_alpha. -/
theorem quotient_small_invariant_le_Z (source : LocalSource L R)
    (hb : 2 < geometry.b R) (modules : ModuleFacts source geometry)
    (ha : color R a = false) (o : MovingOrientationAt a) (flag : SL)
    (K : Subgroup (FreeAmalgam R))
    (hKB : K ≤ B R a (geometry.Z_normal a))
    (hKe : IsElementaryAbelian 2 K) (hcard : Nat.card K ≤ 4)
    (hQK : Q R a ≤ normalizer (K : Set (FreeAmalgam R)))
    (hTK : lineResidual o flag ≤
      normalizer (K.subgroupOf (stabilizer R a) : Set (stabilizer R a))) :
    quotientImage a K ≤ quotientImage a (Z R a) := by
  let S := stabilizer R a
  let f : FrameAt a := ⟨o.projection,o.naturalU,o.natural_section⟩
  let π := markedQuotientProjection o
  let Q₀ := quotientImage a (Q R a)
  let Z₀ := quotientImage a (Z R a)
  let K₀ := quotientImage a K
  let E := component (projection f) flag
  let T := (lineResidual o flag).map (quotientMap a)
  let := finite_stabilizer R a
  let := quotientImage_normal a (Q R a) (Q_normalized R a)
  let := quotientImage_normal a (Z R a) (Z_normalized R a)
  have hKQ : K ≤ Q R a :=
    hKB.trans ((EdgeTransfer.B_le_radius hb a ha).trans (geometry.V_le_Q hb a ha))
  have hKS : K ≤ S := hKQ.trans (fun _ hx => hx.1)
  have hZQ : Z R a ≤ Q R a := (Z_le_VBall R a 2).trans (geometry.V_le_Q hb a ha)
  let : IsElementaryAbelian 2 K := hKe
  let : IsElementaryAbelian 2 (K.subgroupOf S) := IsElementaryAbelian.subgroupOf hKS
  let : IsElementaryAbelian 2 K₀ := IsElementaryAbelian.map _
  let : IsElementaryAbelian 2 (Z R a) := by
    rw [← modules.X_eq_Z a ha]
    exact omegaCenter_elementary _
  let : IsElementaryAbelian 2 ((Z R a).subgroupOf S) :=
    IsElementaryAbelian.subgroupOf (Z_le_stabilizer R a)
  let : IsElementaryAbelian 2 Z₀ := IsElementaryAbelian.map _
  have hQK₀ : Q₀ ≤ normalizer (K₀ : Set (LocalQuotient a)) :=
    (map_mono ((comap_mono hQK).trans (le_normalizer_comap S.subtype))).trans
      (le_normalizer_map (quotientMap a))
  have hTK₀ : T ≤ normalizer (K₀ : Set (LocalQuotient a)) :=
    (map_mono hTK).trans (le_normalizer_map (quotientMap a))
  have hn : (residual (modelParabolic flag true)).comap π ≤ normalizer K₀ := by
    rw [← lineResidual_image source ha o flag, comap_map_eq,
      markedQuotientProjection_kernel]
    exact sup_le hTK₀ hQK₀
  have hc : Nat.card K₀ ≤ 4 := by
    apply (Nat.le_of_dvd (Nat.card_pos (α := K.subgroupOf S))
      ((K.subgroupOf S).card_map_dvd (quotientMap a))).trans
    rw [Nat.card_congr (subgroupOfEquivOfLe hKS).toEquiv]
    exact hcard
  have hKE : ⁅K₀,E⁆ ≤ Z₀ := by
    rw [commutator_comm]
    apply commutator_le.mpr
    intro e he k hk
    exact (mem_centralizerModulo_iff.mp
      (quotientImage_B_le_fixed (f := f) (geometry := geometry) source ha flag
        ((map_mono (comap_mono hKB)) hk))).2 e he
  have hE : E.map π = ⊤ := by
    change E.map (o.naturalU.marking.toMonoidHom.comp (projection f)) = ⊤
    rw [← map_map, component_map _
      (quotientProjection_surjective a _ o.natural_section.projection_surjective _) flag,
      map_top_of_surjective _ o.naturalU.marking.surjective]
  exact small_residual_le_natural π (markedQuotientProjection_surjective o)
    Q₀ E Z₀ K₀ (markedQuotientProjection_kernel o) hE
    (CyclicLocalization.component_sup_Q source ha f flag) (quotientNatural modules ha o)
    (map_mono (comap_mono hZQ)) (map_mono (comap_mono hKQ))
    ((Q_isPGroup R source.two_group source.core_le a ha).comap_subtype.map _)
    hQK₀ (SelectedSeed.Z_centralizes_Q (geometry := geometry) ha) hKE
    (CyclicLocalization.quotient_Q_fixed_eq_bot source ha f flag) flag true hc hn

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.PairingControl.FirstPairing.StepThree.RankOne.SmallInvariant
