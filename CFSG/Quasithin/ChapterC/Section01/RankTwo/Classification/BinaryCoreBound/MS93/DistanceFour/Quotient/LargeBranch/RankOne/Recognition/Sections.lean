module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Flags.RankOne.Triple
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Quotient.LargeBranch.RankOne.Recognition.Modules
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Quotient.LargeBranch.RankOne.Recognition.Transport
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Quotient.LargeBranch.RankOne.Recognition.Sections.Geometry
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Quotient.LargeBranch.RankOne.Recognition.Sections.Actions
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Quotient.LargeBranch.RankOne.Recognition.Sections.FromFrame

/-!
# Rank-one sections in the large-intersection branch

`rankOneSections` proves both section calculations from the original
source hypotheses. `exists_frame` constructs the marked frame using the
genuine (4.6.8) flag theorem, and `naturalSections_of_frame` assembles the
two literal sections for that frame. `FromFrame` supplies the first natural plane and
the second direct sum, after proving the actual commutator-map and cubic
fixed-space calculations. Both maps have exact relative kernels and
retain the ambient conjugation formula for the same source-ordered
residual and its marked quotient onto the literal SL2(2)'.

The denominator of the second section is the preimage Y of
C_{K/Z_alpha}(T_beta), where K = V_alpha intersect Q_c. Both relative
normality assertions and residual invariance are included in the result.
The radius module is constructed from the original inputs. No additional
flag, action, fixed-space or actor-descent premise remains. The section
calculations also hold without the large-intersection assumption, as
recorded separately by `exists_naturalSections`.

Source: Meierfrankenfeld--Stellmacher (1993), (4.6.12)(1)--(2), printed
p.910, using the flag notation on p.905 and (4.6.9) on p.908.
-/

@[expose] public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.LargeBranch.RankOne.Sections
open Flags.RankOne

variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}

/-- The actual two sections in (4.6.12)(1)--(2), with a common source marking.
This is output data: `naturalSections_of_frame` constructs every field
from the marked frame and the common and radius facts. The maps retain the literal ambient
denominators, and the linear coordinates identify the original quotient
spaces with natural modules for the derived subgroup SL2(2)'. -/
structure NaturalSections (source : LocalSource L R) (c : Vertex R) where
  frame : Frame source
  layer : LayerModule source (V R (alpha R))
  Z_le_Y : Z R (alpha R) ≤ fixedPreimage c
  Y_le_K : fixedPreimage c ≤ intersection c
  K_normal : ((intersection c).subgroupOf (V R (alpha R))).Normal
  Y_normal : ((fixedPreimage c).subgroupOf (intersection c)).Normal
  normalizes_K : flagResidual source frame.orientation ≤ normalizer (intersection c)
  normalizes_Y : flagResidual source frame.orientation ≤ normalizer (fixedPreimage c)
  first_index : (intersection c).relIndex (V R (alpha R)) = 4
  first_card : Nat.card (layer.Space ⧸ layer.subspace (intersection c)) = 4
  firstCoordinates : (layer.Space ⧸ layer.subspace (intersection c)) ≃ₗ[ZMod 2]
    (Fin 2 → ZMod 2)
  firstMap : V R (alpha R) →* Multiplicative (Fin 2 → ZMod 2)
  first_surjective : Function.Surjective firstMap
  first_kernel : firstMap.ker = (intersection c).subgroupOf (V R (alpha R))
  first_coordinates : ∀ v, Multiplicative.toAdd (firstMap v) =
    firstCoordinates ((layer.quotientMap (intersection c) v).toAdd)
  first_action : ∀ (g : flagResidual source frame.orientation) (v w : V R (alpha R)),
    (w : FreeAmalgam R) = g * (v : FreeAmalgam R) * (g : FreeAmalgam R)⁻¹ →
      Multiplicative.toAdd (firstMap w) =
        (markedResidualProjection source frame g).val.val.mulVec
          (Multiplicative.toAdd (firstMap v))
  copies : ℕ
  secondCoordinates : ((layer.subspace (intersection c)) ⧸
    (layer.subspace (fixedPreimage c)).comap (layer.subspace (intersection c)).subtype) ≃ₗ[ZMod 2]
      (Fin copies → Fin 2 → ZMod 2)
  secondMap : intersection c →* Multiplicative (Fin copies → Fin 2 → ZMod 2)
  second_surjective : Function.Surjective secondMap
  second_kernel : secondMap.ker = (fixedPreimage c).subgroupOf (intersection c)
  second_coordinates : ∀ v : intersection c, Multiplicative.toAdd (secondMap v) =
    secondCoordinates ((layer.sectionMap (intersection c) (fixedPreimage c)
      (by rw [intersection]; exact inf_le_left) v).toAdd)
  second_action : ∀ (g : flagResidual source frame.orientation)
    (v w : intersection c) (j : Fin copies),
    (w : FreeAmalgam R) = g * (v : FreeAmalgam R) * (g : FreeAmalgam R)⁻¹ →
      (Multiplicative.toAdd (secondMap w)) j =
        (markedResidualProjection source frame g).val.val.mulVec
          ((Multiplicative.toAdd (secondMap v)) j)

variable {source : LocalSource L R} {geometry : Geometry R}

/-- Assemble both source section calculations for the same supplied marked
frame, constructing the radius realization as well. This conditional
consumer leaves only the (4.6.8) frame construction to source assembly. -/
theorem naturalSections_of_frame (common : CommonFacts R source geometry)
    (radius : RadiusFacts R geometry) (f : Frame source) (hb : geometry.b R = 4)
    (s : CriticalSegment geometry) (hbc : Adjacent R (beta R) s.middle) :
    Nonempty (NaturalSections source s.middle) := by
  obtain ⟨d⟩ := exists_radiusModule common radius
  obtain ⟨e₁, φ₁, honto₁, hker₁, hcoords₁, hact₁⟩ :=
    exists_first_natural_map common radius f hb s hbc d
  obtain ⟨n, e₂, φ₂, honto₂, hker₂, hcoords₂, hact₂⟩ :=
    exists_second_natural common radius f hb s hbc d
  exact ⟨{
    frame := f
    layer := d
    Z_le_Y := Z_le_fixedPreimage common s.first_distance
    Y_le_K := commutatorPreimage_le _ _ _
    K_normal := radius_inf_kernel_normal common radius rfl s.first_distance
    Y_normal := fixedPreimage_normal common hbc
    normalizes_K := residual_normalizes_intersection common radius f s.first_distance hbc
    normalizes_Y := residual_normalizes_fixedPreimage common radius f s.first_distance hbc
    first_index := intersection_index_four common radius f hb s hbc
    first_card := first_quotient_card common radius f hb s hbc d
    firstCoordinates := e₁
    firstMap := φ₁
    first_surjective := honto₁
    first_kernel := hker₁
    first_coordinates := hcoords₁
    first_action := hact₁
    copies := n
    secondCoordinates := e₂
    secondMap := φ₂
    second_surjective := honto₂
    second_kernel := hker₂
    second_coordinates := hcoords₂
    second_action := hact₂ }⟩

/-- Construct the genuine marked frame from the original source hypotheses,
including the intrinsic edge-core equality and the central triple bound. -/
theorem exists_frame (common : CommonFacts R source geometry)
    (radius : RadiusFacts R geometry) (hb : geometry.b R = 4) :
    Nonempty (Frame source) :=
  exists_frame_of_flagControl (flagControl source geometry common hb radius.toEarlyFacts)

/-- Both section calculations hold at every critical midpoint on the
distinguished edge, with the marked frame constructed from the source. -/
theorem exists_naturalSections (common : CommonFacts R source geometry)
    (radius : RadiusFacts R geometry) (hb : geometry.b R = 4)
    (s : CriticalSegment geometry) (hbc : Adjacent R (beta R) s.middle) :
    Nonempty (NaturalSections source s.middle) := by
  obtain ⟨f⟩ := exists_frame common radius hb
  exact naturalSections_of_frame common radius f hb s hbc

/-- MS93 (4.6.12)(1)--(2) in the large-intersection branch, with no extra
flag, module, fixed-space or actor-descent hypothesis. The chosen frame,
its intrinsic core identification, the literal quotient maps, their exact
relative kernels and their residual action equations are all retained. -/
theorem rankOneSections (common : CommonFacts R source geometry)
    (radius : RadiusFacts R geometry) (hb : geometry.b R = 4)
    (s : CriticalSegment geometry) (_hs : ¬ s.SmallIntersection)
    (hbc : Adjacent R (beta R) s.middle) :
    Nonempty (NaturalSections source s.middle) :=
  exists_naturalSections common radius hb s hbc

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.LargeBranch.RankOne.Sections
