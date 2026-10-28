module

public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Symplectic.CharacteristicBlock.RootClosure
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Symplectic.CharacteristicBlock.MSRecognition
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.DistanceTwoRecognition.PairedOrbit

/-!
# Symplectic closure from a distance-two replacement

The full-image MS-pair lives on the literal product L O₂(G₁), with the
original marked quotient action. The whole-core theorem at distance two
makes its original component short and supplies its actual natural block
module at the original field degree. Short-group irreducibility, together
with O₂(L)=[O₂(L),L], then gives O₂(L)=V for the chosen perfect module.
The already proved root-image and terminal arguments finish abelianness.

Thus this closure application does not require the field-four restriction
or the original-radical saturation needed for the complete C.1.32 block
classification. The existence of a distance-two characteristic replacement
is still an explicit input, owned by qt-c132-nonbinary-distance-reduction.
It is not implied merely by positivity and evenness of the critical distance.
The closure owner qt-d-1222-natural-closure-sp4 retains its final discharge;
qt-d-1222-natural-closure retains the preceding source-geometry discharge.

Source: Aschbacher--Smith C.1.7 and 11.5.7, printed pp.123,782--784;
Meierfrankenfeld--Stellmacher (1993), (3.6), printed pp.870--872.
-/

public noncomputable section
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Symplectic
open Subgroup Theory.SpecificGroups.SymplecticFour
open CFSG.Quasithin.Chapter12.Section02
open ChapterC.BinaryMS.MS93
open ChapterC.RankTwo.NonbinarySymplectic
open ChapterB.QuasisimpleSource Representation.BinaryOffender
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : ChosenModule T L V} (E : Geometry D) (m : MarkedFlag E)

namespace CharacteristicBlock
include m

/-- The distance-two whole-core theorem transports to the original L,
including the actual conjugation-module model and the unchanged degree. -/
theorem msPair_short_and_natural_of_distance_two
    (hms : LocalGeometry.Normalizers.PointBlocks.NonbinaryMSPair
      E.input.field L (E.G₁.pCoreIn 2))
    (d : CharacteristicReduction (L.subgroupOf (L ⊔ E.G₁.pCoreIn 2))
      ((E.G₁.pCoreIn 2).subgroupOf (L ⊔ E.G₁.pCoreIn 2)))
    (graph : ChapterC.BinaryMS.MS93.Geometry d.radical) (hb : graph.b d.radical = 2) :
    ChapterC.IsShort L ∧ ∃ F : BinaryField, F.degree = E.input.field.degree ∧
      ChapterC.IsLinearBlockModel L (binarySymplectic F) := by
  obtain ⟨hs,F,hF,hmodel⟩ := DistanceTwoRecognition.short_and_natural_of_distance_two
    (intrinsicMSInput E m hms) d graph hb
  let e : L.subgroupOf (L ⊔ E.G₁.pCoreIn 2) ≃* L := subgroupOfEquivOfLe le_sup_left
  exact ⟨hs.of_mulEquiv e,F,hF,hmodel.of_mulEquiv e⟩

/-- On the actual closure MS-pair, distance two identifies O₂(L) with V.
The fixed part of the original chosen module is retained throughout. -/
theorem msPair_core_eq_seed_of_distance_two
    (hms : LocalGeometry.Normalizers.PointBlocks.NonbinaryMSPair
      E.input.field L (E.G₁.pCoreIn 2))
    (d : CharacteristicReduction (L.subgroupOf (L ⊔ E.G₁.pCoreIn 2))
      ((E.G₁.pCoreIn 2).subgroupOf (L ⊔ E.G₁.pCoreIn 2)))
    (graph : ChapterC.BinaryMS.MS93.Geometry d.radical) (hb : graph.b d.radical = 2) :
    L.pCoreIn 2 = V :=
  core_eq_chosen_of_short D
    (msPair_short_and_natural_of_distance_two E m hms d graph hb).1
    (core_eq_commutator E m)

end CharacteristicBlock

variable
    (g : Sp E.input.field.Carrier)
    (hpoint : m.flag.space 0 = (point E.input.field.Carrier).map (toLinear g).toLinearMap)
    (hthree : m.flag.space 2 =
      ((form E.input.field.Carrier).orthogonal (point E.input.field.Carrier)).map
        (toLinear g).toLinearMap)
    (hX : LocalGeometry.IsCartan T L E.X)
    (hcartan : PointModel.image m (E.L₁ ⊔ E.X) =
      pointParabolic.map (MulAut.conj g).toMonoidHom)
    (hn3 : E.L₁ ⊔ (T : Subgroup G) ≤ normalizer (E.V₃ : Set G))
    (hirr : ∀ A : Subgroup G, E.V₁ ≤ A → A ≤ E.V₃ →
      E.L₁ ⊔ (T : Subgroup G) ≤ normalizer (A : Set G) → A = E.V₁ ∨ A = E.V₃)
    (hti : ∀ x ∈ E.M, V ⊓ V.map (MulAut.conj x).toMonoidHom = ⊥ ∨
      V.map (MulAut.conj x).toMonoidHom = V)
    (hgen : E.G₁ ≤ (E.K ⊔ E.Y) ⊔ E.M₁) (hVX : ⁅V,E.X⁆ = V)
    (hfour : ∀ P : Subgroup G, ⁅P,E.X⁆ = P → P ≤ (T : Subgroup G) →
      (frattini P).map P.subtype ≤ E.G₁.pCoreIn 2 → ⁅P,E.Y⁆ ≤ E.Y.pCoreIn 2)
    (hfive : ⁅(L ⊔ (T : Subgroup G)).pCoreIn 2,E.X⁆ ≤
      (E.K ⊔ (T : Subgroup G)).pCoreIn 2)

include hpoint hthree hX hcartan hn3 hirr hti hgen hVX hfour hfive in
/-- Closure abelianness from the distance-two replacement of its literal
MS-pair. Shortness is proved by the whole-core distance-two theorem; no
field-four or radical-saturation premise remains. The witness itself is
produced by qt-c132-nonbinary-distance-reduction, and its final application
remains with qt-d-1222-natural-closure-sp4. -/
theorem abelian_of_preceding_and_distance_two
    (p : Terminal.PointCoordinates E m)
    (σ : MulAut (Sp E.input.field.Carrier))
    (hlocal₁ : (E.L₁.subgroupOf L).map
      (σ.toMonoidHom.comp (Terminal.RadicalGeometry.componentQuotient m)) = pointLocal)
    (hlocal₂ : (E.L₂.subgroupOf L).map
      (σ.toMonoidHom.comp (Terminal.RadicalGeometry.componentQuotient m)) = planeLocal)
    (hunique : Source.UniqueNoncentralComponent (normalizer (E.V₂ : Set G)) E.V₂ E.L₂)
    (hmoved₁ : ⁅V,E.L₁⁆ = E.V₃) (hmoved₂ : ⁅V,E.L₂⁆ = V)
    (hcontrol : normalizer (E.V₃ : Set G) ⊓ normalizer (E.L₁ : Set G) ≤ E.M)
    (hout : ¬ centralizer (E.V₁ : Set G) ≤ E.M)
    (hdistance : LocalGeometry.Normalizers.PointBlocks.NonbinaryMSPair
      E.input.field L (E.G₁.pCoreIn 2) →
      ∃ d : CharacteristicReduction (L.subgroupOf (L ⊔ E.G₁.pCoreIn 2))
        ((E.G₁.pCoreIn 2).subgroupOf (L ⊔ E.G₁.pCoreIn 2)),
        ∃ graph : ChapterC.BinaryMS.MS93.Geometry d.radical,
          graph.b d.radical = 2) :
    IsMulCommutative E.W := by
  apply abelian_of_preceding_and_core_recognition E m g hpoint hthree hX hcartan
    hn3 hirr hti hgen hVX hfour hfive p σ hlocal₁ hlocal₂ hunique hmoved₁ hmoved₂
    hcontrol hout
  intro hms
  obtain ⟨d,graph,hb⟩ := hdistance hms
  exact CharacteristicBlock.msPair_core_eq_seed_of_distance_two E m hms d graph hb

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Symplectic
