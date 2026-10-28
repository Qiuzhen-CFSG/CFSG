module
public import CFSG.Quasithin.Chapter12.Section05.NaturalSource.Local.Normalizers.JankoActorSeed
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.ElementaryNormalizerCover.PureTwoA.EightSylow

/-!
# Excluding the native eight branch for the original Janko actor

The original G3 or G6 projection contains a full Sylow of the point
component. If it normalizes a subgroup whose whole centralizer fuses to the
native elementary group of order 256, the proved eight-normalizer placement
would put that Sylow in an F local, contradicting its two-part.

Apply this to the literal central omega of the original Y-closure supplied
by JankoActorSeed. Both the quotient image and the component equivalence
are unchanged. This excludes the exceptional centralizer branch without an
eight-placement premise. The other source branches and the uniform
four-local cover remain separate obligations.

Source: Aschbacher--Smith 12.5.4, printed p.819, and Kleidman--Wilson
(1988), Corollary 2.3.6, p.493.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section05.NaturalSource
open Section02
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {D : ChosenModule T L V}
namespace SylowExteriorMarking
variable (s : SylowExteriorMarking D)

/-- The original projected actor cannot normalize a subgroup in the fused
eight-centralizer branch. Its full Sylow comes from the original projection. -/
theorem point_projection_not_janko_fused_eight
    {K : Subgroup G} (hN : (K.subgroupOf (s.marking.Gi 1)).Normal)
    (e : s.pointCoreImage K ≃* Janko4.Model)
    (i : ℕ) (hi : i = 3 ∨ i = 6) (X : Subgroup Janko4.Model) (g : Janko4.Model)
    (hactor : ((s.localPointProjection K i).subgroupOf (s.pointCoreImage K)).map
      e.toMonoidHom ≤ normalizer (X : Set Janko4.Model)) :
    (centralizer (X : Set Janko4.Model)).map (MulAut.conj g).toMonoidHom ≠
      Janko4.LocalStructure.ElementaryEightGeometry.nativeEight 1 := by
  intro hC
  obtain ⟨S,_,hSA⟩ := s.point_projection_contains_original_sylow hN i hi
  exact Janko4.LocalStructure.ElementaryNormalizerCover.PureTwoA.not_sylow_le_fused_eight_normalizer
    (S.mapSurjective (f := e.toMonoidHom) e.surjective) X g hC
    ((map_mono hSA).trans hactor)

/-- Apply the eight-centralizer exclusion to the actual elementary seed of
the original Y-closure. No replacement seed or normalizing actor is assumed. -/
theorem point_projection_janko_seed_not_fused_eight
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) {K : Subgroup G}
    (hK : K ∈ Chapter1.cComponentsIn (s.marking.Gi 1))
    (hN : (K.subgroupOf (s.marking.Gi 1)).Normal)
    (e : s.pointCoreImage K ≃* Janko4.Model)
    (hplace : (s.pointComponentParabolic K).map e.toMonoidHom ≤
        Janko4.Cardinality.max1Subgroup Janko4.matrixA_mul_self Janko4.matrixB_pow_four ∨
      (s.pointComponentParabolic K).map e.toMonoidHom ≤
        Janko4.LocalStructure.SymmetricLinear.max4Subgroup)
    (i : ℕ) (hi : i = 3 ∨ i = 6) (g : Janko4.Model) :
    let C := s.pointCoreImage K
    let U := ((s.pointCoreImage s.Y).subgroupOf C).map e.toMonoidHom
    let A := ((s.localPointProjection K i).subgroupOf C).map e.toMonoidHom
    let E := omegaCenterIn ((conjugateSpanBy U A).pCoreIn 2)
    (centralizer (E : Set Janko4.Model)).map (MulAut.conj g).toMonoidHom ≠
      Janko4.LocalStructure.ElementaryEightGeometry.nativeEight 1 := by
  obtain ⟨_,_,_,_,_,hn⟩ := s.point_projection_janko_elementary_seed h hK hN e hplace i hi
  exact s.point_projection_not_janko_fused_eight hN e i hi _ g hn

end SylowExteriorMarking
end CFSG.Quasithin.Chapter12.Section05.NaturalSource
