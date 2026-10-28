module
public import CFSG.Quasithin.Chapter12.Section05.NaturalSource.Local.Normalizers.JankoMax4
public import Theory.SpecificGroups.Janko4.Model.InvolutionCentralizers.First.ParabolicExclusion
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.Mathieu.PointParabolic

/-!
# Original exterior parabolics in the native Janko locals

Keep the supplied map from the original point component. In the native
first-centralizer branch, its full Sylow and seven divisor survive the
literal M22 projection, contradicting the native two-local seven bound.
In the native max1 branch, the elementary kernel lies in the original
full Sylow. The quotient is therefore a Mathieu trio stabilizer and the
original parabolic is its full inverse image.

Both arguments use the embedding into the original M1 image, whose
intrinsic two-core quotient has order 1008. Thus the native quotient
images cannot be core-free. The max1-to-max4 incidence comparison and the
same original actor's normalizer exclusion remain with qt-d-1251-local;
this module does not assume a cover row has been selected. Final exterior
assembly remains with qt-d-1251-source.
Source: Aschbacher–Smith 12.5.3--4, printed pp.818--819/PDF pp.835--836.
-/

public noncomputable section
attribute [local irreducible] Janko4.modelGroup Janko4.matrixA Janko4.matrixB
  Janko4.Cardinality.max1Subgroup
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section05.NaturalSource
open Section02
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {D : ChosenModule T L V}
namespace SylowExteriorMarking
variable (s : SylowExteriorMarking D)

private def parabolicEmbedding (K : Subgroup G) :
    s.pointComponentParabolic K →* s.pointCoreImage (s.marking.Mi 1) where
  toFun x := ⟨x.val.val, x.property⟩
  map_one' := rfl
  map_mul' _ _ := rfl

omit [Finite G] in
private theorem parabolicEmbedding_injective (K : Subgroup G) :
    Function.Injective (s.parabolicEmbedding K) := by
  intro x y he
  apply Subtype.ext
  apply Subtype.ext
  exact congrArg (fun z : s.pointCoreImage (s.marking.Mi 1) =>
    (z : s.marking.Gi 1 ⧸ pCore 2 (s.marking.Gi 1))) he

/-- The original point parabolic cannot lie in the native first involution centralizer. -/
theorem pointComponentParabolic_not_janko_firstCentralizer
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) {K : Subgroup G}
    (hK : K ∈ Chapter1.cComponentsIn (s.marking.Gi 1))
    (hLK : s.marking.Li 1 ≤ K) (hN : (K.subgroupOf (s.marking.Gi 1)).Normal)
    (e : s.pointCoreImage K ≃* Janko4.Model) :
    ¬ (s.pointComponentParabolic K).map e.toMonoidHom ≤
      Janko4.InvolutionCentralizers.First.centralizer := by
  intro hplace
  have hY := s.Y_le_point_component_of_large_model h hK hN
    (.inr (.inr ⟨(s.pointComponentCoreEquivImage hK.1 hN).trans e⟩))
  obtain ⟨S, hS, hi⟩ := s.pointComponentParabolic_sylow_index hK.1 hN hLK hY
  let H := (s.pointComponentParabolic K).map e.toMonoidHom
  let M := Janko4.InvolutionCentralizers.First.centralizer
  let R := S.mapSurjective (f := e.toMonoidHom) e.surjective
  have hRH : (R : Subgroup Janko4.Model) ≤ H := map_mono hS
  let J := H.subgroupOf M
  let d : J ≃* s.pointComponentParabolic K :=
    (subgroupOfEquivOfLe hplace).trans (e.subgroupMap (s.pointComponentParabolic K)).symm
  have h7 : 7 ∣ Nat.card J := by
    rw [Nat.card_congr d.toEquiv]
    have h63 : 63 ∣ Nat.card (s.pointComponentParabolic K) := by
      rw [← hi]
      exact (S : Subgroup (s.pointCoreImage K)).relIndex_dvd_card
        (s.pointComponentParabolic K)
    exact (by decide : 7 ∣ 63).trans h63
  exact Janko4.InvolutionCentralizers.First.ParabolicExclusion.not_small_core_quotient_embedding
    (R.subtype (hRH.trans hplace)) J (comap_mono hRH) h7
    ((s.parabolicEmbedding K).comp d.toMonoidHom)
    ((s.parabolicEmbedding_injective K).comp d.injective) s.pointCoreImage_M₁_core_card

/-- The same original parabolic is a full native Mathieu trio preimage in the max1 branch. -/
theorem pointComponentParabolic_janko_max1
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) {K : Subgroup G}
    (hK : K ∈ Chapter1.cComponentsIn (s.marking.Gi 1))
    (hLK : s.marking.Li 1 ≤ K) (hN : (K.subgroupOf (s.marking.Gi 1)).Normal)
    (e : s.pointCoreImage K ≃* Janko4.Model)
    (hplace : (s.pointComponentParabolic K).map e.toMonoidHom ≤
      Janko4.Cardinality.max1Subgroup Janko4.matrixA_mul_self Janko4.matrixB_pow_four) :
    ∃ g : Sporadic.Mathieu.M24,
      (s.pointComponentParabolic K).map e.toMonoidHom =
        ((Sporadic.Mathieu.M24LocalGeometry.PairOvergroups.trioStabilizer
          Sporadic.Mathieu.M24LocalGeometry.PairOvergroups.standardTrio).comap
          ((MulAut.conj g).toMonoidHom.comp Janko4.LocalStructure.MathieuHallActors.projection)).map
          (Janko4.Cardinality.max1Subgroup Janko4.matrixA_mul_self Janko4.matrixB_pow_four).subtype := by
  have hY := s.Y_le_point_component_of_large_model h hK hN
    (.inr (.inr ⟨(s.pointComponentCoreEquivImage hK.1 hN).trans e⟩))
  obtain ⟨S, hS, hi⟩ := s.pointComponentParabolic_sylow_index hK.1 hN hLK hY
  let H := (s.pointComponentParabolic K).map e.toMonoidHom
  let M := Janko4.Cardinality.max1Subgroup Janko4.matrixA_mul_self Janko4.matrixB_pow_four
  let R := S.mapSurjective (f := e.toMonoidHom) e.surjective
  have hRH : (R : Subgroup Janko4.Model) ≤ H := map_mono hS
  let J := H.subgroupOf M
  let d : J ≃* s.pointComponentParabolic K :=
    (subgroupOfEquivOfLe hplace).trans (e.subgroupMap (s.pointComponentParabolic K)).symm
  have hrel : ((R.subtype (hRH.trans hplace)) : Subgroup M).relIndex J = 63 := by
    change ((R : Subgroup Janko4.Model).subgroupOf M).relIndex (H.subgroupOf M) = 63
    rw [relIndex_subgroupOf hplace]
    exact (relIndex_map_map_of_injective _ _ e.injective).trans hi
  obtain ⟨g, hg⟩ := Janko4.LocalStructure.MathieuParabolic.eq_trio_preimage
    (R.subtype (hRH.trans hplace)) J (comap_mono hRH) hrel
    ((s.parabolicEmbedding K).comp d.toMonoidHom)
    ((s.parabolicEmbedding_injective K).comp d.injective) s.pointCoreImage_M₁_core_card
  refine ⟨g, ?_⟩
  exact (map_subgroupOf_eq_of_le hplace).symm.trans (congrArg (map M.subtype) hg)

end SylowExteriorMarking
end CFSG.Quasithin.Chapter12.Section05.NaturalSource
