module
public import CFSG.Quasithin.Chapter12.Section05.NaturalSource.Local.Normalizers.JankoCrossLocal
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.SymmetricLinear.PointParabolic.MathieuOverlap.Reverse

/-!
# Both original J₄ cross-local actor branches

The reverse native incidence places the original full Mathieu trio preimage
in the same conjugate max4 as the original projected actor. The max4 residual
normalizer theorem then gives G₃,G₆ ≤ N_G(L). In the other direction, the
conjugate point-parabolic incidence aligns max4 with an independently
conjugated max1 actor, and the original Y-closure theorem gives the same
ambient containment.

Every subgroup is the original source subgroup. When the given native local
is conjugated, the supplied component equivalence, parabolic and actor are
transported together; no new Sylow or actor is substituted. These results
close both max1/max4 cross pairs, including independent actor conjugators.
The max2 actor, native cover/max3 inputs and full LocalComponents assembly
remain with their existing owners; this is not an unconditional 12.5.4 claim.
Source: Aschbacher–Smith 12.5.3–4, printed pp.818–819/PDF pp.835–836.
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

private theorem map_le_conjugate_pull {C : Type*} [Group C]
    (e : C ≃* Janko4.Model) (H : Subgroup C) (N : Subgroup Janko4.Model) (a : Janko4.Model)
    (h : H.map e.toMonoidHom ≤ N.map (MulAut.conj a).toMonoidHom) :
    H.map (e.trans (MulAut.conj a).symm).toMonoidHom ≤ N := by
  let c := MulAut.conj a
  have hc : c.symm.toMonoidHom.comp c.toMonoidHom = MonoidHom.id Janko4.Model := by
    ext x
    exact c.symm_apply_apply x
  have hh := map_mono (f := c.symm.toMonoidHom) h
  change (H.map e.toMonoidHom).map c.symm.toMonoidHom ≤
    (N.map c.toMonoidHom).map c.symm.toMonoidHom at hh
  change H.map (c.symm.toMonoidHom.comp e.toMonoidHom) ≤ N
  simpa only [map_map, hc, map_id] using hh

/-- The full original parabolic follows a max4 placement of the original
actor, even when its own cover placement is the Mathieu row. -/
theorem pointComponentParabolic_le_conjugate_max4_of_janko_max1_actor
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) {K : Subgroup G}
    (hK : K ∈ Chapter1.cComponentsIn (s.marking.Gi 1))
    (hLK : s.marking.Li 1 ≤ K) (hN : (K.subgroupOf (s.marking.Gi 1)).Normal)
    (e : s.pointCoreImage K ≃* Janko4.Model)
    (hplace : (s.pointComponentParabolic K).map e.toMonoidHom ≤
      Janko4.Cardinality.max1Subgroup Janko4.matrixA_mul_self Janko4.matrixB_pow_four)
    (i : ℕ) (hi : i = 3 ∨ i = 6) (a : Janko4.Model)
    (hactor : ((s.localPointProjection K i).subgroupOf (s.pointCoreImage K)).map
      e.toMonoidHom ≤ Janko4.LocalStructure.SymmetricLinear.max4Subgroup.map
        (MulAut.conj a).toMonoidHom) :
    (s.pointComponentParabolic K).map e.toMonoidHom ≤
      Janko4.LocalStructure.SymmetricLinear.max4Subgroup.map (MulAut.conj a).toMonoidHom := by
  let C := s.pointCoreImage K
  obtain ⟨S, hS, hSA⟩ := s.point_projection_contains_original_sylow hN i hi
  have hSP : (S : Subgroup C) ≤ s.pointComponentParabolic K := by
    rw [hS]
    exact comap_mono (s.pointCoreImage_mono (le_inf le_sup_right s.sylow_le_G₁))
  let R := S.mapSurjective (f := e.toMonoidHom) e.surjective
  obtain ⟨g, hg⟩ := s.pointComponentParabolic_janko_max1 h hK hLK hN e hplace
  exact Janko4.LocalStructure.SymmetricLinear.trio_preimage_le_conjugate_max4 R
    ((s.pointComponentParabolic K).map e.toMonoidHom) (map_mono hSP) hplace a
    ((map_mono hSA).trans hactor) g hg

/-- Reverse cross-local actor control, with the original parabolic, actor
and full point-core quotient transported together through the given conjugator. -/
theorem local_normalizer_le_M_of_janko_max1_conjugate_max4
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) {K : Subgroup G}
    (hK : K ∈ Chapter1.cComponentsIn (s.marking.Gi 1))
    (hLK : s.marking.Li 1 ≤ K) (hN : (K.subgroupOf (s.marking.Gi 1)).Normal)
    (e : s.pointCoreImage K ≃* Janko4.Model)
    (hplace : (s.pointComponentParabolic K).map e.toMonoidHom ≤
      Janko4.Cardinality.max1Subgroup Janko4.matrixA_mul_self Janko4.matrixB_pow_four)
    (i : ℕ) (hi : i = 3 ∨ i = 6) (a : Janko4.Model)
    (hactor : ((s.localPointProjection K i).subgroupOf (s.pointCoreImage K)).map
      e.toMonoidHom ≤ Janko4.LocalStructure.SymmetricLinear.max4Subgroup.map
        (MulAut.conj a).toMonoidHom) :
    s.marking.Gi i ≤ s.marking.M := by
  have hP := s.pointComponentParabolic_le_conjugate_max4_of_janko_max1_actor
    h hK hLK hN e hplace i hi a hactor
  exact s.local_normalizer_le_M_of_janko_same_max4 h hK hLK hN
    (e.trans (MulAut.conj a).symm) (map_le_conjugate_pull e _ _ a hP) i hi
    (map_le_conjugate_pull e _ _ a hactor)

/-- The other cross-local comparison also accepts an independent cover
conjugator for the original actor. -/
theorem local_normalizer_le_M_of_janko_max4_conjugate_max1
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) {K : Subgroup G}
    (hK : K ∈ Chapter1.cComponentsIn (s.marking.Gi 1))
    (hLK : s.marking.Li 1 ≤ K) (hN : (K.subgroupOf (s.marking.Gi 1)).Normal)
    (e : s.pointCoreImage K ≃* Janko4.Model)
    (hplace : (s.pointComponentParabolic K).map e.toMonoidHom ≤
      Janko4.LocalStructure.SymmetricLinear.max4Subgroup)
    (i : ℕ) (hi : i = 3 ∨ i = 6) (a : Janko4.Model)
    (hactor : ((s.localPointProjection K i).subgroupOf (s.pointCoreImage K)).map
      e.toMonoidHom ≤
      (Janko4.Cardinality.max1Subgroup Janko4.matrixA_mul_self Janko4.matrixB_pow_four).map
        (MulAut.conj a).toMonoidHom) :
    s.marking.Gi i ≤ s.marking.M := by
  let C := s.pointCoreImage K
  let e' := e.trans (MulAut.conj a).symm
  let M := Janko4.Cardinality.max1Subgroup Janko4.matrixA_mul_self Janko4.matrixB_pow_four
  have hA : ((s.localPointProjection K i).subgroupOf C).map e'.toMonoidHom ≤ M :=
    map_le_conjugate_pull e _ _ a hactor
  obtain ⟨S, hS, hSA⟩ := s.point_projection_contains_original_sylow hN i hi
  have hSP : (S : Subgroup C) ≤ s.pointComponentParabolic K := by
    rw [hS]
    exact comap_mono (s.pointCoreImage_mono (le_inf le_sup_right s.sylow_le_G₁))
  let R := S.mapSurjective (f := e'.toMonoidHom) e'.surjective
  obtain ⟨j, hj⟩ := s.pointComponentParabolic_janko_max4 h hK hLK hN e hplace
  have heq : (s.pointComponentParabolic K).map e'.toMonoidHom =
      (Janko4.LocalStructure.SymmetricLinear.pointParabolic j).map
        (MulAut.conj a⁻¹).toMonoidHom := by
    change (s.pointComponentParabolic K).map
      ((MulAut.conj a⁻¹).toMonoidHom.comp e.toMonoidHom) = _
    rw [← map_map, hj]
  have hRM : (R : Subgroup Janko4.Model) ≤ M := (map_mono hSA).trans hA
  have hRP : (R : Subgroup Janko4.Model) ≤
      (Janko4.LocalStructure.SymmetricLinear.pointParabolic j).map
        (MulAut.conj a⁻¹).toMonoidHom := (map_mono hSP).trans_eq heq
  have hPM := Janko4.LocalStructure.SymmetricLinear.conjugate_pointParabolic_le_mathieu j a⁻¹ R hRP hRM
  exact s.local_normalizer_le_M_of_janko_same_max1 h hK hLK hN e'
    (heq.trans_le hPM) i hi hA

end SylowExteriorMarking
end CFSG.Quasithin.Chapter12.Section05.NaturalSource
