module
public import CFSG.Quasithin.Chapter12.Section05.NaturalSource.Local.Normalizers.JankoLocalAlignment
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.SymmetricLinear.PointParabolic.MathieuOverlap.Placement

/-!
# Original max4 parabolics and max1 actors

The supplied point-component equivalence places the original parabolic in
native max4. Its point-stabilizer identification and the certified normal
elementary subgroup put that whole parabolic in a conjugate max1. If the
original actor lies in max1, the common original full Sylow aligns these
Mathieu locals. The existing original-Y-closure argument then controls the
same actor and yields G₃,G₆ ≤ N_G(L).

The component, quotient, actor, Y-image and Sylow remain the original ones.
The reverse pair of native rows and the other actor rows remain separate
source obligations. No full elementary-normalizer cover is assumed here.
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

/-- Native max4-to-max1 incidence, retaining the original parabolic, actor,
component equivalence and full Sylow. -/
theorem pointComponentParabolic_le_max1_of_janko_max4_actor
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) {K : Subgroup G}
    (hK : K ∈ Chapter1.cComponentsIn (s.marking.Gi 1))
    (hLK : s.marking.Li 1 ≤ K) (hN : (K.subgroupOf (s.marking.Gi 1)).Normal)
    (e : s.pointCoreImage K ≃* Janko4.Model)
    (hplace : (s.pointComponentParabolic K).map e.toMonoidHom ≤
      Janko4.LocalStructure.SymmetricLinear.max4Subgroup)
    (i : ℕ) (hi : i = 3 ∨ i = 6)
    (hactor : ((s.localPointProjection K i).subgroupOf (s.pointCoreImage K)).map
      e.toMonoidHom ≤
      Janko4.Cardinality.max1Subgroup Janko4.matrixA_mul_self Janko4.matrixB_pow_four) :
    (s.pointComponentParabolic K).map e.toMonoidHom ≤
      Janko4.Cardinality.max1Subgroup Janko4.matrixA_mul_self Janko4.matrixB_pow_four := by
  let C := s.pointCoreImage K
  let H := (s.pointComponentParabolic K).map e.toMonoidHom
  let M := Janko4.Cardinality.max1Subgroup Janko4.matrixA_mul_self Janko4.matrixB_pow_four
  obtain ⟨S, hS, hSA⟩ := s.point_projection_contains_original_sylow hN i hi
  have hSP : (S : Subgroup C) ≤ s.pointComponentParabolic K := by
    rw [hS]
    exact comap_mono (s.pointCoreImage_mono (le_inf le_sup_right s.sylow_le_G₁))
  let R := S.mapSurjective (f := e.toMonoidHom) e.surjective
  have hRH : (R : Subgroup Janko4.Model) ≤ H := map_mono hSP
  have hRM : (R : Subgroup Janko4.Model) ≤ M := (map_mono hSA).trans hactor
  obtain ⟨j, hj⟩ := s.pointComponentParabolic_janko_max4 h hK hLK hN e hplace
  have hRP : (R : Subgroup Janko4.Model) ≤
      Janko4.LocalStructure.SymmetricLinear.pointParabolic j := hRH.trans_eq hj
  obtain ⟨g, hg⟩ :=
    Janko4.LocalStructure.SymmetricLinear.pointParabolic_le_conjugate_mathieu j R hRP
  have hHM : H ≤ M.map (MulAut.conj g).toMonoidHom := by
    change (s.pointComponentParabolic K).map e.toMonoidHom ≤ _
    rw [hj]
    exact hg
  have he := R.conjugate_overgroup_eq M hRM
    (by rw [Janko4.sylow_normalizer_eq]; exact hRM) g (hRH.trans hHM)
  exact hHM.trans_eq he

/-- If the original parabolic is in max4 and the original actor is in max1,
the native incidence calculation gives the original ambient normalizer. -/
theorem local_normalizer_le_M_of_janko_max4_max1
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) {K : Subgroup G}
    (hK : K ∈ Chapter1.cComponentsIn (s.marking.Gi 1))
    (hLK : s.marking.Li 1 ≤ K) (hN : (K.subgroupOf (s.marking.Gi 1)).Normal)
    (e : s.pointCoreImage K ≃* Janko4.Model)
    (hplace : (s.pointComponentParabolic K).map e.toMonoidHom ≤
      Janko4.LocalStructure.SymmetricLinear.max4Subgroup)
    (i : ℕ) (hi : i = 3 ∨ i = 6)
    (hactor : ((s.localPointProjection K i).subgroupOf (s.pointCoreImage K)).map
      e.toMonoidHom ≤
      Janko4.Cardinality.max1Subgroup Janko4.matrixA_mul_self Janko4.matrixB_pow_four) :
    s.marking.Gi i ≤ s.marking.M := by
  have hmax1 := s.pointComponentParabolic_le_max1_of_janko_max4_actor
    h hK hLK hN e hplace i hi hactor
  exact s.local_normalizer_le_M_of_janko_same_max1 h hK hLK hN e hmax1 i hi hactor

end SylowExteriorMarking
end CFSG.Quasithin.Chapter12.Section05.NaturalSource
