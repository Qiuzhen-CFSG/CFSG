module
public import CFSG.Quasithin.Chapter12.Section05.NaturalSource.Local.Normalizers.JankoMax1Actor
public import CFSG.Quasithin.Chapter12.Section05.NaturalSource.Local.Normalizers.JankoMax4Actor
public import Theory.GroupTheory.SylowConjugateOvergroup
public import Theory.SpecificGroups.Janko4.Model.SylowNormalizer

/-!
# Aligning native locals through the original full Sylow

The original parabolic and projected actor both contain the image of the
same original Sylow intersection in the point component. Every Sylow
two-subgroup of the native J4 model is self-normalizing. Sylow conjugacy
inside a local therefore makes any two conjugate locals containing this
same Sylow equal. Thus independent cover conjugators in one native row
do not require an additional simultaneous-placement assumption.

The max1 and max4 applications retain the original component map, actor,
point residual and whole quotient kernel, and give G_i <= N_G(L), i=3,6.
This aligns conjugates of one row; the max1/trio-to-max4 incidence and
actors in other rows still require proof. Native cover, intrinsic symmetry
and native max3 retain their existing producers; no cover is asserted here.
The remaining local assembly belongs to qt-d-1251-local and the final
exterior assembly to qt-d-1251-source.
Source: Aschbacher--Smith 12.5.3--4, printed pp.818--819/PDF pp.835--836.
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

/-- Independent conjugates of a native local align through the same original
full Sylow; the actor itself and the component map are unchanged. -/
theorem point_projection_le_native_of_conjugate {K : Subgroup G}
    (hN : (K.subgroupOf (s.marking.Gi 1)).Normal)
    (e : s.pointCoreImage K ≃* Janko4.Model)
    (M : Subgroup Janko4.Model)
    (hplace : (s.pointComponentParabolic K).map e.toMonoidHom ≤ M)
    (i : ℕ) (hi : i = 3 ∨ i = 6) (g : Janko4.Model)
    (hactor : ((s.localPointProjection K i).subgroupOf (s.pointCoreImage K)).map
      e.toMonoidHom ≤ M.map (MulAut.conj g).toMonoidHom) :
    ((s.localPointProjection K i).subgroupOf (s.pointCoreImage K)).map
      e.toMonoidHom ≤ M := by
  let C := s.pointCoreImage K
  obtain ⟨S, hS, hSA⟩ := s.point_projection_contains_original_sylow hN i hi
  have hSP : (S : Subgroup C) ≤ s.pointComponentParabolic K := by
    rw [hS]
    exact comap_mono (s.pointCoreImage_mono (le_inf le_sup_right s.sylow_le_G₁))
  let R := S.mapSurjective (f := e.toMonoidHom) e.surjective
  have hRM : (R : Subgroup Janko4.Model) ≤ M := (map_mono hSP).trans hplace
  have hconj := R.conjugate_overgroup_eq M hRM
    (by rw [Janko4.sylow_normalizer_eq]; exact hRM) g
    ((map_mono hSA).trans hactor)
  exact hactor.trans_eq hconj

/-- The original ambient normalizer containment when the two native cover
placements are independently conjugate max1 rows. -/
theorem local_normalizer_le_M_of_janko_conjugate_max1
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) {K : Subgroup G}
    (hK : K ∈ Chapter1.cComponentsIn (s.marking.Gi 1))
    (hLK : s.marking.Li 1 ≤ K) (hN : (K.subgroupOf (s.marking.Gi 1)).Normal)
    (e : s.pointCoreImage K ≃* Janko4.Model)
    (hplace : (s.pointComponentParabolic K).map e.toMonoidHom ≤
      Janko4.Cardinality.max1Subgroup Janko4.matrixA_mul_self Janko4.matrixB_pow_four)
    (i : ℕ) (hi : i = 3 ∨ i = 6) (g : Janko4.Model)
    (hactor : ((s.localPointProjection K i).subgroupOf (s.pointCoreImage K)).map
      e.toMonoidHom ≤
      (Janko4.Cardinality.max1Subgroup Janko4.matrixA_mul_self Janko4.matrixB_pow_four).map
        (MulAut.conj g).toMonoidHom) :
    s.marking.Gi i ≤ s.marking.M := by
  exact s.local_normalizer_le_M_of_janko_same_max1 h hK hLK hN e hplace i hi
    (s.point_projection_le_native_of_conjugate hN e _ hplace i hi g hactor)

/-- The original ambient normalizer containment when the two native cover
placements are independently conjugate max4 rows. -/
theorem local_normalizer_le_M_of_janko_conjugate_max4
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) {K : Subgroup G}
    (hK : K ∈ Chapter1.cComponentsIn (s.marking.Gi 1))
    (hLK : s.marking.Li 1 ≤ K) (hN : (K.subgroupOf (s.marking.Gi 1)).Normal)
    (e : s.pointCoreImage K ≃* Janko4.Model)
    (hplace : (s.pointComponentParabolic K).map e.toMonoidHom ≤
      Janko4.LocalStructure.SymmetricLinear.max4Subgroup)
    (i : ℕ) (hi : i = 3 ∨ i = 6) (g : Janko4.Model)
    (hactor : ((s.localPointProjection K i).subgroupOf (s.pointCoreImage K)).map
      e.toMonoidHom ≤ Janko4.LocalStructure.SymmetricLinear.max4Subgroup.map
        (MulAut.conj g).toMonoidHom) :
    s.marking.Gi i ≤ s.marking.M := by
  exact s.local_normalizer_le_M_of_janko_same_max4 h hK hLK hN e hplace i hi
    (s.point_projection_le_native_of_conjugate hN e _ hplace i hi g hactor)

end SylowExteriorMarking
end CFSG.Quasithin.Chapter12.Section05.NaturalSource
