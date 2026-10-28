module
public import CFSG.Quasithin.Chapter12.Section05.NaturalSource.Local.Normalizers.JankoMax4
public import Theory.GroupTheory.PerfectSolvableSectionLift

/-!
# The original point residual in the native max4 normalizer

The original parabolic is the full preimage of a point S4 times SL3(2),
and its original perfect residual maps onto the linear factor. The whole
native projection kernel is therefore inside the parabolic and normalizes
that same residual. The kernel is solvable, so the residual is recovered
as the perfect residual of its full preimage. Consequently all of max4
normalizes the original residual, not merely its image in the quotient.

The original projected actor, when it lies in that same max4, thus gives
G_i <= N_G(L) for i = 3,6 through the full point-core quotient. The supplied
component equivalence and every original subgroup are retained. Comparing
different native local rows remains with qt-d-1251-local; final exterior
assembly remains with qt-d-1251-source.
Source: Aschbacher--Smith, 12.5.3--4, printed pp.818--819/PDF pp.835--836.
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

/-- The whole specified max4 normalizes the original perfect point residual.
The actual projection kernel lies in the original parabolic. -/
theorem point_residual_janko_max4_normalizer
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) {K : Subgroup G}
    (hK : K ∈ Chapter1.cComponentsIn (s.marking.Gi 1))
    (hLK : s.marking.Li 1 ≤ K) (hN : (K.subgroupOf (s.marking.Gi 1)).Normal)
    (e : s.pointCoreImage K ≃* Janko4.Model)
    (hplace : (s.pointComponentParabolic K).map e.toMonoidHom ≤
      Janko4.LocalStructure.SymmetricLinear.max4Subgroup) :
    Janko4.LocalStructure.SymmetricLinear.max4Subgroup ≤
      normalizer ((((s.pointCoreImage (s.marking.Li 1)).subgroupOf
        (s.pointCoreImage K)).map e.toMonoidHom) : Set Janko4.Model) := by
  let C := s.pointCoreImage K
  let B0 := s.pointCoreImage (s.marking.Li 1)
  let B1 := B0.subgroupOf C
  let B := B1.map e.toMonoidHom
  let H := (s.pointComponentParabolic K).map e.toMonoidHom
  let M := Janko4.LocalStructure.SymmetricLinear.max4Subgroup
  let f := Janko4.LocalStructure.SymmetricLinear.max4Projection
  have hBC : B0 ≤ C := s.pointCoreImage_mono hLK
  have hBP : B1 ≤ s.pointComponentParabolic K :=
    comap_mono (s.pointCoreImage_mono (s.Li_le_Mi 1))
  have hBM : B ≤ M := (map_mono hBP).trans hplace
  let q := s.pointCoreImageHom (s.marking.Li 1) (s.marking.Li_le_Gi 1)
  let : Group.IsPerfect (s.marking.Li 1) := s.marking.Li_perfect 1
  let : Group.IsPerfect B0 := Group.IsPerfect.ofSurjective
    (f := q) (s.pointCoreImageHom_surjective _ _)
  let : Group.IsPerfect B1 := Group.IsPerfect.ofSurjective
    (f := (subgroupOfEquivOfLe hBC).symm.toMonoidHom)
    (subgroupOfEquivOfLe hBC).symm.surjective
  let : Group.IsPerfect B := Group.IsPerfect.map _
  let : Group.IsPerfect (B.subgroupOf M) := Group.IsPerfect.ofSurjective
    (f := (subgroupOfEquivOfLe hBM).symm.toMonoidHom)
    (subgroupOfEquivOfLe hBM).symm.surjective
  have hPN : s.pointComponentParabolic K ≤ normalizer (B1 : Set C) := by
    have hn := (s.pointCoreImage_normalizes_point_iff (s.marking.Mi 1) inf_le_right).mpr
      (s.Mi_normalizes_Li 1)
    intro p hp b
    exact hn hp (b : s.marking.Gi 1 ⧸ pCore 2 (s.marking.Gi 1))
  have hHN : H ≤ normalizer (B : Set Janko4.Model) :=
    (map_mono hPN).trans (B1.le_normalizer_map e.toMonoidHom)
  obtain ⟨j, hj, himage⟩ := s.point_residual_janko_max4_marking h hK hLK hN e hplace
  have hkerH : f.ker ≤ H.subgroupOf M := by
    intro x hx
    change (x : Janko4.Model) ∈ (s.pointComponentParabolic K).map e.toMonoidHom
    rw [hj]
    apply mem_map_of_mem M.subtype
    change f x ∈ (MulAction.stabilizer (Equiv.Perm (Fin 5)) j).prod ⊤
    rw [show f x = 1 from hx]
    exact one_mem _
  have hkerN : f.ker ≤ normalizer (B.subgroupOf M : Set M) := by
    intro x hx b
    exact hHN (hkerH hx) (b : Janko4.Model)
  let : Group.IsNilpotent f.ker :=
    Janko4.LocalStructure.SymmetricLinear.max4Projection_kernel_isTwoGroup.isNilpotent
  have hfull := normalizer_comap_map_le_of_solvable_kernel f (B.subgroupOf M) hkerN
  rw [himage] at hfull
  let : ((⊥ : Subgroup (Equiv.Perm (Fin 5))).prod
      (⊤ : Subgroup (Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)))).Normal := inferInstance
  rw [normalizer_eq_top, comap_top] at hfull
  exact (normal_subgroupOf_iff_le_normalizer hBM).mp
    (normalizer_eq_top_iff.mp (top_unique hfull))

/-- A projected actor in the same native max4 gives the original ambient
normalizer containment, with its full point-core kernel retained. -/
theorem local_normalizer_le_M_of_janko_same_max4
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) {K : Subgroup G}
    (hK : K ∈ Chapter1.cComponentsIn (s.marking.Gi 1))
    (hLK : s.marking.Li 1 ≤ K) (hN : (K.subgroupOf (s.marking.Gi 1)).Normal)
    (e : s.pointCoreImage K ≃* Janko4.Model)
    (hplace : (s.pointComponentParabolic K).map e.toMonoidHom ≤
      Janko4.LocalStructure.SymmetricLinear.max4Subgroup)
    (i : ℕ) (hi : i = 3 ∨ i = 6)
    (hactor : ((s.localPointProjection K i).subgroupOf (s.pointCoreImage K)).map
      e.toMonoidHom ≤ Janko4.LocalStructure.SymmetricLinear.max4Subgroup) :
    s.marking.Gi i ≤ s.marking.M := by
  apply (s.local_normalizer_iff_large_point_projection h hK hLK hN
    (.inr (.inr ⟨(s.pointComponentCoreEquivImage hK.1 hN).trans e⟩)) i hi).mpr
  let C := s.pointCoreImage K
  let B := s.pointCoreImage (s.marking.Li 1)
  have hBC : B ≤ C := s.pointCoreImage_mono hLK
  have hh := hactor.trans (s.point_residual_janko_max4_normalizer h hK hLK hN e hplace)
  rw [← map_equiv_normalizer_eq] at hh
  have hA : (s.localPointProjection K i).subgroupOf C ≤
      normalizer (B.subgroupOf C : Set C) := by
    intro a ha
    obtain ⟨x, hx, he⟩ := hh (mem_map_of_mem e.toMonoidHom ha)
    exact e.injective he ▸ hx
  have hm := map_mono (f := C.subtype) hA
  rw [map_subgroupOf_eq_of_le (show s.localPointProjection K i ≤ C from inf_le_left)] at hm
  have hn := (B.subgroupOf C).le_normalizer_map C.subtype
  rw [map_subgroupOf_eq_of_le hBC] at hn
  exact hm.trans hn

end SylowExteriorMarking
end CFSG.Quasithin.Chapter12.Section05.NaturalSource
