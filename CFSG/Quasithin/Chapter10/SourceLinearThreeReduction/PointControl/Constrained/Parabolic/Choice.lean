module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Constrained.Parabolic.Structure
public import Theory.SpecificGroups.BinaryLinear.FiveFlagGeometry.RankOneGeneration

/-!
# Choosing the actual escaping rank-one parabolic

The original natural component L moves u. Since the plane centralizer is
maximal in I C_T(v), adjoining L generates that entire join. The plane
centralizer consequently cannot lie in M. The actual SL₅ quotient and its
two-group kernel then supply a cover of C_T(v) inside the plane centralizer
and outside M. Self-normalization of the prescribed Sylow proves relative
nonnormality, hence the genuine B.6.1 minimal-parabolic condition.

Every subgroup is transported through the literal point-join inclusion.
This is the choice of P in Aschbacher--Smith 10.2.9, printed p.753.
The exchange P^t = P and its two terminal contradictions are not asserted;
qt-d-10-nona5-point-constrained retains them and the construction of
LinearFiveData in final assembly.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher Representation
namespace CFSG.Quasithin.Chapter10.PointControl.Constrained
open Chapter3.Section02 ChapterB.InternalThompsonAction
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L} {t v : G} {I : Subgroup G}

/-- The original natural component moves the opposite involution. -/
theorem LinearFiveData.component_not_le_plane_centralizer {c : Context D t v I}
    (m : LinearFiveData c) : ¬ L ≤ planeCentralizer T t v I := by
  intro hL
  have hu : oppositePoint t v ∈ ⁅D.fullModule,L⁆ ⊓ centralizer (L : Set G) := by
    refine ⟨m.opposite_mem_moved,?_⟩
    intro l hl
    have hh := hL hl
    change l ∈ pointJoin T v I ⊓ centralizer (pointPlane t v : Set G) at hh
    rw [c.join_plane_centralizer] at hh
    exact mem_centralizer_singleton_iff.mp hh.2
  rw [m.moved_fixed_eq_bot] at hu
  exact c.escaping.v_ne ((MulAut.conj t).map_eq_one_iff.mp hu)

/-- The original component together with the plane parabolic generates the
whole point join, by maximality and its nontrivial action on u. -/
theorem LinearFiveData.component_sup_plane_centralizer {c : Context D t v I}
    (m : LinearFiveData c) : L ⊔ planeCentralizer T t v I = pointJoin T v I := by
  let H := pointJoin T v I
  let C := planeCentralizer T t v I
  have hLH : L ≤ H := c.escaping.strict.le.trans le_sup_left
  have hCH : C ≤ H := inf_le_left
  have hstrict : C.subgroupOf H < (L ⊔ C).subgroupOf H := by
    apply lt_iff_le_not_ge.mpr
    refine ⟨comap_mono le_sup_right,?_⟩
    intro h
    apply m.component_not_le_plane_centralizer
    intro x hx
    exact h (show (⟨x,hLH hx⟩ : H) ∈ (L ⊔ C).subgroupOf H from
      (le_sup_left : L ≤ L ⊔ C) hx)
  have ht : (L ⊔ C).subgroupOf H = ⊤ := m.plane_maximal.2 _ hstrict
  have hh := congrArg (Subgroup.map H.subtype) ht
  rw [map_subgroupOf_eq_of_le (sup_le hLH hCH),←MonoidHom.range_eq_map,range_subtype] at hh
  exact hh

/-- The plane parabolic itself escapes M. This supplies the source choice of
a rank-one parabolic over C_T(v) outside M. -/
theorem LinearFiveData.plane_centralizer_escapes {c : Context D t v I}
    (m : LinearFiveData c) : ¬ planeCentralizer T t v I ≤ D.maximalLocal := by
  intro hC
  have hLM : L ≤ D.maximalLocal :=
    (le_componentOrbit L T).trans (localOrbit T L).le_normalizer
  have hH : pointJoin T v I ≤ D.maximalLocal := by
    rw [←m.component_sup_plane_centralizer]
    exact sup_le hLM hC
  exact c.escaping.escapes ((le_sup_left : I ≤ pointJoin T v I).trans hH)

/-- A rank-one overgroup of the original point Sylow lies in the plane
centralizer and escapes M. All subgroups are embedded in the original G. -/
theorem LinearFiveData.exists_escaping_rankOne {c : Context D t v I}
    (m : LinearFiveData c) :
    ∃ P : Subgroup G, pointSylow T v ⋖ P ∧ P ≤ planeCentralizer T t v I ∧
      ¬ P ≤ D.maximalLocal ∧ Chapter1.IsSylowIn 2 (pointSylow T v) P := by
  let H := pointJoin T v I
  let C := planeCentralizer T t v I
  obtain ⟨S,hS⟩ := c.join_sylow
  have hSC : (S : Subgroup H) ≤ C.subgroupOf H := by
    intro s hs
    exact ⟨s.property,m.pointSylow_centralizes_plane (hS ▸ mem_map_of_mem H.subtype hs)⟩
  have hSM : (S : Subgroup H) ≤ D.maximalLocal.subgroupOf H := by
    intro s hs
    exact le_normalizer_componentOrbit L T
      ((hS ▸ mem_map_of_mem H.subtype hs).1)
  have hCM : ¬ C.subgroupOf H ≤ D.maximalLocal.subgroupOf H := by
    intro h
    apply m.plane_centralizer_escapes
    intro x hx
    exact h (show (⟨x,hx.1⟩ : H) ∈ C.subgroupOf H from hx)
  obtain ⟨P,hcov,hPC,hPM⟩ := BinaryLinear.FiveFlagGeometry.exists_rankOne_escaping_of_two_kernel
    m.joinAction m.joinAction_surjective m.joinAction_kernel_two S
      (C.subgroupOf H) (D.maximalLocal.subgroupOf H) hSC hSM hCM
  have hP : P.map H.subtype ≤ C := by
    rintro _ ⟨x,hx,rfl⟩
    exact hPC hx
  have hSP : pointSylow T v ≤ P.map H.subtype := by
    rw [←hS]
    exact map_mono hcov.le
  refine ⟨P.map H.subtype,?_,hP,?_,c.join_sylow.restrict hSP
    (hP.trans inf_le_left)⟩
  · apply covBy_iff_lt_and_eq_or_eq.mpr
    constructor
    · refine lt_of_le_of_ne hSP ?_
      intro he
      apply hcov.ne
      apply map_injective H.subtype_injective
      exact hS.trans he
    · intro X hSX hXP
      have hXH : X ≤ H := hXP.trans (map_subtype_le P)
      have hSX' : (S : Subgroup H) ≤ X.subgroupOf H := by
        intro x hx
        exact hSX (hS ▸ mem_map_of_mem H.subtype hx)
      have hXP' : X.subgroupOf H ≤ P := by
        have hh := comap_mono (f := H.subtype) hXP
        rwa [comap_map_eq,(MonoidHom.ker_eq_bot_iff H.subtype).mpr H.subtype_injective,sup_bot_eq] at hh
      rcases (covBy_iff_lt_and_eq_or_eq.mp hcov).2 (X.subgroupOf H) hSX' hXP' with h | h
      · apply Or.inl
        have hh := congrArg (Subgroup.map H.subtype) h
        rwa [map_subgroupOf_eq_of_le hXH,hS] at hh
      · apply Or.inr
        have hh := congrArg (Subgroup.map H.subtype) h
        rwa [map_subgroupOf_eq_of_le hXH] at hh
  · intro h
    apply hPM
    intro x hx
    exact h (mem_map_of_mem H.subtype hx)

/-- This source rank-one subgroup satisfies the genuine minimal-parabolic
condition, including nonnormality of its prescribed Sylow subgroup. -/
theorem LinearFiveData.exists_escaping_minimalParabolic {c : Context D t v I}
    (m : LinearFiveData c) :
    ∃ (S : Sylow 2 (pointJoin T v I)) (P : Subgroup (pointJoin T v I)),
      (S : Subgroup _).map (pointJoin T v I).subtype = pointSylow T v ∧
      ChapterB.IsMinimalParabolicOver S P ∧
      P.map (pointJoin T v I).subtype ≤ planeCentralizer T t v I ∧
      ¬ P.map (pointJoin T v I).subtype ≤ D.maximalLocal := by
  let H := pointJoin T v I
  obtain ⟨S,hS⟩ := c.join_sylow
  obtain ⟨P,hcov,hPC,hPM,_⟩ := m.exists_escaping_rankOne
  have hPH : P ≤ H := hPC.trans inf_le_left
  have hS' : (S : Subgroup H) = (pointSylow T v).subgroupOf H := by
    apply map_injective H.subtype_injective
    rw [hS,map_subgroupOf_eq_of_le le_sup_right]
  have hSP : (S : Subgroup H) ≤ P.subgroupOf H := by
    rw [hS']
    exact comap_mono hcov.le
  have hcov' : (S : Subgroup H) ⋖ P.subgroupOf H := by
    apply covBy_iff_lt_and_eq_or_eq.mpr
    constructor
    · refine lt_of_le_of_ne hSP ?_
      intro he
      have hh := congrArg (Subgroup.map H.subtype) he
      rw [hS,map_subgroupOf_eq_of_le hPH] at hh
      exact hcov.ne hh
    · intro X hSX hXP
      have hSm : pointSylow T v ≤ X.map H.subtype := by rw [←hS]; exact map_mono hSX
      have hPm : X.map H.subtype ≤ P := by
        have hh := map_mono (f := H.subtype) hXP
        rwa [map_subgroupOf_eq_of_le hPH] at hh
      rcases (covBy_iff_lt_and_eq_or_eq.mp hcov).2 (X.map H.subtype) hSm hPm with h | h
      · exact Or.inl (map_injective H.subtype_injective (h.trans hS.symm))
      · apply Or.inr
        apply map_injective H.subtype_injective
        rwa [map_subgroupOf_eq_of_le hPH]
  refine ⟨S,P.subgroupOf H,hS,?_,?_,?_⟩
  · apply (ChapterB.isMinimalParabolicOver_iff S _).mpr
    constructor
    · refine ⟨hcov'.lt,⟨(S : Subgroup H),⟨le_rfl,hcov'⟩,?_⟩⟩
      intro X hX
      exact ((covBy_iff_lt_and_eq_or_eq.mp hcov').2 X hX.1 hX.2.le).resolve_right hX.2.ne
    · intro hn
      have hnorm := (normal_subgroupOf_iff_le_normalizer hSP).mp hn
      rw [BinaryLinear.FiveFlagGeometry.normalizer_sylow_eq_of_two_kernel
        m.joinAction m.joinAction_surjective m.joinAction_kernel_two S] at hnorm
      exact hcov'.lt.not_ge hnorm
  · rwa [map_subgroupOf_eq_of_le hPH]
  · rwa [map_subgroupOf_eq_of_le hPH]

end CFSG.Quasithin.Chapter10.PointControl.Constrained
