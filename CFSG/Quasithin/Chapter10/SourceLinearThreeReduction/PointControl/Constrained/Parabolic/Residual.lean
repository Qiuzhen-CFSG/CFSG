module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Constrained.Parabolic.Plane
public import Theory.SpecificGroups.BinaryLinear.OuterTwo
public import Theory.SpecificGroups.BinaryLinear.SmallCubicRank
public import Theory.Representation.SLHigherNaturalFirstCohomology.Elementary
public import Theory.GroupTheory.CComponent.RankTwoResidual

/-!
# The actual point and plane residuals in the linear-five endgame

The supplied kernel equality identifies I/O₂(I), using the literal action
map, with SL₅(2). Its center is trivial, its cubic rank is two, and its
outer automorphism group is a two-group. The rank-two C-component
residual theorem therefore proves I = O^{3′}(C_G(v)). Conjugation gives
the same identity at u = v^t, with component I^t.

The residual of C_G(⟨u,v⟩) lies in both actual components. The original
exchange normalizes that residual and the common point Sylow, so their
join is invariant and lies in both point joins. The remaining parabolic
argument must identify this join with C_{I C_T(v)}(⟨u,v⟩), and then prove
the rank-five and rank-ten contradictions. No such equality is assumed
or asserted here.

Source: Aschbacher--Smith, A.3.18 and 10.2.9, printed pp.51--53,752--753,
combined manuscript of 1 March 2004.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
open Stellmacher Representation
namespace CFSG.Quasithin.Chapter10.PointControl.Constrained
open Chapter3.Section02 ChapterB.InternalThompsonAction
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L} {t v : G} {I : Subgroup G}

/-- The actual action kernel gives the intrinsic component two-core quotient. -/
def LinearFiveData.componentQuotient {c : Context D t v I} (m : LinearFiveData c) :
    (I ⧸ pCore 2 I) ≃* Matrix.SpecialLinearGroup (Fin 5) (ZMod 2) := by
  let H := pointJoin T v I
  let K := I.subgroupOf H
  let := c.reduced.normal
  let f := (actionMk (internalModule D v I)).subgroupMap K
  let a : I ≃* K := (subgroupOfEquivOfLe (show I ≤ H from le_sup_left)).symm
  exact (QuotientGroup.congr _ _ a (pCore_map_iso 2 a)).trans
    (((QuotientGroup.quotientMulEquivOfEq m.kernel_eq.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective f
        ((actionMk (internalModule D v I)).subgroupMap_surjective K))).trans m.actor)

/-- In the terminal model the original point component is exactly the
three-prime residual of the full ambient point centralizer. -/
theorem LinearFiveData.component_eq_point_residual {c : Context D t v I}
    (m : LinearFiveData c) :
    (primeToResidual 3 (centralizer ({v} : Set G))).map
      (centralizer ({v} : Set G)).subtype = I := by
  let X := centralizer ({v} : Set G)
  let K := I.subgroupOf X
  let e : (K ⧸ pCore 2 K) ≃* Matrix.SpecialLinearGroup (Fin 5) (ZMod 2) :=
    (QuotientGroup.congr _ _ (subgroupOfEquivOfLe c.escaping.le_centralizer)
      (pCore_map_iso 2 _)).trans m.componentQuotient
  let := c.reduced.normal
  have hi : IsQuasisimple ((I.subgroupOf (pointJoin T v I)).map
      (actionMk (internalModule D v I))) :=
    (c.actionFacts_of_linearFiveData m).classification.1
  let : IsQuasisimple (Matrix.SpecialLinearGroup (Fin 5) (ZMod 2)) :=
    IsQuasisimple.of_mulEquiv m.actor
  let : IsQuasisimple (K ⧸ pCore 2 K) := IsQuasisimple.of_mulEquiv e.symm
  have hz : center (K ⧸ pCore 2 K) = ⊥ := by
    apply _root_.eq_bot_iff.mpr
    intro x hx
    have hh := (centerCongr e ⟨x,hx⟩).property
    change e x ∈ center (Matrix.SpecialLinearGroup (Fin 5) (ZMod 2)) at hh
    rw [Representation.OneCohomology.SLHigherNatural.binary_center_eq_bot,mem_bot] at hh
    exact e.map_eq_one_iff.mp hh
  have hr : 2 ≤ primeRank 3 (K ⧸ pCore 2 K) := by
    rw [primeRank_equiv 3 e]
    exact BinaryLinear.SmallCubicRank.five
  have hX : IsSQTK KnownSimple.IsKnownSimple X :=
    D.simpleQTKE.involution_centralizer_sqtk c.point_involution
  have ho : IsPGroup 2 (MulAut.Outer (K ⧸ pCore 2 K)) :=
    (BinaryLinear.OuterCyclic.sl_outer_isTwoGroup (Or.inr rfl)).of_equiv
      (MulAut.outerCongr e).symm
  have he := c.escaping.component.eq_primeToResidual_three_of_rank_outer_two hz hr
    (hX.stronglyQuasithin 3 (by decide) (by decide)) ho
  rw [←he,map_subgroupOf_eq_of_le c.escaping.le_centralizer]


omit [Finite G] in
private theorem map_point_centralizer (a : G ≃* G) (w : G) :
    (centralizer ({w} : Set G)).map a.toMonoidHom = centralizer ({a w} : Set G) := by
  ext g
  constructor
  · rintro ⟨x,hx,rfl⟩
    apply mem_centralizer_singleton_iff.mpr
    change a x * a w = a w * a x
    simpa only [map_mul] using congrArg a (mem_centralizer_singleton_iff.mp hx)
  · intro hg
    refine ⟨a.symm g,mem_centralizer_singleton_iff.mpr ?_,a.apply_symm_apply g⟩
    apply a.injective
    simpa only [map_mul,a.apply_symm_apply] using mem_centralizer_singleton_iff.mp hg

/-- The same embedded residual identity in the conjugate point centralizer. -/
theorem LinearFiveData.conjugate_component_eq_point_residual {c : Context D t v I}
    (m : LinearFiveData c) :
    (primeToResidual 3 (centralizer ({oppositePoint t v} : Set G))).map
      (centralizer ({oppositePoint t v} : Set G)).subtype =
        I.map (MulAut.conj t).toMonoidHom := by
  rw [←m.component_eq_point_residual,map_embedded_primeToResidual,
    map_point_centralizer]

/-- The prescribed point Sylow is the same for both original coordinates. -/
theorem LinearFiveData.opposite_pointSylow {c : Context D t v I}
    (m : LinearFiveData c) : pointSylow T (oppositePoint t v) = pointSylow T v := by
  have ht : (T : Subgroup G).map (MulAut.conj t).toMonoidHom = (T : Subgroup G) :=
    mem_normalizer_iff_map_conj_eq.mp ((T : Subgroup G).le_normalizer c.escaping.t_mem)
  have hs := mem_normalizer_iff_map_conj_eq.mp (m.pointSylow_normalized c.escaping.t_mem)
  calc
    pointSylow T (oppositePoint t v) = (pointSylow T v).map (MulAut.conj t).toMonoidHom := by
      rw [pointSylow,pointSylow,Subgroup.map_inf _ _ _ (MulAut.conj t).injective,
        ht,map_point_centralizer]
    _ = pointSylow T v := hs

/-- The plane residual lies in both of the actual conjugate components. -/
theorem LinearFiveData.plane_residual_le_components {c : Context D t v I}
    (m : LinearFiveData c) :
    (primeToResidual 3 (centralizer (pointPlane t v : Set G))).map
      (centralizer (pointPlane t v : Set G)).subtype ≤ I ⊓ I.map (MulAut.conj t).toMonoidHom := by
  apply le_inf
  · rw [←m.component_eq_point_residual]
    exact embedded_primeToResidual_mono 3 (centralizer_le
      (Set.singleton_subset_iff.mpr
        ((show zpowers v ≤ pointPlane t v from le_sup_right) (mem_zpowers v))))
  · rw [←m.conjugate_component_eq_point_residual]
    exact embedded_primeToResidual_mono 3 (centralizer_le
      (Set.singleton_subset_iff.mpr
        ((show zpowers (oppositePoint t v) ≤ pointPlane t v from le_sup_left) (mem_zpowers _))))

/-- The original exchange acts on the embedded plane residual. -/
theorem LinearFiveData.exchange_normalizes_plane_residual {c : Context D t v I}
    (m : LinearFiveData c) : t ∈ normalizer
      ((primeToResidual 3 (centralizer (pointPlane t v : Set G))).map
        (centralizer (pointPlane t v : Set G)).subtype : Set G) := by
  apply mem_normalizer_iff_map_conj_eq.mpr
  change ((primeToResidual 3 (centralizer (pointPlane t v : Set G))).map
    (centralizer (pointPlane t v : Set G)).subtype).map (MulAut.conj t).toMonoidHom = _
  rw [map_embedded_primeToResidual]
  have hc := mem_normalizer_iff_map_conj_eq.mp
    (normalizer_le_normalizer_centralizer (pointPlane t v) m.exchange_normalizes_plane)
  change (centralizer (pointPlane t v : Set G)).map (MulAut.conj t).toMonoidHom = _ at hc
  rw [hc]

/-- The source residual and Sylow supplement is t-invariant and lies in both
original point joins. The remaining parabolic geometry must prove that it
exhausts the point-join centralizer of E. -/
theorem LinearFiveData.plane_residual_supplement {c : Context D t v I}
    (m : LinearFiveData c) :
    let R := (primeToResidual 3 (centralizer (pointPlane t v : Set G))).map
      (centralizer (pointPlane t v : Set G)).subtype
    t ∈ normalizer ((R ⊔ pointSylow T v : Subgroup G) : Set G) ∧
      R ⊔ pointSylow T v ≤
        (pointJoin T v I ⊓ centralizer (pointPlane t v : Set G)) ⊓
        pointJoin T (oppositePoint t v) (I.map (MulAut.conj t).toMonoidHom) := by
  dsimp only
  constructor
  · exact normalizer_inf_normalizer_le_normalizer_sup _ _
      ⟨m.exchange_normalizes_plane_residual,m.pointSylow_normalized c.escaping.t_mem⟩
  · apply le_inf
    · apply le_inf
      · exact sup_le ((m.plane_residual_le_components.trans inf_le_left).trans le_sup_left)
          le_sup_right
      · exact sup_le (map_subtype_le _) m.pointSylow_centralizes_plane
    · change _ ≤ I.map (MulAut.conj t).toMonoidHom ⊔ pointSylow T (oppositePoint t v)
      rw [m.opposite_pointSylow]
      exact sup_le ((m.plane_residual_le_components.trans inf_le_right).trans le_sup_left)
        le_sup_right

end CFSG.Quasithin.Chapter10.PointControl.Constrained
