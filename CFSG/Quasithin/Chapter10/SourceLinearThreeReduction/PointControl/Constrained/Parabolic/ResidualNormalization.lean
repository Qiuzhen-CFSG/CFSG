module
public import Theory.SpecificGroups.BinaryLinear.FiveFlagGeometry.ResidualExchange
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Constrained.Parabolic.RankTen

/-!
# The original moving parabolic normalizes the escaping residual

The nonzero natural point is not fixed by the original component, so the
literal join L C_T(v) contains a rank-one node P_f outside C_{I C_T(v)}(E).
The already constructed P_c and its conjugate have solvable join. Their
exchange fixes the escaping node P; the flag diagram therefore identifies
the actual quotient of P P_f by its two-core as S₃ × S₃. The residual
normality theorem proves that P_f normalizes O²(P). Since t fixes P, its
conjugate P_f^t normalizes the same embedded residual.

This proves the normalization assertion of the rank-five source argument,
including all original inclusions and quotient maps. The elementary-nine
actor and ensuing cubic-rank contradiction remain with the final owner
qt-d-10-nona5-point-constrained, together with the earlier model reduction.

Source: Aschbacher--Smith, 10.2.9, printed p.753.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher Representation
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter10.PointControl.Constrained
open Chapter3.Section02 ChapterB.InternalThompsonAction
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L} {t v : G} {I : Subgroup G}

omit [Finite G] in
private theorem solvable_subgroupOf_iff (A H : Subgroup G) (hAH : A ≤ H) :
    Group.IsSolvable (A.subgroupOf H) ↔ Group.IsSolvable A := by
  let e := subgroupOfEquivOfLe hAH
  constructor
  · intro hs
    let := hs
    exact Group.isSolvable_of_surjective (f := e.toMonoidHom) e.surjective
  · intro hs
    let := hs
    exact Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective

/-- The original component does not centralize its nonzero natural point. -/
theorem LinearFiveData.component_not_le_plane {c : Context D t v I}
    (m : LinearFiveData c) : ¬ L ≤ planeCentralizer T t v I := by
  intro h
  have hLC : L ≤ centralizer ({oppositePoint t v} : Set G) := by
    have hh := h.trans inf_le_right
    exact hh.trans (centralizer_le (Set.singleton_subset_iff.mpr
      ((show zpowers (oppositePoint t v) ≤ pointPlane t v from le_sup_left) (mem_zpowers _))))
  have he : componentPointCentralizer L t v = L := inf_eq_left.mpr hLC
  have hi := m.componentPointCentralizer_index
  rw [he,subgroupOf_self,index_top] at hi
  omega

/-- Choose the actual noncentralizing node inside L C_T(v). -/
theorem LinearFiveData.exists_component_moving_node {c : Context D t v I}
    (m : LinearFiveData c) :
    ∃ F : Subgroup G, pointSylow T v ⋖ F ∧ F ≤ L ⊔ pointSylow T v ∧
      ¬ F ≤ planeCentralizer T t v I := by
  let H := pointJoin T v I
  let C := planeCentralizer T t v I
  let K := L ⊔ pointSylow T v
  have hKH : K ≤ H := sup_le (c.escaping.strict.le.trans le_sup_left) le_sup_right
  obtain ⟨S,hS⟩ := c.join_sylow
  have hSK : (S : Subgroup H) ≤ K.subgroupOf H := by
    intro x hx
    exact (show pointSylow T v ≤ K from le_sup_right) (hS ▸ mem_map_of_mem H.subtype hx)
  have hSC : (S : Subgroup H) ≤ C.subgroupOf H := by
    intro x hx
    exact (le_inf le_sup_right m.pointSylow_centralizes_plane)
      (hS ▸ mem_map_of_mem H.subtype hx)
  have hKC : ¬ K.subgroupOf H ≤ C.subgroupOf H := by
    intro h
    have hh := map_mono (f := H.subtype) h
    rw [map_subgroupOf_eq_of_le hKH,map_subgroupOf_eq_of_le (show C ≤ H from inf_le_left)] at hh
    exact m.component_not_le_plane (le_sup_left.trans hh)
  obtain ⟨F,hF,hFK,hFC⟩ := BinaryLinear.FiveFlagGeometry.exists_rankOne_escaping_of_two_kernel
    m.joinAction m.joinAction_surjective m.joinAction_kernel_two S
    (K.subgroupOf H) (C.subgroupOf H) hSK hSC hKC
  refine ⟨F.map H.subtype,?_,?_,?_⟩
  · have hh := (covBy_map_subtype_iff H _ _).mpr hF
    rwa [hS] at hh
  · have hh := map_mono (f := H.subtype) hFK
    rwa [map_subgroupOf_eq_of_le hKH] at hh
  · intro h
    apply hFC
    exact (le_comap_map H.subtype F).trans (comap_mono h)

/-- The exchanged nodes force the actual S₃ × S₃ pair and normalization
of O²(P) by both the original moving node and its conjugate. -/
theorem LinearFiveData.exists_residual_normalizing_pair {c : Context D t v I}
    (m : LinearFiveData c) :
    ∃ P F : Subgroup G,
      pointSylow T v ⋖ P ∧ P ≤ planeCentralizer T t v I ∧
      ¬ P ≤ D.maximalLocal ∧ t ∈ normalizer (P : Set G) ∧
      pointSylow T v ⋖ F ∧ F ≤ L ⊔ pointSylow T v ∧
      ¬ F ≤ planeCentralizer T t v I ∧
      Nonempty (((P ⊔ F : Subgroup G) ⧸ pCore 2 (P ⊔ F : Subgroup G)) ≃*
        (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3))) ∧
      F ⊔ F.map (MulAut.conj t).toMonoidHom ≤
        normalizer ((pResidual 2 P).map P.subtype : Set G) := by
  let H := pointJoin T v I
  let C := planeCentralizer T t v I
  let A := componentPointNode T L t v
  let f := (MulAut.conj t).toMonoidHom
  let B := A.map f
  let node : BinaryLinear.FiveFlagGeometry.RankOneBelow (pointSylow T v) C :=
    ⟨A,m.componentPointNode_covBy,m.componentPointNode_le_plane⟩
  have hAB : A ≠ B := m.componentPointNode_moved.symm
  have hBM : B ≤ D.maximalLocal :=
    (m.rankOneExchange_le_maximalLocal_iff node).mpr m.componentPointNode_le_maximalLocal
  obtain ⟨P,hP,hPC,hPM,htP,_⟩ :=
    m.exists_exchange_fixed_escaping_rankOne_of_moved_node node
      m.componentPointNode_le_maximalLocal (fun h => m.componentPointNode_moved (congrArg Subtype.val h))
  obtain ⟨F,hF,hFK,hFC⟩ := m.exists_component_moving_node
  have hAP : A ≠ P := fun he => hPM (he ▸ m.componentPointNode_le_maximalLocal)
  have hBP : B ≠ P := fun he => hPM (he ▸ hBM)
  have hBC : B ≤ C := (m.rankOneExchange node).property.2
  have hB : pointSylow T v ⋖ B := (m.rankOneExchange node).property.1
  have hAH : A ≤ H := m.componentPointNode_le_plane.trans inf_le_left
  have hBH : B ≤ H := hBC.trans inf_le_left
  have hPH : P ≤ H := hPC.trans inf_le_left
  have hFH : F ≤ H := hFK.trans (sup_le (c.escaping.strict.le.trans le_sup_left) le_sup_right)
  have heP : P.map f = P := mem_normalizer_iff_map_conj_eq.mp htP
  let : Group.IsSolvable f.ker := by
    rw [(MonoidHom.ker_eq_bot_iff f).mpr (MulAut.conj t).injective]
    infer_instance
  have hex : Group.IsSolvable (A ⊔ P : Subgroup G) ↔
      Group.IsSolvable (B ⊔ P : Subgroup G) := by
    have he : (A ⊔ P).map f = B ⊔ P := by rw [Subgroup.map_sup,heP]
    rw [←he]
    exact (Group.isSolvable_map_iff_of_solvable_ker f _).symm
  obtain ⟨S,hS⟩ := c.join_sylow
  have cov (X : Subgroup G) (hXH : X ≤ H) (hX : pointSylow T v ⋖ X) :
      (S : Subgroup H) ⋖ X.subgroupOf H := by
    apply (covBy_map_subtype_iff H _ _).mp
    rw [hS,map_subgroupOf_eq_of_le hXH]
    exact hX
  have neq (X Y : Subgroup G) (hX : X ≤ H) (hY : Y ≤ H) (hne : X ≠ Y) :
      X.subgroupOf H ≠ Y.subgroupOf H := by
    intro he
    have hh := congrArg (Subgroup.map H.subtype) he
    rw [map_subgroupOf_eq_of_le hX,map_subgroupOf_eq_of_le hY] at hh
    exact hne hh
  have hs : Group.IsSolvable (A.subgroupOf H ⊔ B.subgroupOf H : Subgroup H) := by
    rw [←subgroupOf_sup hAH hBH]
    exact (solvable_subgroupOf_iff _ _ (sup_le hAH hBH)).mpr m.componentPointNode_pair_solvable
  have he : Group.IsSolvable (A.subgroupOf H ⊔ P.subgroupOf H : Subgroup H) ↔
      Group.IsSolvable (B.subgroupOf H ⊔ P.subgroupOf H : Subgroup H) := by
    rw [←subgroupOf_sup hAH hPH,←subgroupOf_sup hBH hPH,
      solvable_subgroupOf_iff _ _ (sup_le hAH hPH),
      solvable_subgroupOf_iff _ _ (sup_le hBH hPH)]
    exact hex
  obtain ⟨e⟩ := BinaryLinear.FiveFlagGeometry.pair_quotient_of_solvable_exchange_of_two_kernel
    m.joinAction m.joinAction_surjective m.joinAction_kernel_two S
    (C.subgroupOf H) (A.subgroupOf H) (B.subgroupOf H) (P.subgroupOf H) (F.subgroupOf H)
    (by
      intro x hx
      exact (le_inf le_sup_right m.pointSylow_centralizes_plane)
        (hS ▸ mem_map_of_mem H.subtype hx)) m.plane_maximal
    (cov A hAH m.componentPointNode_covBy) (comap_mono m.componentPointNode_le_plane)
    (cov B hBH hB) (comap_mono hBC) (cov P hPH hP) (comap_mono hPC)
    (cov F hFH hF) (by
      intro h
      have hh := map_mono (f := H.subtype) h
      rw [map_subgroupOf_eq_of_le hFH,map_subgroupOf_eq_of_le (show C ≤ H from inf_le_left)] at hh
      exact hFC hh)
    (neq A B hAH hBH hAB) (neq A P hAH hPH hAP) (neq B P hBH hPH hBP) hs he
  have hnorm := BinaryLinear.FiveFlagGeometry.pair_normalizes_residual S
    (P.subgroupOf H) (F.subgroupOf H) (cov P hPH hP).le e
  have hnormG : P ⊔ F ≤ normalizer ((pResidual 2 P).map P.subtype : Set G) := by
    have hh := (map_mono (f := H.subtype) hnorm).trans
      (((pResidual 2 (P.subgroupOf H)).map (P.subgroupOf H).subtype).le_normalizer_map H.subtype)
    rw [Subgroup.map_sup, map_subgroupOf_eq_of_le hPH,map_subgroupOf_eq_of_le hFH,
      map_embedded_pResidual,map_subgroupOf_eq_of_le hPH] at hh
    exact hh
  have hFn := (show F ≤ P ⊔ F from le_sup_right).trans hnormG
  have hFt : F.map f ≤ normalizer ((pResidual 2 P).map P.subtype : Set G) := by
    have hh := (map_mono (f := f) hFn).trans
      (((pResidual 2 P).map P.subtype).le_normalizer_map f)
    rw [map_embedded_pResidual,heP] at hh
    exact hh
  have eJ : (P ⊔ F : Subgroup G) ≃* (P.subgroupOf H ⊔ F.subgroupOf H : Subgroup H) :=
    (subgroupOfEquivOfLe (sup_le hPH hFH)).symm.trans
      (MulEquiv.subgroupCongr (subgroupOf_sup hPH hFH))
  let eqJ := QuotientGroup.congr _ _ eJ (pCore_map_iso 2 eJ)
  exact ⟨P,F,hP,hPC,hPM,htP,hF,hFK,hFC,⟨eqJ.trans e⟩,sup_le hFn hFt⟩
end CFSG.Quasithin.Chapter10.PointControl.Constrained
