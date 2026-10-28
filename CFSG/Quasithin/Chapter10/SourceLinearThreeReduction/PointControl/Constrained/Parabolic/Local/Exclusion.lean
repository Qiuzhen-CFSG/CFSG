module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Constrained.Parabolic.Local.Nodes
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Constrained.Parabolic.RankFive

/-!
# Excluding the retained four-natural row by local parabolics

The two exchanged component point nodes have solvable join. Their
exchange contradicts the rank-ten flag diagram, leaving dimension five.
The moving rank-one node and its conjugate normalize the escaping
node's two-residual. They contain an elementary nine-group disjoint
from the plane centralizer, making the residual product's three-rank
at least three. Its genuine two-local normalizer is SQTK, giving the
contradictory upper bound two.

This is the existing rank-five and rank-ten argument applied to the
smaller orbit, with its literal action kernel. Local point reselection
therefore excludes every original four-natural cover. Combined with
the previous row exclusions, every OriginalMovedCover is impossible.
Original row exhaustion remains with qt-d-10-nona5-point-constrained;
no later nonnormal generation bound or A₅ tensor exclusion is used.
Source: Aschbacher--Smith, 10.2.9, p.753.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher Representation
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.Chapter10.PointControl.Constrained
open Chapter3.Section02 ChapterB.InternalThompsonAction
open BinaryLinear.FiveFlagGeometry
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L} {t v : G} {I : Subgroup G}


theorem LocalFiveData.componentPointCentralizer_solvable {c : Context D t v I}
    (m : LocalFiveData c) : Group.IsSolvable (componentPointCentralizer L t v) := by
  apply isSolvable_of_prime_dvd_card_eq_two_or_three
  intro p hp hd
  rw [m.componentPointCentralizer_card] at hd
  obtain ⟨n,hn⟩ := (pCore_isPGroup (p := 2) (G := L)).exists_card_eq
  rw [hn] at hd
  rcases hp.dvd_mul.mp hd with h24 | h2
  · have h : p ∣ 2^3*3 := h24
    rcases hp.dvd_mul.mp h with h2 | h3
    · exact Or.inl (((Nat.dvd_prime Nat.prime_two).mp (hp.dvd_of_dvd_pow h2)).resolve_left hp.ne_one)
    · exact Or.inr (((Nat.dvd_prime Nat.prime_three).mp h3).resolve_left hp.ne_one)
  · exact Or.inl (((Nat.dvd_prime Nat.prime_two).mp (hp.dvd_of_dvd_pow h2)).resolve_left hp.ne_one)

/-- The two original component centralizers have solvable join: their
mutual commutator lies in the actual local two-core. -/
theorem LocalFiveData.componentPointCentralizer_pair_solvable {c : Context D t v I}
    (m : LocalFiveData c) : Group.IsSolvable
      (componentPointCentralizer L t v ⊔
        (componentPointCentralizer L t v).map (MulAut.conj t).toMonoidHom : Subgroup G) := by
  let A := componentPointCentralizer L t v
  let B := A.map (MulAut.conj t).toMonoidHom
  let : Group.IsSolvable A := m.componentPointCentralizer_solvable
  let : Group.IsSolvable B := Group.isSolvable_of_surjective
    ((MulAut.conj t).toMonoidHom.subgroupMap_surjective A)
  have hc : ⁅A,B⁆ ≤ (L ⊔ (T : Subgroup G)).pCoreIn 2 :=
    (commutator_mono inf_le_left (map_mono inf_le_left)).trans
      (source_conjugate_commutator_le_core D.simpleQTKE D.maximal.1
        c.escaping.t_mem c.escaping.t_not_normalizes)
  let : Group.IsNilpotent (⁅A,B⁆ : Subgroup G) :=
    ((isPGroup_pCoreIn 2 (L ⊔ (T : Subgroup G))).to_le hc).isNilpotent
  exact Group.isSolvable_sup_of_solvable_commutator A B

/-- The literal Pc and its t-conjugate generate a solvable subgroup. -/
theorem LocalFiveData.componentPointNode_pair_solvable {c : Context D t v I}
    (m : LocalFiveData c) : Group.IsSolvable
      (componentPointNode T L t v ⊔
        (componentPointNode T L t v).map (MulAut.conj t).toMonoidHom : Subgroup G) := by
  let A := componentPointCentralizer L t v
  let B := A.map (MulAut.conj t).toMonoidHom
  let S := pointSylow T v
  let f := (MulAut.conj t).toMonoidHom
  have hS : S.map f = S := mem_normalizer_iff_map_conj_eq.mp
    (m.pointSylow_normalized c.escaping.t_mem)
  have hSA : S ≤ normalizer (A : Set G) := m.pointSylow_normalizes_componentPointCentralizer
  have hSB : S ≤ normalizer (B : Set G) := by
    rw [←hS]
    exact (map_mono hSA).trans (A.le_normalizer_map f)
  have hSAB : S ≤ normalizer ((A ⊔ B : Subgroup G) : Set G) :=
    (le_inf hSA hSB).trans (normalizer_inf_normalizer_le_normalizer_sup A B)
  let : Group.IsSolvable (A ⊔ B : Subgroup G) := m.componentPointCentralizer_pair_solvable
  let : Group.IsNilpotent S := ((Chapter1.isSylowIn_iff.mp c.join_sylow).1).isNilpotent
  have hs := Group.isSolvable_sup_of_normalizes (A ⊔ B) S hSAB
  have he : componentPointNode T L t v ⊔
      (componentPointNode T L t v).map f = (A ⊔ B) ⊔ S := by
    change (A ⊔ S) ⊔ (A ⊔ S).map f = _
    rw [Subgroup.map_sup,hS]
    exact sup_sup_sup_comm A S B S |>.trans (by rw [sup_idem])
  rw [he]
  exact hs


omit [Finite G] in
private theorem RankTen_solvable_subgroupOf_iff (A H : Subgroup G) (hAH : A ≤ H) :
    Group.IsSolvable (A.subgroupOf H) ↔ Group.IsSolvable A := by
  let e := subgroupOfEquivOfLe hAH
  constructor
  · intro hs
    let := hs
    exact Group.isSolvable_of_surjective (f := e.toMonoidHom) e.surjective
  · intro hs
    let := hs
    exact Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective

/-- The source rank-ten plane centralizer has two-core quotient of order 1008. -/
theorem LocalFiveData.plane_quotient_card_ten {c : Context D t v I}
    (m : LocalFiveData c)
    (hd : letI := m.reduced.elementary
      Module.finrank (ZMod 2) (Additive (localFiveModule T t v I)) = 10) :
    Nat.card (planeCentralizer T t v I ⧸ pCore 2 (planeCentralizer T t v I)) = 1008 := by
  obtain ⟨_,⟨e⟩⟩ := m.plane_structure_ten hd
  rw [Nat.card_congr e.toEquiv,Nat.card_prod]
  have hc : Nat.card (Matrix.ProjectiveSpecialLinearGroup (Fin 3) (ZMod 2)) = 168 := by
    rw [←Nat.card_congr BinaryLinear.SmallParabolicLevi.linearThreeEquivProjective.toEquiv,
      ←Nat.card_congr (BinaryLinear.OuterCyclic.slEquivLinear 3).toEquiv]
    exact BinaryLinear.NaturalThreePoint.group_card
  rw [hc,Nat.card_eq_fintype_card,Fintype.card_perm,Fintype.card_fin]
  decide

/-- The rank-ten branch of the actual constrained linear-five configuration
is impossible. The original exchange identifies joins of different solvability. -/
theorem LocalFiveData.not_dimension_ten {c : Context D t v I}
    (m : LocalFiveData c)
    (hd : letI := m.reduced.elementary
      Module.finrank (ZMod 2) (Additive (localFiveModule T t v I)) = 10) : False := by
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
  have hAP : A ≠ P := fun he => hPM (he ▸ m.componentPointNode_le_maximalLocal)
  have hBP : B ≠ P := fun he => hPM (he ▸ hBM)
  have hBC : B ≤ C := (m.rankOneExchange node).property.2
  have hB : pointSylow T v ⋖ B := (m.rankOneExchange node).property.1
  have hAH : A ≤ H := m.componentPointNode_le_plane.trans inf_le_left
  have hBH : B ≤ H := hBC.trans inf_le_left
  have hPH : P ≤ H := hPC.trans inf_le_left
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
  have hS' : (S : Subgroup H) = (pointSylow T v).subgroupOf H := by
    apply map_injective H.subtype_injective
    rw [hS,map_subgroupOf_eq_of_le le_sup_right]
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
  let eC := subgroupOfEquivOfLe (show C ≤ H from inf_le_left)
  let eqC := QuotientGroup.congr _ _ eC (pCore_map_iso 2 eC)
  have hcard : Nat.card (C.subgroupOf H ⧸ pCore 2 (C.subgroupOf H)) = 1008 :=
    (Nat.card_congr eqC.toEquiv).trans (m.plane_quotient_card_ten hd)
  have hs : Group.IsSolvable (A.subgroupOf H ⊔ B.subgroupOf H : Subgroup H) := by
    rw [←subgroupOf_sup hAH hBH]
    exact (RankTen_solvable_subgroupOf_iff _ _ (sup_le hAH hBH)).mpr m.componentPointNode_pair_solvable
  have he : Group.IsSolvable (A.subgroupOf H ⊔ P.subgroupOf H : Subgroup H) ↔
      Group.IsSolvable (B.subgroupOf H ⊔ P.subgroupOf H : Subgroup H) := by
    rw [←subgroupOf_sup hAH hPH,←subgroupOf_sup hBH hPH,
      RankTen_solvable_subgroupOf_iff _ _ (sup_le hAH hPH),
      RankTen_solvable_subgroupOf_iff _ _ (sup_le hBH hPH)]
    exact hex
  apply BinaryLinear.FiveFlagGeometry.no_solvable_exchange_of_two_kernel
    m.joinAction m.joinAction_surjective m.joinAction_kernel_two S
    (C.subgroupOf H) (A.subgroupOf H) (B.subgroupOf H) (P.subgroupOf H)
    _ m.plane_maximal hcard
    (cov A hAH m.componentPointNode_covBy) (comap_mono m.componentPointNode_le_plane)
    (cov B hBH hB) (comap_mono hBC) (cov P hPH hP) (comap_mono hPC)
    (neq A B hAH hBH hAB) (neq A P hAH hPH hAP) (neq B P hBH hPH hBP) hs he
  rw [hS']
  exact comap_mono (le_inf le_sup_right m.pointSylow_centralizes_plane)

/-- The rank-ten case is removed without any extra preparation or model callback. -/
theorem LocalFiveData.dimension_five {c : Context D t v I} (m : LocalFiveData c) :
    letI := m.reduced.elementary
    Module.finrank (ZMod 2) (Additive (localFiveModule T t v I)) = 5 :=
  m.dimension.resolve_right m.not_dimension_ten


omit [Finite G] in
private theorem ResidualNormalization_solvable_subgroupOf_iff (A H : Subgroup G) (hAH : A ≤ H) :
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
theorem LocalFiveData.component_not_le_plane {c : Context D t v I}
    (m : LocalFiveData c) : ¬ L ≤ planeCentralizer T t v I := by
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
theorem LocalFiveData.exists_component_moving_node {c : Context D t v I}
    (m : LocalFiveData c) :
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
theorem LocalFiveData.exists_residual_normalizing_pair {c : Context D t v I}
    (m : LocalFiveData c) :
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
    exact (ResidualNormalization_solvable_subgroupOf_iff _ _ (sup_le hAH hBH)).mpr m.componentPointNode_pair_solvable
  have he : Group.IsSolvable (A.subgroupOf H ⊔ P.subgroupOf H : Subgroup H) ↔
      Group.IsSolvable (B.subgroupOf H ⊔ P.subgroupOf H : Subgroup H) := by
    rw [←subgroupOf_sup hAH hPH,←subgroupOf_sup hBH hPH,
      ResidualNormalization_solvable_subgroupOf_iff _ _ (sup_le hAH hPH),
      ResidualNormalization_solvable_subgroupOf_iff _ _ (sup_le hBH hPH)]
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

/-- The source rank-five parabolics satisfy the actual two-local cubic-rank
bound on the residual product, including both moving nodes. -/
theorem LocalFiveData.exists_rankFive_residual_configuration {c : Context D t v I}
    (m : LocalFiveData c) :
    ∃ P F : Subgroup G,
      pointSylow T v ⋖ P ∧ P ≤ planeCentralizer T t v I ∧
      ¬ P ≤ D.maximalLocal ∧ t ∈ normalizer (P : Set G) ∧
      pointSylow T v ⋖ F ∧ F ≤ L ⊔ pointSylow T v ∧
      ¬ F ≤ planeCentralizer T t v I ∧
      Nonempty (((P ⊔ F : Subgroup G) ⧸ pCore 2 (P ⊔ F : Subgroup G)) ≃*
        (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3))) ∧
      F ⊔ F.map (MulAut.conj t).toMonoidHom ≤
        normalizer ((pResidual 2 P).map P.subtype : Set G) ∧
      IsSQTK KnownSimple.IsKnownSimple (normalizer ((pResidual 2 P).map P.subtype : Set G)) ∧
      primeRank 3 ((pResidual 2 P).map P.subtype ⊔
        (F ⊔ F.map (MulAut.conj t).toMonoidHom) : Subgroup G) ≤ 2 := by
  obtain ⟨P,F,hP,hPC,hPM,htP,hF,hFK,hFC,he,hn⟩ := m.exists_residual_normalizing_pair
  have hPH : P ≤ pointJoin T v I := hPC.trans inf_le_left
  exact ⟨P,F,hP,hPC,hPM,htP,hF,hFK,hFC,he,hn,
    c.node_residual_normalizer_sqtk P hP.lt hPH,
    c.node_residual_join_three_rank P _ hP.lt hPH hn⟩


/-- A proper Sylow overgroup in the actual five-space action has a cubic divisor. -/
theorem LocalFiveData.three_dvd_sylow_overgroup {c : Context D t v I}
    (m : LocalFiveData c) (F : Subgroup G) (hSF : pointSylow T v < F)
    (hFH : F ≤ pointJoin T v I) : 3 ∣ Nat.card F := by
  let H := pointJoin T v I
  let X := F.subgroupOf H
  obtain ⟨S,hS⟩ := c.join_sylow
  have hSX : (S : Subgroup H) ≤ X := by
    intro x hx
    exact hSF.le (hS ▸ mem_map_of_mem H.subtype hx)
  by_contra h3
  have hX3 : ¬ 3 ∣ Nat.card X := by
    rwa [Nat.card_congr (subgroupOfEquivOfLe hFH).toEquiv]
  have him3 : ¬ 3 ∣ Nat.card (X.map m.joinAction) := fun h =>
    hX3 (h.trans (card_dvd_of_surjective (m.joinAction.subgroupMap X)
      (m.joinAction.subgroupMap_surjective X)))
  have hp := BinaryLinear.FiveFlagGeometry.isPGroup_of_sylow_le_of_not_three_dvd
    (S.mapSurjective m.joinAction_surjective) (X.map m.joinAction) (map_mono hSX) him3
  have hX2 : IsPGroup 2 X :=
    (hp.comap_of_ker_isPGroup m.joinAction m.joinAction_kernel_two).to_le
      (le_comap_map m.joinAction X)
  have he := S.is_maximal' hX2 hSX
  have hh := congrArg (Subgroup.map H.subtype) he
  rw [map_subgroupOf_eq_of_le hFH,hS] at hh
  exact hSF.ne hh.symm

/-- The literal moving node fixes u precisely on its common point Sylow. -/
theorem LocalFiveData.moving_node_point_centralizer {c : Context D t v I}
    (m : LocalFiveData c) (F : Subgroup G) (hSF : pointSylow T v ⋖ F)
    (hFH : F ≤ pointJoin T v I) (hFC : ¬ F ≤ planeCentralizer T t v I) :
    F ⊓ centralizer ({oppositePoint t v} : Set G) = pointSylow T v := by
  have hSC : pointSylow T v ≤ centralizer ({oppositePoint t v} : Set G) :=
    m.pointSylow_centralizes_plane.trans (centralizer_le (Set.singleton_subset_iff.mpr
      ((show zpowers (oppositePoint t v) ≤ pointPlane t v from le_sup_left) (mem_zpowers _))))
  rcases (covBy_iff_lt_and_eq_or_eq.mp hSF).2 _ (le_inf hSF.le hSC) inf_le_left with h | h
  · exact h
  · apply False.elim
    apply hFC
    change F ≤ pointJoin T v I ⊓ centralizer (pointPlane t v : Set G)
    rw [c.join_plane_centralizer]
    exact le_inf hFH (h.symm.le.trans inf_le_right)

omit [Finite G] in
private theorem prime_card_elementary (X : Subgroup G) (hc : Nat.card X = 3) :
    IsElementaryAbelian 3 X := by
  let : IsCyclic X := isCyclic_of_prime_card hc
  exact { toIsMulCommutative := inferInstance
          exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr
            (fun x => by rw [←hc]; exact pow_card_eq_one') }

/-- A cubic factor in the literal moving node belongs to L and meets C_G(u) trivially. -/
theorem LocalFiveData.exists_moving_cubic {c : Context D t v I}
    (m : LocalFiveData c) (F : Subgroup G) (hSF : pointSylow T v ⋖ F)
    (hFL : F ≤ L ⊔ pointSylow T v) (hFC : ¬ F ≤ planeCentralizer T t v I) :
    ∃ X : Subgroup G, X ≤ F ∧ X ≤ L ∧ IsElementaryAbelian 3 X ∧ Nat.card X = 3 ∧
      Disjoint X (centralizer ({oppositePoint t v} : Set G)) := by
  have hFH : F ≤ pointJoin T v I := hFL.trans
    (sup_le (c.escaping.strict.le.trans le_sup_left) le_sup_right)
  obtain ⟨x,hx⟩ := exists_prime_orderOf_dvd_card' (G := F) 3
    (m.three_dvd_sylow_overgroup F hSF.lt hFH)
  let X := zpowers (x : G)
  have hX : X ≤ F := zpowers_le.mpr x.property
  have hcX : Nat.card X = 3 := by
    rw [Nat.card_zpowers, Subgroup.orderOf_coe x,hx]
  have hpX : IsPPerfect 2 X := by
    intro N hN hp
    let _ := hN
    have hd : Nat.card (X ⧸ N) ∣ 3 := hcX ▸ N.card_quotient_dvd_card
    have hc : Nat.card (X ⧸ N) = 1 := by
      obtain ⟨n,hn⟩ := hp.exists_card_eq
      rcases Nat.prime_three.eq_one_or_self_of_dvd _ hd with h | h
      · exact h
      · have hdiv : 2 ∣ 3 := h ▸ (hn ▸ dvd_pow_self 2 (by
          intro hz
          simp [hz] at hn
          omega))
        omega
    exact (index_eq_one.mp hc)
  have hXL : X ≤ L := le_of_isPPerfect_of_le_sup_of_normalizes X L (pointSylow T v)
    hpX ((Chapter1.isSylowIn_iff.mp c.join_sylow).1) c.escaping.sylow_normalizes (hX.trans hFL)
  have he := m.moving_node_point_centralizer F hSF hFH hFC
  have hxs : Disjoint X (pointSylow T v) := by
    obtain ⟨n,hn⟩ := ((Chapter1.isSylowIn_iff.mp c.join_sylow).1).exists_card_eq
    exact disjoint_of_coprime_natCard (by rw [hcX,hn]; exact (by decide : Nat.Coprime 3 2).pow_right n)
  refine ⟨X,hX,hXL,prime_card_elementary X hcX,hcX,?_⟩
  apply disjoint_def.mpr
  intro z hz hzc
  exact hxs.le_bot ⟨hz,he ▸ (show z ∈ F ⊓ centralizer ({oppositePoint t v} : Set G) from ⟨hX hz,hzc⟩)⟩

/-- The two original cubic factors lift together; the resulting nine-group
has no nonidentity element centralizing the original plane. -/
theorem LocalFiveData.exists_cubic_pair {c : Context D t v I}
    (m : LocalFiveData c) (X : Subgroup G) (hXL : X ≤ L)
    (hXe : IsElementaryAbelian 3 X) (hXc : Nat.card X = 3)
    (hXu : Disjoint X (centralizer ({oppositePoint t v} : Set G))) :
    ∃ E : Subgroup G, E ≤ X ⊔ X.map (MulAut.conj t).toMonoidHom ∧
      IsElementaryAbelian 3 E ∧ Nat.card E = 9 ∧
      Disjoint E (centralizer (pointPlane t v : Set G)) := by
  let H := localOrbit T L
  let f := (MulAut.conj t).toMonoidHom
  let Y := X.map f
  have hXH : X ≤ H := hXL.trans (le_componentOrbit L T)
  have hYH : Y ≤ H := (map_mono hXL).trans
    (le_iSup (fun s : (T : Subgroup G) => L.map (MulAut.conj s.val).toMonoidHom)
      ⟨t,c.escaping.t_mem⟩)
  have hXv : X ≤ centralizer ({v} : Set G) :=
    hXL.trans (c.escaping.strict.le.trans c.escaping.le_centralizer)
  have hYu : Y ≤ centralizer ({oppositePoint t v} : Set G) := by
    rintro _ ⟨x,hx,rfl⟩
    apply mem_centralizer_singleton_iff.mpr
    change f x * f v = f v * f x
    simpa only [map_mul] using congrArg f (mem_centralizer_singleton_iff.mp (hXv hx))
  have hYv : Disjoint Y (centralizer ({v} : Set G)) := by
    apply disjoint_def.mpr
    rintro _ ⟨x,hx,rfl⟩ hv
    have hc : x ∈ centralizer ({oppositePoint t v} : Set G) := by
      apply mem_centralizer_singleton_iff.mpr
      apply (MulAut.conj t).injective
      change f (x * oppositePoint t v) = f (oppositePoint t v * x)
      simpa only [map_mul,show f (oppositePoint t v) = v from m.exchange_opposite] using
        mem_centralizer_singleton_iff.mp hv
    rw [show x = 1 from hXu.le_bot ⟨hx,hc⟩,map_one]
  let A := X.subgroupOf H
  let B := Y.subgroupOf H
  let C := (centralizer ({oppositePoint t v} : Set G)).subgroupOf H
  let V := (centralizer ({v} : Set G)).subgroupOf H
  let q := QuotientGroup.mk' (pCore 2 H)
  let := hXe
  let : IsElementaryAbelian 3 Y := IsElementaryAbelian.map f
  let : IsElementaryAbelian 3 A := IsElementaryAbelian.subgroupOf hXH
  let : IsElementaryAbelian 3 B := IsElementaryAbelian.subgroupOf hYH
  have hk : Nat.Coprime 3 (Nat.card q.ker) := by
    rw [QuotientGroup.ker_mk']
    obtain ⟨n,hn⟩ := (pCore_isPGroup (p := 2) (G := H)).exists_card_eq
    rw [hn]
    exact (by decide : Nat.Coprime 3 2).pow_right n
  have hAB : ⁅A,B⁆ ≤ pCore 2 H := by
    apply (map_le_map_iff_of_injective H.subtype_injective).mp
    rw [map_commutator,map_subgroupOf_eq_of_le hXH,map_subgroupOf_eq_of_le hYH]
    exact (commutator_mono hXL (map_mono hXL)).trans c.factor_commutator_le_orbit_core
  have hcomm : A.map q ≤ centralizer (B.map q : Set (H ⧸ pCore 2 H)) := by
    apply commutator_eq_bot_iff_le_centralizer.mp
    rw [←map_commutator,Subgroup.map_eq_bot_iff,QuotientGroup.ker_mk']
    exact hAB
  have hkerCV : q.ker ≤ C ⊓ V := by
    intro x hx
    have hxQ : (x : G) ∈ H.pCoreIn 2 := mem_map_of_mem H.subtype
      (show x ∈ pCore 2 H from (QuotientGroup.eq_one_iff x).mp hx)
    have hxE := (source_fullModule_orbit_core_centralizes D hxQ)
    constructor
    · exact mem_centralizer_singleton_iff.mpr
        (hxE _ (m.plane_le_fullModule (mem_sup_left (mem_zpowers _)))).symm
    · exact mem_centralizer_singleton_iff.mpr
        (hxE _ (m.plane_le_fullModule (mem_sup_right (mem_zpowers _)))).symm
  have hAc : Nat.card A = 3 := (Nat.card_congr (subgroupOfEquivOfLe hXH).toEquiv).trans hXc
  have hBc : Nat.card B = 3 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hYH).toEquiv,card_map_of_injective (MulAut.conj t).injective,hXc]
  have hAC : Disjoint A C := by
    apply disjoint_def.mpr
    intro x hx hc
    exact Subtype.ext (hXu.le_bot ⟨hx,hc⟩)
  have hBV : Disjoint B V := by
    apply disjoint_def.mpr
    intro x hx hc
    exact Subtype.ext (hYv.le_bot ⟨hx,hc⟩)
  obtain ⟨E,hE,hEe,hEc,hEd⟩ := exists_separated_elementary_pair q hk A B C V
    hAc hBc hcomm hkerCV (comap_mono hXv) (comap_mono hYu) hAC hBV
  let := hEe
  refine ⟨E.map H.subtype,?_,IsElementaryAbelian.map H.subtype,?_,?_⟩
  · have hh := map_mono (f := H.subtype) hE
    rwa [Subgroup.map_sup,map_subgroupOf_eq_of_le hXH,map_subgroupOf_eq_of_le hYH] at hh
  · simpa only [card_map_of_injective H.subtype_injective,show (3:ℕ)^2=9 from by decide] using hEc
  · apply disjoint_def.mpr
    rintro _ ⟨x,hx,rfl⟩ hc
    apply congrArg Subtype.val (hEd.le_bot ⟨hx,?_,?_⟩ : x = 1)
    · exact mem_centralizer_singleton_iff.mpr
        (hc _ (mem_sup_left (mem_zpowers _))).symm
    · exact mem_centralizer_singleton_iff.mpr
        (hc _ (mem_sup_right (mem_zpowers _))).symm

/-- The literal moving pair contains the nine-group required by the source;
its common point-centralizer intersection is trivial. -/
theorem LocalFiveData.exists_moving_nine {c : Context D t v I}
    (m : LocalFiveData c) (F : Subgroup G) (hSF : pointSylow T v ⋖ F)
    (hFL : F ≤ L ⊔ pointSylow T v) (hFC : ¬ F ≤ planeCentralizer T t v I) :
    ∃ E : Subgroup G, E ≤ F ⊔ F.map (MulAut.conj t).toMonoidHom ∧
      IsElementaryAbelian 3 E ∧ Nat.card E = 9 ∧
      Disjoint E (centralizer (pointPlane t v : Set G)) := by
  obtain ⟨X,hXF,hXL,hXe,hXc,hXu⟩ := m.exists_moving_cubic F hSF hFL hFC
  obtain ⟨E,hE,he,hc,hd⟩ := m.exists_cubic_pair X hXL hXe hXc hXu
  exact ⟨E,hE.trans (sup_le_sup hXF (map_mono hXF)),he,hc,hd⟩



/-- The literal rank-one node has cubic residual modulo its own two-core. -/
theorem LocalFiveData.node_residual_quotient_card {c : Context D t v I}
    (m : LocalFiveData c) (P : Subgroup G) (hSP : pointSylow T v ⋖ P)
    (hPH : P ≤ pointJoin T v I) :
    Nat.card (((pResidual 2 P).map P.subtype) ⧸
      pCore 2 ((pResidual 2 P).map P.subtype)) = 3 := by
  let H := pointJoin T v I
  obtain ⟨S,hS⟩ := c.join_sylow
  have hp : (S : Subgroup H) ⋖ P.subgroupOf H := by
    apply (covBy_map_subtype_iff H _ _).mp
    rw [hS,map_subgroupOf_eq_of_le hPH]
    exact hSP
  have hc := BinaryLinear.FiveFlagGeometry.rankOne_residual_quotient_card_of_two_kernel
    m.joinAction m.joinAction_surjective m.joinAction_kernel_two S (P.subgroupOf H) hp
  let eP := subgroupOfEquivOfLe hPH
  let eR : pResidual 2 (P.subgroupOf H) ≃* pResidual 2 P :=
    (eP.subgroupMap (pResidual 2 (P.subgroupOf H))).trans
      (MulEquiv.subgroupCongr (map_pResidual_of_surjective 2 eP.toMonoidHom eP.surjective))
  let e := eR.trans ((pResidual 2 P).equivMapOfInjective P.subtype P.subtype_injective)
  rw [←Nat.card_congr (QuotientGroup.congr _ _ e (pCore_map_iso 2 e)).toEquiv]
  exact hc

/-- Both terminal dimensions are impossible on the original linear-five data.
The moving nine-group is independent of the residual because the latter
centralizes the original plane. Their actual join violates the SQTK bound. -/
theorem LocalFiveData.impossible {c : Context D t v I} (m : LocalFiveData c) : False := by
  obtain ⟨P,F,hP,hPC,_,_,hF,hFL,hFC,_,hn,_,hu⟩ := m.exists_rankFive_residual_configuration
  obtain ⟨E,hEF,hEe,hEc,hEd⟩ := m.exists_moving_nine F hF hFL hFC
  let R := (pResidual 2 P).map P.subtype
  have hRC : R ≤ centralizer (pointPlane t v : Set G) :=
    (map_subtype_le _).trans (hPC.trans inf_le_right)
  have hd : Disjoint R E := (hEd.mono_right hRC).symm
  have hER : E ≤ normalizer (R : Set G) := hEF.trans hn
  have hl := three_le_primeRank_of_nine_normalizing_cubic_section R E hER
    (m.node_residual_quotient_card P hP (hPC.trans inf_le_left)) hEe hEc hd
  have hb := (primeRank_mono 3 (sup_le_sup le_rfl hEF)).trans hu
  change primeRank 3 (R ⊔ E : Subgroup G) ≤ 2 at hb
  omega


/-- The local endgame excludes the retained four-copy marking on the original setup. -/
theorem Context.no_fourNaturalCover (c : Context D t v I) (h : FourNaturalCover D) : False := by
  obtain ⟨u,hu,hne,_⟩ := c.local_seed_orbit_of_original_moved_cover (.fourNatural h)
  obtain ⟨J,c',hw,hs⟩ := c.reselect_local_point_of_four_natural_cover h hu hne
  exact (LocalFiveData.impossible (c := c') ⟨h,hs,hw⟩)

/-- Every literal marked original row is excluded. Exhaustion is separate. -/
theorem Context.no_originalMovedCover (c : Context D t v I) (h : OriginalMovedCover D) : False :=
  c.no_fourNaturalCover (c.four_natural_of_original_moved_cover h)

end CFSG.Quasithin.Chapter10.PointControl.Constrained
