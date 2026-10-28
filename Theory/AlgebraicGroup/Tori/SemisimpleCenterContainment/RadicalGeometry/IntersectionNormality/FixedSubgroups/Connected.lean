module

public import Theory.AlgebraicGroup.Tori.SemisimpleCenterContainment.RadicalGeometry.IntersectionNormality.Basic
public import Theory.AlgebraicGroup.Unipotent.SemisimpleCommutator

/-!
Connected fixed subgroups for external torus actions (Borel, III, 9.4(1)).
A subtorus normalizing a connected unipotent subgroup has a connected fixed
subgroup. No containment of the torus in the unipotent subgroup is required.

Noetherianity reduces the centralizer to finitely many torus points. Successive
centralizers stay connected by Borel 9.3(2), and the remaining torus points
normalize each intermediate subgroup because they commute. This adapts the
finite-centralizer argument in `Solvable.SubtorusCentralizer`, replacing ambient
normality with precisely the normalizing action used in the source.
-/

universe u

namespace Theory.AlgebraicGroup.SemisimpleCenterContainment.RadicalGeometry.IntersectionNormality

variable {k : Type u} [Field k] [IsAlgClosed k]

set_option linter.style.haveILetI false

omit [IsAlgClosed k] in
private lemma carrier_isConnected_local
    {G : Variety k} [AlgebraicGroup G] (H : ClosedSubgroup G)
    (hH : _root_.IsConnected (H : Set (Variety.Point G))) :
    Variety.IsConnected H.carrierVariety := by
  let e := Variety.closedSubvarietyPointHomeomorph H.isZariskiClosed
  let : ConnectedSpace {x : Variety.Point G // x ∈ (H : Set (Variety.Point G))} :=
    Subtype.connectedSpace hH
  let : ConnectedSpace (Variety.Point H.carrierVariety) :=
    e.connectedSpace_iff.mpr inferInstance
  exact connectedSpace_iff_univ.mp inferInstance

omit [IsAlgClosed k] in
private lemma isConnected_of_carrier_local
    {G : Variety k} [AlgebraicGroup G] (H : ClosedSubgroup G)
    (hH : Variety.IsConnected H.carrierVariety) :
    _root_.IsConnected (H : Set (Variety.Point G)) := by
  let e := Variety.closedSubvarietyPointHomeomorph H.isZariskiClosed
  let : ConnectedSpace (Variety.Point H.carrierVariety) :=
    connectedSpace_iff_univ.mpr hH
  let : ConnectedSpace {x : Variety.Point G // x ∈ (H : Set (Variety.Point G))} :=
    e.connectedSpace_iff.mp inferInstance
  exact isConnected_iff_connectedSpace.mpr inferInstance

private noncomputable def listPointCentralizer
    {G : Variety k} [AlgebraicGroup G]
    (L : List (Variety.Point G)) : ClosedSubgroup G :=
  match L with
  | [] => ClosedSubgroup.top
  | s :: L => (listPointCentralizer L).inter
      (semisimpleCommutatorPointCentralizer s)

omit [IsAlgClosed k] in
private lemma mem_listPointCentralizer_iff
    {G : Variety k} [AlgebraicGroup G]
    (L : List (Variety.Point G)) (x : Variety.Point G) :
    x ∈ listPointCentralizer L ↔
      ∀ s ∈ L, x * s = s * x := by
  induction L with
  | nil =>
      constructor
      · intro _ s hs
        exact (List.not_mem_nil hs).elim
      · intro _
        change x ∈ (⊤ : Subgroup (Variety.Point G))
        exact Subgroup.mem_top x
  | cons a L ih =>
      rw [listPointCentralizer, ClosedSubgroup.mem_inter_iff, ih]
      change (_ ∧ x ∈ Subgroup.centralizer ({a} : Set (Variety.Point G))) ↔ _
      rw [Subgroup.mem_centralizer_iff]
      constructor
      · rintro ⟨hL, ha⟩ y hy
        rcases List.mem_cons.mp hy with rfl | hy
        · exact (ha y (by simp)).symm
        · exact hL y hy
      · intro h
        refine ⟨fun y hy => h y (List.mem_cons_of_mem a hy), ?_⟩
        intro y hy
        subst y
        exact (h a (by simp)).symm

omit [IsAlgClosed k] in
private theorem exists_list_centralizer_le_centralizer
    {G : Variety k} [AlgebraicGroup G] (S : ClosedSubgroup G) :
    ∃ L : List (Variety.Point G),
      (∀ s ∈ L, s ∈ S.toSubgroup) ∧
      listPointCentralizer L ≤ S.centralizer := by
  classical
  let closedSet : ClosedSubgroup G →
      TopologicalSpace.Closeds (Variety.Point G) := fun H ↦
    ⟨(H : Set (Variety.Point G)),
      Variety.isClosed_iff_isZariskiClosed.mpr H.isZariskiClosed⟩
  let family : Set (TopologicalSpace.Closeds (Variety.Point G)) :=
    {A | ∃ L : List (Variety.Point G),
      (∀ s ∈ L, s ∈ S.toSubgroup) ∧
      A = closedSet (listPointCentralizer L)}
  have hfamily : family.Nonempty := by
    refine ⟨closedSet (listPointCentralizer []), [], ?_, rfl⟩
    intro s hs
    exact (List.not_mem_nil hs).elim
  obtain ⟨A, hAfamily, hAmin⟩ :=
    noetherian_closedSets_minimumCondition G family hfamily
  rcases hAfamily with ⟨L, hLS, hAL⟩
  subst A
  refine ⟨L, hLS, ?_⟩
  by_contra hnot
  obtain ⟨x, hxL, hxC⟩ := Set.not_subset.mp hnot
  change x ∉ Subgroup.centralizer
    (S.toSubgroup : Set (Variety.Point G)) at hxC
  rw [Subgroup.mem_centralizer_iff] at hxC
  push Not at hxC
  obtain ⟨s, hsS, hsx⟩ := hxC
  let L' := s :: L
  have hL'family : closedSet (listPointCentralizer L') ∈ family := by
    refine ⟨L', ?_, rfl⟩
    intro y hy
    rcases List.mem_cons.mp hy with rfl | hy
    · exact hsS
    · exact hLS y hy
  have hproper : closedSet (listPointCentralizer L') <
      closedSet (listPointCentralizer L) := by
    constructor
    · intro y hy
      change y ∈ listPointCentralizer L' at hy
      change y ∈ listPointCentralizer L
      rw [mem_listPointCentralizer_iff] at hy ⊢
      exact fun z hz ↦ hy z (List.mem_cons_of_mem s hz)
    · intro hreverse
      have hxL' : x ∈ listPointCentralizer L' := hreverse hxL
      have hxs := (mem_listPointCentralizer_iff L' x).mp hxL' s (by simp [L'])
      exact hsx hxs.symm
  exact hAmin (closedSet (listPointCentralizer L')) hL'family hproper

private lemma isUnipotentAlgebraicGroup_of_le
    {G : Variety k} [AlgebraicGroup G] (V U : ClosedSubgroup G)
    (hVU : V ≤ U) (hU : IsUnipotentAlgebraicGroup U.carrierVariety) :
    IsUnipotentAlgebraicGroup V.carrierVariety := by
  intro v
  let x := V.inclusion.onPoints v
  have hxV : x ∈ V.toSubgroup := (V.pointEquiv v).property
  have hxU : x ∈ U.toSubgroup := hVU hxV
  let u : Variety.Point U.carrierVariety := U.pointEquiv.symm ⟨x, hxU⟩
  have huAmbient := morphism_preserves_unipotentElement U.inclusion u (hU u)
  have huval : U.inclusion.onPoints u = x := by
    change (U.pointEquiv u).val = x
    simp [u]
  rw [huval] at huAmbient
  have hv := closedSubgroup_unipotent_of_ambient V hxV huAmbient
  have hveq : V.pointEquiv.symm ⟨x, hxV⟩ = v := by
    apply V.pointEquiv.injective
    apply Subtype.ext
    rfl
  rwa [hveq] at hv

private theorem inter_pointCentralizer_isConnected
    {G : Variety k} [AlgebraicGroup G] (V : ClosedSubgroup G)
    (hVconn : Variety.IsConnected V.carrierVariety)
    (hV : IsUnipotentAlgebraicGroup V.carrierVariety)
    (s : Variety.Point G) (hsSemi : IsSemisimpleElement G s)
    (hsNorm : s ∈ Subgroup.normalizer
      (V.toSubgroup : Set (Variety.Point G))) :
    Variety.IsConnected
      (V.inter (semisimpleCommutatorPointCentralizer s)).carrierVariety := by
  letI : AlgebraicGroup V.carrierVariety := V.carrierAlgebraicGroup
  let F : ClosedSubgroup V.carrierVariety :=
    semisimpleCommutatorFixedSubgroup V s
  letI : AlgebraicGroup F.carrierVariety := F.carrierAlgebraicGroup
  let f : AlgebraicGroup.Morphism F.carrierVariety G :=
    V.inclusion.comp F.inclusion
  have hFconn : Variety.IsConnected F.carrierVariety :=
    semisimpleCommutatorFixedSubgroup_isConnected V hVconn hV s hsSemi hsNorm
  have himg : f.imageClosedSubgroup =
      V.inter (semisimpleCommutatorPointCentralizer s) := by
    apply SetLike.coe_injective
    ext x
    change (∃ z, f.onPoints z = x) ↔
      x ∈ V.toSubgroup ∧ x ∈ semisimpleCommutatorPointCentralizer s
    constructor
    · rintro ⟨z, rfl⟩
      have hzF : F.inclusion.onPoints z ∈ F := (F.pointEquiv z).property
      have hzComm :=
        (semisimpleCommutatorFixedSubgroup_mem_iff V s
          (F.inclusion.onPoints z)).mp hzF
      refine ⟨(V.pointEquiv (F.inclusion.onPoints z)).property, ?_⟩
      change V.inclusion.onPoints (F.inclusion.onPoints z) ∈
        Subgroup.centralizer ({s} : Set (Variety.Point G))
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      subst y
      exact hzComm.symm
    · rintro ⟨hxV, hxC⟩
      let v : Variety.Point V.carrierVariety :=
        V.pointEquiv.symm ⟨x, hxV⟩
      have hvval : V.inclusion.onPoints v = x := by
        change (V.pointEquiv v).val = x
        simp [v]
      have hvF : v ∈ F := by
        rw [semisimpleCommutatorFixedSubgroup_mem_iff, hvval]
        change x ∈ Subgroup.centralizer ({s} : Set (Variety.Point G)) at hxC
        exact ((Subgroup.mem_centralizer_iff.mp hxC) s (by simp)).symm
      let z : Variety.Point F.carrierVariety := F.pointEquiv.symm ⟨v, hvF⟩
      refine ⟨z, ?_⟩
      change V.inclusion.onPoints (F.inclusion.onPoints z) = x
      have hzval : F.inclusion.onPoints z = v := by
        change (F.pointEquiv z).val = v
        simp [z]
      rw [hzval, hvval]
  rw [← himg]
  exact carrier_isConnected_local f.imageClosedSubgroup
    (f.imageClosedSubgroup_isConnected hFconn)

omit [IsAlgClosed k] in
private lemma subtorus_commute_ambient
    {G : Variety k} [AlgebraicGroup G] {S : ClosedSubgroup G}
    (hS : IsSubtorus S) {x y : Variety.Point G}
    (hx : x ∈ S.toSubgroup) (hy : y ∈ S.toSubgroup) : x * y = y * x := by
  let xS : Variety.Point S.carrierVariety := S.pointEquiv.symm ⟨x, hx⟩
  let yS : Variety.Point S.carrierVariety := S.pointEquiv.symm ⟨y, hy⟩
  have hcomm := isMulCommutative_iff.mp hS.isMulCommutative xS yS
  have hamb := congrArg S.inclusion.onPoints hcomm
  have hxval : S.inclusion.onPoints xS = x := by
    change (S.pointEquiv xS).val = x
    simp [xS]
  have hyval : S.inclusion.onPoints yS = y := by
    change (S.pointEquiv yS).val = y
    simp [yS]
  simpa only [map_mul, hxval, hyval] using hamb

private lemma subtorus_semisimple_ambient
    {G : Variety k} [AlgebraicGroup G] {S : ClosedSubgroup G}
    (hS : IsSubtorus S) {x : Variety.Point G}
    (hx : x ∈ S.toSubgroup) : IsSemisimpleElement G x := by
  let xS : Variety.Point S.carrierVariety := S.pointEquiv.symm ⟨x, hx⟩
  have hamb := morphism_preserves_semisimpleElement S.inclusion xS
    (hS.all_semisimple xS)
  have hxval : S.inclusion.onPoints xS = x := by
    change (S.pointEquiv xS).val = x
    simp [xS]
  rwa [hxval] at hamb

private theorem inter_listPointCentralizer_isConnected
    {G : Variety k} [AlgebraicGroup G] (U S : ClosedSubgroup G)
    (hUconn : Variety.IsConnected U.carrierVariety)
    (hU : IsUnipotentAlgebraicGroup U.carrierVariety)
    (hSN : S ≤ U.normalizer)
    (hS : IsSubtorus S)
    (L : List (Variety.Point G))
    (hLS : ∀ s ∈ L, s ∈ S.toSubgroup) :
    Variety.IsConnected
      (U.inter (listPointCentralizer L)).carrierVariety := by
  induction L with
  | nil =>
      have heq : U.inter (listPointCentralizer []) = U := by
        apply SetLike.coe_injective
        ext x
        change (x ∈ U.toSubgroup ∧ x ∈ (⊤ : Subgroup (Variety.Point G))) ↔
          x ∈ U.toSubgroup
        simp
      rw [heq]
      exact hUconn
  | cons s L ih =>
      have hLS' : ∀ z ∈ L, z ∈ S.toSubgroup := by
        intro z hz
        exact hLS z (List.mem_cons_of_mem s hz)
      have hsS : s ∈ S.toSubgroup := hLS s (by simp)
      have hVconn := ih hLS'
      let V : ClosedSubgroup G := U.inter (listPointCentralizer L)
      have hVU : V ≤ U := by
        intro x hx
        exact hx.1
      have hVuni : IsUnipotentAlgebraicGroup V.carrierVariety :=
        isUnipotentAlgebraicGroup_of_le V U hVU hU
      have hsList : s ∈ listPointCentralizer L := by
        rw [mem_listPointCentralizer_iff]
        intro z hz
        exact subtorus_commute_ambient hS hsS (hLS' z hz)
      have hsNormU : s ∈ Subgroup.normalizer
          (U.toSubgroup : Set (Variety.Point G)) :=
        hSN hsS
      have hsNormList : s ∈ Subgroup.normalizer
          ((listPointCentralizer L).toSubgroup : Set (Variety.Point G)) :=
        (listPointCentralizer L).toSubgroup.le_normalizer hsList
      have hsNormV : s ∈ Subgroup.normalizer
          (V.toSubgroup : Set (Variety.Point G)) := by
        rw [Subgroup.mem_normalizer_iff]
        intro x
        change (x ∈ U.toSubgroup ∧ x ∈ listPointCentralizer L) ↔
          (s * x * s⁻¹ ∈ U.toSubgroup ∧
            s * x * s⁻¹ ∈ listPointCentralizer L)
        exact and_congr
          (Subgroup.mem_normalizer_iff.mp hsNormU x)
          (Subgroup.mem_normalizer_iff.mp hsNormList x)
      have hstep := inter_pointCentralizer_isConnected V hVconn hVuni s
        (subtorus_semisimple_ambient hS hsS) hsNormV
      have heq : V.inter (semisimpleCommutatorPointCentralizer s) =
          U.inter (listPointCentralizer (s :: L)) := by
        apply SetLike.coe_injective
        ext x
        change ((x ∈ U.toSubgroup ∧ x ∈ listPointCentralizer L) ∧
            x ∈ semisimpleCommutatorPointCentralizer s) ↔
          (x ∈ U.toSubgroup ∧
            (x ∈ listPointCentralizer L ∧
              x ∈ semisimpleCommutatorPointCentralizer s))
        exact and_assoc
      rw [← heq]
      exact hstep

/-- The fixed subgroup of a connected unipotent subgroup under a normalizing
subtorus is connected. The acting torus may be external to the subgroup. -/
public theorem externalTorusFixed_isConnected
    {G : Variety k} [AlgebraicGroup G]
    (H S : ClosedSubgroup G)
    (hHc : Variety.IsConnected H.carrierVariety)
    (hHu : IsUnipotentAlgebraicGroup H.carrierVariety)
    (hS : IsSubtorus S) (hSN : S ≤ H.normalizer) :
    Variety.IsConnected (H.pointwiseCentralizer S).carrierVariety := by
  obtain ⟨L, hLS, hLC⟩ := exists_list_centralizer_le_centralizer S
  have hconn := inter_listPointCentralizer_isConnected H S hHc hHu hSN hS L hLS
  have heq : H.inter (listPointCentralizer L) = H.pointwiseCentralizer S := by
    apply SetLike.coe_injective
    ext x
    change (x ∈ H ∧ x ∈ listPointCentralizer L) ↔ (x ∈ H ∧ x ∈ S.centralizer)
    constructor
    · exact fun hx => ⟨hx.1, hLC hx.2⟩
    · rintro ⟨hxH, hxC⟩
      refine ⟨hxH, (mem_listPointCentralizer_iff L x).mpr ?_⟩
      intro s hs
      exact ((Subgroup.mem_centralizer_iff.mp hxC) s (hLS s hs)).symm
  rwa [heq] at hconn

/-- Connectedness in the ambient point topology, for use with identity
components and closed-subgroup generation. -/
public theorem externalTorusFixed_isConnected_set
    {G : Variety k} [AlgebraicGroup G]
    (H S : ClosedSubgroup G)
    (hHc : _root_.IsConnected (H : Set (Variety.Point G)))
    (hHu : IsUnipotentAlgebraicGroup H.carrierVariety)
    (hS : IsSubtorus S) (hSN : S ≤ H.normalizer) :
    _root_.IsConnected (H.pointwiseCentralizer S : Set (Variety.Point G)) :=
  isConnected_of_carrier_local _
    (externalTorusFixed_isConnected H S (carrier_isConnected_local H hHc) hHu hS hSN)

/-- Every subtorus of a normalizing torus has connected fixed subgroup in a
connected unipotent group. -/
public theorem subtorusFixed_isConnected
    {G : Variety k} [AlgebraicGroup G]
    (H T S : ClosedSubgroup G)
    (hHc : Variety.IsConnected H.carrierVariety)
    (hHu : IsUnipotentAlgebraicGroup H.carrierVariety)
    (hTN : T ≤ H.normalizer) (hS : IsSubtorus S) (hST : S ≤ T) :
    Variety.IsConnected (H.pointwiseCentralizer S).carrierVariety :=
  externalTorusFixed_isConnected H S hHc hHu hS (fun _ hx => hTN (hST hx))

end Theory.AlgebraicGroup.SemisimpleCenterContainment.RadicalGeometry.IntersectionNormality
