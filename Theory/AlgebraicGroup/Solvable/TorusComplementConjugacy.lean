module

public import Theory.AlgebraicGroup.Solvable.SemisimpleConjugacy
public import Theory.AlgebraicGroup.Solvable.TorusComplement
public import Theory.AlgebraicGroup.Tori.DiagonalizableClosedSubgroupSemisimple

/-!
# Diagonalizable subgroups and torus complements in connected solvable groups

For a connected solvable algebraic group, any maximal torus is conjugate to a
torus complement to its connected unipotent radical by a point of that
radical; in particular, any two torus complements are conjugate.  This is
the conjugacy assertion in Bor1, Chapter III, Theorem 10.6(4).

The proof replaces Bor1's generic element of the second torus by a finite list
whose centralizer is contained in the centralizer of the whole torus.  Such a
list exists by Noetherian minimality.  Its elements are successively
conjugated into the first complement, working at each stage in the full point
centralizer; the semisimple commutator fixed-subgroup theorem makes its
intersection with the connected unipotent radical connected.  The resulting
conjugate of the second torus centralizes the first.  Factoring one of its
points through the first torus and the unipotent radical then makes the
unipotent factor both semisimple and unipotent, hence trivial.  Maximality of a
torus complement gives equality.

The module sits directly above the semisimple-conjugacy and torus-complement
interfaces used by the argument.

The same finite-centralizer induction also proves Borel's Theorem 10.6(5): an
arbitrary diagonalizable closed subgroup is conjugate into a supplied torus
complement.  This subgroup need not be connected.  Accordingly, that argument
uses the full centralizer of the already treated finite list; Proposition
9.3(2) still makes its intersection with the unipotent radical connected.
Once the finite list detects the centralizer of the whole subgroup, the final
torus-unipotent factorization has a unipotent factor which is also semisimple,
and hence trivial by Jordan uniqueness.
-/

open Theory.AlgebraicGroup

universe u

namespace Theory.AlgebraicGroup

open scoped Pointwise

variable {k : Type u} [Field k] [IsAlgClosed k]

set_option linter.style.haveILetI false

omit [IsAlgClosed k] in
private lemma closedSubgroup_isConnected_of_carrier_local
    {G : Variety k} [AlgebraicGroup G] (H : ClosedSubgroup G)
    (hH : Variety.IsConnected H.carrierVariety) :
    _root_.IsConnected (H : Set (Variety.Point G)) := by
  let e := Variety.closedSubvarietyPointHomeomorph H.isZariskiClosed
  let : ConnectedSpace (Variety.Point H.carrierVariety) :=
    connectedSpace_iff_univ.mpr hH
  let : ConnectedSpace {x : Variety.Point G // x ∈ (H : Set (Variety.Point G))} :=
    e.connectedSpace_iff.mp inferInstance
  exact isConnected_iff_connectedSpace.mpr inferInstance

omit [IsAlgClosed k] in
private lemma closedSubgroup_carrier_isConnected_local
    {G : Variety k} [AlgebraicGroup G] (H : ClosedSubgroup G)
    (hH : _root_.IsConnected (H : Set (Variety.Point G))) :
    Variety.IsConnected H.carrierVariety := by
  let e := Variety.closedSubvarietyPointHomeomorph H.isZariskiClosed
  let : ConnectedSpace {x : Variety.Point G // x ∈ (H : Set (Variety.Point G))} :=
    Subtype.connectedSpace hH
  let : ConnectedSpace (Variety.Point H.carrierVariety) :=
    e.connectedSpace_iff.mpr inferInstance
  exact connectedSpace_iff_univ.mp inferInstance

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
      · rintro ⟨hL, hs⟩ y hy
        rcases List.mem_cons.mp hy with rfl | hy
        · exact (hs y (by simp)).symm
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
  have himage : f.imageClosedSubgroup =
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
  rw [← himage]
  exact closedSubgroup_carrier_isConnected_local f.imageClosedSubgroup
    (f.imageClosedSubgroup_isConnected hFconn)

omit [IsAlgClosed k] in
private lemma IsSubtorus.commute_ambient
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
  simpa [map_mul, hxval, hyval] using hamb

private lemma IsSubtorus.semisimple_ambient
    {G : Variety k} [AlgebraicGroup G] {S : ClosedSubgroup G}
    (hS : IsSubtorus S) {x : Variety.Point G} (hx : x ∈ S.toSubgroup) :
    IsSemisimpleElement G x := by
  let xS : Variety.Point S.carrierVariety := S.pointEquiv.symm ⟨x, hx⟩
  have hamb := morphism_preserves_semisimpleElement S.inclusion xS
    (hS.all_semisimple xS)
  have hxval : S.inclusion.onPoints xS = x := by
    change (S.pointEquiv xS).val = x
    simp [xS]
  rwa [hxval] at hamb

omit [IsAlgClosed k] in
private lemma IsDiagonalizableClosedSubgroup.commute_ambient
    {G : Variety k} [AlgebraicGroup G] {S : ClosedSubgroup G}
    (hS : IsDiagonalizableClosedSubgroup S) {x y : Variety.Point G}
    (hx : x ∈ S.toSubgroup) (hy : y ∈ S.toSubgroup) : x * y = y * x := by
  obtain ⟨n, D, ⟨e⟩⟩ := hS
  letI : AlgebraicGroup D.carrierVariety := D.carrierAlgebraicGroup
  let xS : Variety.Point S.carrierVariety := S.pointEquiv.symm ⟨x, hx⟩
  let yS : Variety.Point S.carrierVariety := S.pointEquiv.symm ⟨y, hy⟩
  have hdiag := dVariety_isMulCommutative (k := k) n
  rw [isMulCommutative_iff] at hdiag
  have hxyD : e.hom.onPoints xS * e.hom.onPoints yS =
      e.hom.onPoints yS * e.hom.onPoints xS := by
    apply D.inclusion_injective
    exact hdiag _ _
  have hxyS := congrArg e.inv.onPoints hxyD
  have hxyS' : xS * yS = yS * xS := by
    simpa only [map_mul, e.hom_inv_id] using hxyS
  have hxy := congrArg S.inclusion.onPoints hxyS'
  have hxval : S.inclusion.onPoints xS = x := by
    change (S.pointEquiv xS).val = x
    simp [xS]
  have hyval : S.inclusion.onPoints yS = y := by
    change (S.pointEquiv yS).val = y
    simp [yS]
  simpa only [map_mul, hxval, hyval] using hxy

private lemma IsDiagonalizableClosedSubgroup.semisimple_ambient
    {G : Variety k} [AlgebraicGroup G] {S : ClosedSubgroup G}
    (hS : IsDiagonalizableClosedSubgroup S) {x : Variety.Point G}
    (hx : x ∈ S.toSubgroup) : IsSemisimpleElement G x := by
  let xS : Variety.Point S.carrierVariety := S.pointEquiv.symm ⟨x, hx⟩
  have hamb := morphism_preserves_semisimpleElement S.inclusion xS
    (hS.all_semisimple xS)
  have hxval : S.inclusion.onPoints xS = x := by
    change (S.pointEquiv xS).val = x
    simp [xS]
  rwa [hxval] at hamb

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

private theorem inter_listPointCentralizer_isConnected
    {G : Variety k} [AlgebraicGroup G] (U S : ClosedSubgroup G)
    (hUconn : Variety.IsConnected U.carrierVariety)
    (hU : IsUnipotentAlgebraicGroup U.carrierVariety)
    (hUnormal : U.toSubgroup.Normal)
    (hS : IsDiagonalizableClosedSubgroup S)
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
        exact hS.commute_ambient hsS (hLS' z hz)
      letI : U.toSubgroup.Normal := hUnormal
      have hsNormU : s ∈ Subgroup.normalizer
          (U.toSubgroup : Set (Variety.Point G)) :=
        Subgroup.subset_normalizer_of_normal (Set.mem_univ s)
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
        (hS.semisimple_ambient hsS) hsNormV
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

omit [IsAlgClosed k] in
private noncomputable def closedSubgroupInside
    {G : Variety k} [AlgebraicGroup G]
    (K H : ClosedSubgroup G) (hKH : K ≤ H) :
    ClosedSubgroup H.carrierVariety := by
  let f : AlgebraicGroup.Morphism K.carrierVariety H.carrierVariety :=
    K.inclusion.codRestrictClosedSubgroup H
      (fun x ↦ hKH (K.pointEquiv x).property)
  exact f.imageClosedSubgroup

private theorem mem_closedSubgroupInside_iff
    {G : Variety k} [AlgebraicGroup G]
    (K H : ClosedSubgroup G) (hKH : K ≤ H)
    (x : Variety.Point H.carrierVariety) :
    letI : AlgebraicGroup H.carrierVariety := H.carrierAlgebraicGroup
    x ∈ closedSubgroupInside K H hKH ↔ H.includePoint x ∈ K := by
  letI : AlgebraicGroup H.carrierVariety := H.carrierAlgebraicGroup
  let f : AlgebraicGroup.Morphism K.carrierVariety H.carrierVariety :=
    K.inclusion.codRestrictClosedSubgroup H
      (fun y ↦ hKH (K.pointEquiv y).property)
  have hf (y : Variety.Point K.carrierVariety) :
      H.inclusion.onPoints (f.onPoints y) = K.inclusion.onPoints y :=
    K.inclusion.codRestrictClosedSubgroup_inclusion_apply H
      (fun z ↦ hKH (K.pointEquiv z).property) y
  change (∃ y, f.onPoints y = x) ↔ H.includePoint x ∈ K
  constructor
  · rintro ⟨y, rfl⟩
    change H.inclusion.onPoints (f.onPoints y) ∈ K
    rw [hf]
    exact (K.pointEquiv y).property
  · intro hx
    let y : Variety.Point K.carrierVariety :=
      K.pointEquiv.symm ⟨H.includePoint x, hx⟩
    refine ⟨y, H.inclusion_injective ?_⟩
    rw [hf]
    exact congrArg Subtype.val
      (K.pointEquiv.apply_symm_apply ⟨H.includePoint x, hx⟩)

private theorem closedSubgroupInside_isSubtorus
    {G : Variety k} [AlgebraicGroup G]
    (T H : ClosedSubgroup G) (hTH : T ≤ H) (hT : IsSubtorus T) :
    letI : AlgebraicGroup H.carrierVariety := H.carrierAlgebraicGroup
    IsSubtorus (closedSubgroupInside T H hTH) := by
  letI : AlgebraicGroup H.carrierVariety := H.carrierAlgebraicGroup
  let f : AlgebraicGroup.Morphism T.carrierVariety H.carrierVariety :=
    T.inclusion.codRestrictClosedSubgroup H
      (fun y ↦ hTH (T.pointEquiv y).property)
  change IsSubtorus f.imageClosedSubgroup
  exact morphism_image_isTorus f hT

private theorem semisimpleElement_conjugate_inside_connected_subgroup
    {G : Variety k} [AlgebraicGroup G] (T U H : ClosedSubgroup G)
    (hT : IsSubtorus T)
    (hU : IsUnipotentAlgebraicGroup U.carrierVariety)
    (hUnormal : U.toSubgroup.Normal)
    (hfactor : ∀ x : Variety.Point G, ∃ t u,
      t ∈ T.toSubgroup ∧ u ∈ U.toSubgroup ∧ x = t * u)
    (hTH : T ≤ H)
    (hUHconn : Variety.IsConnected
      (U.inter H).carrierVariety)
    (s : Variety.Point G) (hsH : s ∈ H.toSubgroup)
    (hsSemi : IsSemisimpleElement G s) :
    ∃ u : Variety.Point G,
      u ∈ U.toSubgroup ∧ u ∈ H.toSubgroup ∧
        u⁻¹ * s * u ∈ T.toSubgroup := by
  letI : AlgebraicGroup H.carrierVariety := H.carrierAlgebraicGroup
  let V : ClosedSubgroup G := U.inter H
  have hVH : V ≤ H := by
    intro x hx
    exact hx.2
  have hVU : V ≤ U := by
    intro x hx
    exact hx.1
  let TI : ClosedSubgroup H.carrierVariety := closedSubgroupInside T H hTH
  let VI : ClosedSubgroup H.carrierVariety := closedSubgroupInside V H hVH
  letI : AlgebraicGroup TI.carrierVariety := TI.carrierAlgebraicGroup
  letI : AlgebraicGroup VI.carrierVariety := VI.carrierAlgebraicGroup
  have hTI : IsSubtorus TI := closedSubgroupInside_isSubtorus T H hTH hT
  let fV : AlgebraicGroup.Morphism V.carrierVariety H.carrierVariety :=
    V.inclusion.codRestrictClosedSubgroup H
      (fun y ↦ hVH (V.pointEquiv y).property)
  have hfVmem (v : Variety.Point V.carrierVariety) :
      fV.onPoints v ∈ VI.toSubgroup := ⟨v, rfl⟩
  let pV : AlgebraicGroup.Morphism V.carrierVariety VI.carrierVariety :=
    fV.codRestrictClosedSubgroup VI hfVmem
  have hpVsurj : Function.Surjective pV.onPoints :=
    fV.codRestrictImageClosedSubgroup_surjective hfVmem
  have hVIconn : Variety.IsConnected VI.carrierVariety :=
    closedSubgroup_carrier_isConnected_local VI
      (fV.imageClosedSubgroup_isConnected hUHconn)
  have hVuni : IsUnipotentAlgebraicGroup V.carrierVariety :=
    isUnipotentAlgebraicGroup_of_le V U hVU hU
  have hVIuni : IsUnipotentAlgebraicGroup VI.carrierVariety :=
    hVuni.of_surjective pV hpVsurj
  have hVInormal : VI.toSubgroup.Normal := by
    refine ⟨?_⟩
    intro x hx g
    have hxV : H.includePoint x ∈ V.toSubgroup :=
      (mem_closedSubgroupInside_iff V H hVH x).mp hx
    have hxU : H.includePoint x ∈ U.toSubgroup := hxV.1
    have hxH : H.includePoint x ∈ H.toSubgroup := (H.pointEquiv x).property
    have hgH : H.includePoint g ∈ H.toSubgroup := (H.pointEquiv g).property
    apply (mem_closedSubgroupInside_iff V H hVH _).mpr
    change H.inclusion.onPoints (g * x * g⁻¹) ∈ V
    rw [map_mul, map_inv, map_mul]
    refine ⟨hUnormal.conj_mem _ hxU _, ?_⟩
    exact H.toSubgroup.mul_mem
      (H.toSubgroup.mul_mem hgH hxH) (H.toSubgroup.inv_mem hgH)
  have hfactorH : ∀ x : Variety.Point H.carrierVariety, ∃ t u,
      t ∈ TI.toSubgroup ∧ u ∈ VI.toSubgroup ∧ x = t * u := by
    intro x
    obtain ⟨t, u, ht, hu, htu⟩ := hfactor (H.includePoint x)
    have htH : t ∈ H.toSubgroup := hTH ht
    have huEq : u = t⁻¹ * H.includePoint x := by
      rw [htu]
      group
    have huH : u ∈ H.toSubgroup := by
      rw [huEq]
      exact H.toSubgroup.mul_mem (H.toSubgroup.inv_mem htH)
        (H.pointEquiv x).property
    have huV : u ∈ V.toSubgroup := ⟨hu, huH⟩
    let tH : Variety.Point H.carrierVariety := H.pointEquiv.symm ⟨t, htH⟩
    let uH : Variety.Point H.carrierVariety := H.pointEquiv.symm ⟨u, huH⟩
    have htHval : H.includePoint tH = t := by
      change (H.pointEquiv tH).val = t
      simp [tH]
    have huHval : H.includePoint uH = u := by
      change (H.pointEquiv uH).val = u
      simp [uH]
    refine ⟨tH, uH,
      (mem_closedSubgroupInside_iff T H hTH tH).mpr (by simpa [htHval]),
      (mem_closedSubgroupInside_iff V H hVH uH).mpr (by simpa [huHval]), ?_⟩
    apply H.inclusion_injective
    change H.includePoint x = H.includePoint tH * H.includePoint uH
    rw [htHval, huHval, ← htu]
  let sH : Variety.Point H.carrierVariety := H.pointEquiv.symm ⟨s, hsH⟩
  have hsHval : H.includePoint sH = s := by
    change (H.pointEquiv sH).val = s
    simp [sH]
  have hsSemiH : IsSemisimpleElement H.carrierVariety sH := by
    have h := (closedSubgroup_semisimpleElement_iff H hsH).mp hsSemi
    simpa [sH] using h
  obtain ⟨uH, huHVI, huHsTI⟩ :=
    semisimpleElement_conjugate_into_subtorus_of_unipotent_factorization
      TI VI hTI hVIconn hVIuni hVInormal hfactorH sH hsSemiH
  let u := H.includePoint uH
  have huV : H.includePoint uH ∈ V.toSubgroup :=
    (mem_closedSubgroupInside_iff V H hVH uH).mp huHVI
  refine ⟨u, huV.1, (H.pointEquiv uH).property, ?_⟩
  have husT := (mem_closedSubgroupInside_iff T H hTH
    (uH⁻¹ * sH * uH)).mp huHsTI
  change H.inclusion.onPoints (uH⁻¹ * sH * uH) ∈ T at husT
  simp only [map_mul, map_inv] at husT
  have hsHval' : H.inclusion.onPoints sH = s := hsHval
  rw [hsHval'] at husT
  change (H.inclusion.onPoints uH)⁻¹ * s * H.inclusion.onPoints uH ∈ T
  exact husT

omit [IsAlgClosed k] in
private theorem conjugate_isSubtorus
    {G : Variety k} [AlgebraicGroup G] (S : ClosedSubgroup G)
    (hS : IsSubtorus S) (g : Variety.Point G) :
    IsSubtorus (S.conjugate g) := by
  rcases hS with ⟨n, ⟨e⟩⟩
  exact ⟨n, ⟨(S.conjugateIso g).comp e⟩⟩

omit [IsAlgClosed k] in
private theorem conjugate_isDiagonalizableClosedSubgroup
    {G : Variety k} [AlgebraicGroup G] (S : ClosedSubgroup G)
    (hS : IsDiagonalizableClosedSubgroup S) (g : Variety.Point G) :
    IsDiagonalizableClosedSubgroup (S.conjugate g) := by
  rcases hS with ⟨n, D, ⟨e⟩⟩
  letI : AlgebraicGroup D.carrierVariety := D.carrierAlgebraicGroup
  exact ⟨n, D, ⟨e.comp (S.conjugateIso g).symm⟩⟩

omit [IsAlgClosed k] in
private noncomputable def topClosedSubgroupIso_local
    (G : Variety k) [AlgebraicGroup G] :
    AlgebraicGroup.Iso G
      (ClosedSubgroup.top (G := G)).carrierVariety := by
  let T : ClosedSubgroup G := ClosedSubgroup.top
  let toTop : AlgebraicGroup.Morphism G T.carrierVariety :=
    (AlgebraicGroup.Morphism.id G).codRestrictClosedSubgroup T
      (fun _ => trivial)
  exact
    { hom := toTop
      inv := T.inclusion
      hom_inv_id := by intro x; rfl
      inv_hom_id := by
        intro y
        apply T.inclusion_injective
        rfl }

omit [IsAlgClosed k] in
private lemma isDiagonalizableClosedSubgroup_of_isSubtorus
    {G : Variety k} [AlgebraicGroup G]
    {S : ClosedSubgroup G} (hS : IsSubtorus S) :
    IsDiagonalizableClosedSubgroup S := by
  rcases hS with ⟨n, ⟨e⟩⟩
  let D : ClosedSubgroup (dVariety k n) := ClosedSubgroup.top
  letI : AlgebraicGroup D.carrierVariety := D.carrierAlgebraicGroup
  exact ⟨n, D, ⟨(topClosedSubgroupIso_local (dVariety k n)).comp e.symm⟩⟩

omit [IsAlgClosed k] in
private lemma conjugated_point_mem_conjugate
    {G : Variety k} [AlgebraicGroup G] (S : ClosedSubgroup G)
    (g x : Variety.Point G) (hx : x ∈ S.toSubgroup) :
    g * x * g⁻¹ ∈ (S.conjugate g).toSubgroup := by
  change g * x * g⁻¹ ∈ S.conjugate g
  rw [S.mem_conjugate_iff]
  have heq : g⁻¹ * (g * x * g⁻¹) * g = x := by group
  rwa [heq]

private theorem exists_list_conjugator_into_subtorus
    {G : Variety k} [AlgebraicGroup G]
    (T U S : ClosedSubgroup G)
    (hT : IsSubtorus T)
    (hUconn : Variety.IsConnected U.carrierVariety)
    (hU : IsUnipotentAlgebraicGroup U.carrierVariety)
    (hUnormal : U.toSubgroup.Normal)
    (hfactor : ∀ x : Variety.Point G, ∃ t u,
      t ∈ T.toSubgroup ∧ u ∈ U.toSubgroup ∧ x = t * u)
    (hS : IsDiagonalizableClosedSubgroup S)
    (L : List (Variety.Point G))
    (hLS : ∀ s ∈ L, s ∈ S.toSubgroup) :
    ∃ u : Variety.Point G, u ∈ U.toSubgroup ∧
      ∀ s ∈ L, u⁻¹ * s * u ∈ T.toSubgroup := by
  induction L with
  | nil =>
      refine ⟨1, U.toSubgroup.one_mem, ?_⟩
      intro s hs
      exact (List.not_mem_nil hs).elim
  | cons s L ih =>
      have hsS : s ∈ S.toSubgroup := hLS s (by simp)
      have hLS' : ∀ z ∈ L, z ∈ S.toSubgroup := by
        intro z hz
        exact hLS z (List.mem_cons_of_mem s hz)
      obtain ⟨u, huU, huL⟩ := ih hLS'
      let c : Variety.Point G → Variety.Point G := fun z ↦ u⁻¹ * z * u
      let N : List (Variety.Point G) := L.map c
      let S' : ClosedSubgroup G := S.conjugate u⁻¹
      have hS' : IsDiagonalizableClosedSubgroup S' :=
        conjugate_isDiagonalizableClosedSubgroup S hS u⁻¹
      have hcMem (z : Variety.Point G) (hz : z ∈ S.toSubgroup) :
          c z ∈ S'.toSubgroup := by
        simpa [c, S'] using conjugated_point_mem_conjugate S u⁻¹ z hz
      have hNS' : ∀ z ∈ N, z ∈ S'.toSubgroup := by
        intro z hz
        rcases List.mem_map.mp hz with ⟨y, hy, rfl⟩
        exact hcMem y (hLS' y hy)
      let C : ClosedSubgroup G := listPointCentralizer N
      have hTC : T ≤ C := by
        intro t ht
        change t ∈ listPointCentralizer N
        rw [mem_listPointCentralizer_iff]
        intro z hz
        rcases List.mem_map.mp hz with ⟨y, hy, rfl⟩
        exact hT.commute_ambient ht (huL y hy)
      have hS'C : S' ≤ C := by
        intro x hx
        change x ∈ listPointCentralizer N
        rw [mem_listPointCentralizer_iff]
        intro z hz
        exact hS'.commute_ambient hx (hNS' z hz)
      have hcsC : c s ∈ C.toSubgroup := hS'C (hcMem s hsS)
      have hUCconn : Variety.IsConnected (U.inter C).carrierVariety :=
        inter_listPointCentralizer_isConnected U S' hUconn hU hUnormal
          hS' N hNS'
      obtain ⟨v, hvU, hvC, hvHead⟩ :=
        semisimpleElement_conjugate_inside_connected_subgroup T U C hT hU
          hUnormal hfactor hTC hUCconn (c s) hcsC
          (hS'.semisimple_ambient (hcMem s hsS))
      refine ⟨u * v, U.toSubgroup.mul_mem huU hvU, ?_⟩
      intro z hz
      rcases List.mem_cons.mp hz with rfl | hz
      · simpa [c, mul_assoc] using hvHead
      · have hvComm : v * c z = c z * v :=
          (mem_listPointCentralizer_iff N v).mp hvC (c z)
            (List.mem_map.mpr ⟨z, hz, rfl⟩)
        have heq : (u * v)⁻¹ * z * (u * v) = c z := by
          calc
            (u * v)⁻¹ * z * (u * v) = v⁻¹ * c z * v := by
              simp only [mul_inv_rev, c]
              group
            _ = c z := by
              rw [show v⁻¹ * c z = c z * v⁻¹ from
                (show Commute v (c z) from hvComm).inv_left.eq]
              group
        rw [heq]
        exact huL z hz

omit [IsAlgClosed k] in
private theorem conjugate_isMaximalTorus
    {G : Variety k} [AlgebraicGroup G] (S : ClosedSubgroup G)
    (hS : IsMaximalTorus S) (g : Variety.Point G) :
    IsMaximalTorus (S.conjugate g) := by
  refine ⟨conjugate_isSubtorus S hS.1 g, ?_⟩
  intro R hR hle
  have hSR : S ≤ R.conjugate g⁻¹ := by
    intro x hx
    change x ∈ R.conjugate g⁻¹
    rw [R.mem_conjugate_iff]
    have hmem := hle (conjugated_point_mem_conjugate S g x hx)
    change g * x * g⁻¹ ∈ R.toSubgroup at hmem
    simpa only [inv_inv] using hmem
  have heq : R.conjugate g⁻¹ = S := hS.2 _
    (conjugate_isSubtorus R hR g⁻¹) hSR
  have heq' := congrArg (fun K : ClosedSubgroup G ↦ K.conjugate g) heq
  rw [ClosedSubgroup.conjugate_conjugate, mul_inv_cancel,
    ClosedSubgroup.conjugate_one] at heq'
  exact heq'

omit [IsAlgClosed k] in
private lemma mem_invtSubmodule_iff_of_inverse_local
    {M : Type*} [AddCommGroup M] [Module k M]
    {T S : Module.End k M} (hTS : T.comp S = 1) (hST : S.comp T = 1)
    (P : Submodule k M) [Module.Finite k P] :
    P ∈ T.invtSubmodule ↔ P ∈ S.invtSubmodule := by
  have forward {A B : Module.End k M} (hBA : B.comp A = 1)
      (hPA : P ∈ A.invtSubmodule) : P ∈ B.invtSubmodule := by
    let AP : Module.End k P := A.restrict hPA
    have hAinj : Function.Injective A := by
      intro x y hxy
      calc
        x = B (A x) := by
          have hx := LinearMap.congr_fun hBA x
          simpa using hx.symm
        _ = B (A y) := congrArg B hxy
        _ = y := by
          have hy := LinearMap.congr_fun hBA y
          simpa using hy
    have hAPinj : Function.Injective AP := by
      intro x y hxy
      apply Subtype.ext
      apply hAinj
      exact congrArg Subtype.val hxy
    have hAPsurj : Function.Surjective AP :=
      LinearMap.surjective_of_injective hAPinj
    intro x hx
    rcases hAPsurj ⟨x, hx⟩ with ⟨y, hy⟩
    have hAy : A y.1 = x := congrArg Subtype.val hy
    have hBx : B x = y.1 := by
      calc
        B x = B (A y.1) := by rw [hAy]
        _ = y.1 := by
          have hy' := LinearMap.congr_fun hBA y.1
          simpa using hy'
    change B x ∈ P
    rw [hBx]
    exact y.2
  exact ⟨forward hST, forward hTS⟩

omit [IsAlgClosed k] in
private lemma finitelySemisimple_of_inverse_local
    {M : Type*} [AddCommGroup M] [Module k M]
    {T S : Module.End k M} (hT : T.IsFinitelySemisimple)
    (hTS : T.comp S = 1) (hST : S.comp T = 1) :
    S.IsFinitelySemisimple := by
  intro P hPS hPfinite
  let : Module.Finite k P := hPfinite
  have hPT : P ∈ T.invtSubmodule :=
    (mem_invtSubmodule_iff_of_inverse_local hTS hST P).mpr hPS
  let TP : Module.End k P := T.restrict hPT
  let SP : Module.End k P := S.restrict hPS
  have hTPSP : TP.comp SP = 1 := by
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    exact LinearMap.congr_fun hTS x.1
  have hSPTP : SP.comp TP = 1 := by
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    exact LinearMap.congr_fun hST x.1
  have hinv : ∀ Q : Submodule k P,
      Q ∈ TP.invtSubmodule ↔ Q ∈ SP.invtSubmodule :=
    fun Q ↦ mem_invtSubmodule_iff_of_inverse_local hTPSP hSPTP Q
  have hTPsem : TP.IsSemisimple := hT P hPT hPfinite
  rw [Module.End.isSemisimple_iff] at hTPsem ⊢
  intro Q hQS
  obtain ⟨R, hRT, hcompl⟩ := hTPsem Q ((hinv Q).mpr hQS)
  exact ⟨R, (hinv R).mp hRT, hcompl⟩

omit [IsAlgClosed k] in
private lemma semisimpleElement_inv_local
    {G : Variety k} [AlgebraicGroup G] {x : Variety.Point G}
    (hx : IsSemisimpleElement G x) : IsSemisimpleElement G x⁻¹ := by
  change Module.End.IsFinitelySemisimple (rightTranslationPullback G x⁻¹)
  apply finitelySemisimple_of_inverse_local
    (T := rightTranslationPullback G x)
    (S := rightTranslationPullback G x⁻¹)
  · exact hx
  · exact rightTranslationPullback_comp_inv G x
  · exact rightTranslationPullback_inv_comp G x

private lemma semisimpleElement_mul_of_commute_local
    {G : Variety k} [AlgebraicGroup G] {x y : Variety.Point G}
    (hx : IsSemisimpleElement G x) (hy : IsSemisimpleElement G y)
    (hxy : Commute x y) : IsSemisimpleElement G (x * y) := by
  have hTU : Commute (rightTranslationPullback G x)
      (rightTranslationPullback G y) := by
    change (rightTranslationPullback G x).comp (rightTranslationPullback G y) =
      (rightTranslationPullback G y).comp (rightTranslationPullback G x)
    rw [← rightTranslationPullback_mul, ← rightTranslationPullback_mul]
    exact congrArg (rightTranslationPullback G) hxy.eq
  rw [IsSemisimpleElement, rightTranslationPullback_mul]
  exact Module.End.IsFinitelySemisimple.mul_of_commute
    (rightTranslationPullback_locallyFinite G x)
    (rightTranslationPullback_locallyFinite G y) hx hy hTU

/-- Every diagonalizable closed subgroup of a connected solvable algebraic
group is conjugate into a supplied torus complement by a point of the
connected unipotent radical.  No connectedness is assumed of the
diagonalizable subgroup. -/
public theorem diagonalizableClosedSubgroup_conjugate_into_torusComplement
    {G : Variety k} [AlgebraicGroup G]
    (hsolvable : Group.IsSolvable (Variety.Point G))
    (hconnected : Variety.IsConnected G)
    (U T S : ClosedSubgroup G)
    (hUrad : IsUnipotentRadicalSubgroup U)
    (hT : IsTorusComplement T U)
    (hS : IsDiagonalizableClosedSubgroup S) :
    ∃ u : Variety.Point G, u ∈ U.toSubgroup ∧
      IsSubtorus (T.conjugate u) ∧ S ≤ T.conjugate u := by
  have hUconn :=
    hUrad.isConnected_of_solvable_connected hsolvable hconnected
  have hU :=
    hUrad.isUnipotent_of_solvable_connected hsolvable hconnected
  have hUnormal :=
    hUrad.normal_of_solvable_connected hsolvable hconnected
  obtain ⟨L, hLS, hLcentral⟩ :=
    exists_list_centralizer_le_centralizer S
  obtain ⟨u, huU, huL⟩ :=
    exists_list_conjugator_into_subtorus
      T U S hT.1 hUconn hU hUnormal hT.2.1 hS L hLS
  let S' : ClosedSubgroup G := S.conjugate u⁻¹
  have hS' : IsDiagonalizableClosedSubgroup S' :=
    conjugate_isDiagonalizableClosedSubgroup S hS u⁻¹
  have hbackTC : T.conjugate u ≤ listPointCentralizer L := by
    intro x hx
    change x ∈ listPointCentralizer L
    rw [mem_listPointCentralizer_iff]
    intro z hz
    have hxT : u⁻¹ * x * u ∈ T.toSubgroup :=
      (T.mem_conjugate_iff u x).mp hx
    have hzT : u⁻¹ * z * u ∈ T.toSubgroup := huL z hz
    have hcomm := hT.1.commute_ambient hxT hzT
    have hamb := congrArg (fun y : Variety.Point G ↦ u * y * u⁻¹) hcomm
    simpa only [mul_assoc] using (show x * z = z * x by
      convert hamb using 1 <;> group)
  have hTcentralS' : T ≤ S'.centralizer := by
    intro t ht
    change t ∈ Subgroup.centralizer (S'.toSubgroup : Set (Variety.Point G))
    rw [Subgroup.mem_centralizer_iff]
    intro y hyS'
    have htBack : u * t * u⁻¹ ∈ T.conjugate u :=
      conjugated_point_mem_conjugate T u t ht
    have htCentral : u * t * u⁻¹ ∈ S.centralizer :=
      hLcentral (hbackTC htBack)
    have hyBack : u * y * u⁻¹ ∈ S.toSubgroup := by
      have hy := (S.mem_conjugate_iff u⁻¹ y).mp hyS'
      simpa only [inv_inv] using hy
    have hcomm := (Subgroup.mem_centralizer_iff.mp htCentral)
      (u * y * u⁻¹) hyBack
    have hamb := congrArg (fun z : Variety.Point G ↦ u⁻¹ * z * u) hcomm
    convert hamb using 1 <;> group
  refine ⟨u, huU, conjugate_isSubtorus T hT.1 u, ?_⟩
  intro x hxS
  apply (T.mem_conjugate_iff u x).mpr
  have hxS' : u⁻¹ * x * u ∈ S'.toSubgroup := by
    simpa [S'] using conjugated_point_mem_conjugate S u⁻¹ x hxS
  obtain ⟨t, v, htT, hvU, hxtv⟩ := hT.2.1 (u⁻¹ * x * u)
  have hxSemi : IsSemisimpleElement G (u⁻¹ * x * u) :=
    hS'.semisimple_ambient hxS'
  have htSemi : IsSemisimpleElement G t := hT.1.semisimple_ambient htT
  have hxt : (u⁻¹ * x * u) * t = t * (u⁻¹ * x * u) :=
    (Subgroup.mem_centralizer_iff.mp (hTcentralS' htT)) _ hxS'
  have hvEq : v = t⁻¹ * (u⁻¹ * x * u) := by
    rw [hxtv]
    group
  have hvSemi : IsSemisimpleElement G v := by
    rw [hvEq]
    exact semisimpleElement_mul_of_commute_local
      (semisimpleElement_inv_local htSemi) hxSemi
      (show Commute t⁻¹ (u⁻¹ * x * u) from
        (show Commute t (u⁻¹ * x * u) from hxt.symm).inv_left)
  let vU : Variety.Point U.carrierVariety := U.pointEquiv.symm ⟨v, hvU⟩
  have hvUniAmbient := morphism_preserves_unipotentElement U.inclusion vU
    (hU vU)
  have hvUval : U.inclusion.onPoints vU = v := by
    change (U.pointEquiv vU).val = v
    simp [vU]
  rw [hvUval] at hvUniAmbient
  have hvOne := semisimple_unipotent_eq_one v hvSemi hvUniAmbient
  rw [hxtv, hvOne, mul_one]
  exact htT

/-- A maximal torus and a torus complement to the connected unipotent radical
of a connected solvable algebraic group are conjugate by a point of that
radical. -/
public theorem maximalTorus_conjugate_to_torusComplement_by_unipotentRadical
    {G : Variety k} [AlgebraicGroup G]
    (hsolvable : Group.IsSolvable (Variety.Point G))
    (hconnected : Variety.IsConnected G)
    (U T₁ T₂ : ClosedSubgroup G)
    (hUrad : IsUnipotentRadicalSubgroup U)
    (hT₁ : IsTorusComplement T₁ U)
    (hT₂ : IsMaximalTorus T₂) :
    ∃ u : Variety.Point G, u ∈ U.toSubgroup ∧
      T₂.conjugate u = T₁ := by
  obtain ⟨u, huU, huT₂⟩ :=
    diagonalizableClosedSubgroup_conjugate_into_torusComplement
      hsolvable hconnected U T₁ T₂ hUrad hT₁
        (isDiagonalizableClosedSubgroup_of_isSubtorus hT₂.1)
  rcases huT₂ with ⟨hT₁u, hT₂le⟩
  have heq : T₁.conjugate u = T₂ := hT₂.2 _ hT₁u hT₂le
  have heq' := congrArg
    (fun K : ClosedSubgroup G ↦ K.conjugate u⁻¹) heq
  rw [ClosedSubgroup.conjugate_conjugate, inv_mul_cancel,
    ClosedSubgroup.conjugate_one] at heq'
  refine ⟨u⁻¹, U.toSubgroup.inv_mem huU, ?_⟩
  exact heq'.symm

/-- Any two torus complements to the connected unipotent radical of a
connected solvable algebraic group are conjugate by a point of that radical. -/
public theorem torusComplements_conjugate_by_unipotentRadical
    {G : Variety k} [AlgebraicGroup G]
    (hsolvable : Group.IsSolvable (Variety.Point G))
    (hconnected : Variety.IsConnected G)
    (U T₁ T₂ : ClosedSubgroup G)
    (hUrad : IsUnipotentRadicalSubgroup U)
    (hT₁ : IsTorusComplement T₁ U)
    (hT₂ : IsTorusComplement T₂ U) :
    ∃ u : Variety.Point G, u ∈ U.toSubgroup ∧
      T₂.conjugate u = T₁ := by
  exact maximalTorus_conjugate_to_torusComplement_by_unipotentRadical
    hsolvable hconnected U T₁ T₂ hUrad hT₁
      (hT₂.isMaximalTorus_of_unipotent
        (hUrad.isUnipotent_of_solvable_connected hsolvable hconnected))

end Theory.AlgebraicGroup
