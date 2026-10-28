module

public import Theory.AlgebraicGroup.Solvable.TriangularDiagonalizableSplitting

/-!
# Connected centralizers of subtori in connected solvable groups

For a connected solvable algebraic group, the centralizer of a subtorus is
connected.  A supplied torus complement contains a conjugate of the subtorus;
a finite list of its points detects the full centralizer, and induction using
connected fixed subgroups in the unipotent radical makes the corresponding
intersection connected.  The torus/unipotent factorization then identifies
the centralizer with the product of the torus and this connected intersection.
Finally, conjugation transports connectedness back from the conjugated
subtorus.  This is the triangular proof of Bor1, Chapter III, Theorem
10.6(5)(ii), using only the diagonalizable splitting and fixed-unipotent
interfaces proved below it.
-/

open Theory.AlgebraicGroup

universe u

namespace Theory.AlgebraicGroup

open scoped Pointwise

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
    (hUnormal : U.toSubgroup.Normal)
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
private lemma isDiagonalizableClosedSubgroup_of_isSubtorus_local
    {G : Variety k} [AlgebraicGroup G]
    {S : ClosedSubgroup G} (hS : IsSubtorus S) :
    IsDiagonalizableClosedSubgroup S := by
  rcases hS with ⟨n, ⟨e⟩⟩
  let D : ClosedSubgroup (dVariety k n) := ClosedSubgroup.top
  letI : AlgebraicGroup D.carrierVariety := D.carrierAlgebraicGroup
  exact ⟨n, D, ⟨(topClosedSubgroupIso_local (dVariety k n)).comp e.symm⟩⟩

omit [IsAlgClosed k] in
private lemma closedSubgroup_conjugate_isConnected_local
    {G : Variety k} [AlgebraicGroup G] (X : ClosedSubgroup G)
    (g : Variety.Point G)
    (hX : _root_.IsConnected (X : Set (Variety.Point G))) :
    _root_.IsConnected (X.conjugate g : Set (Variety.Point G)) := by
  apply isConnected_of_carrier_local
  exact (algebraicGroupIso_isConnected_iff (X.conjugateIso g)).mp
    (carrier_isConnected_local X hX)

omit [IsAlgClosed k] in
private lemma centralizer_conjugate_eq
    {G : Variety k} [AlgebraicGroup G]
    (S : ClosedSubgroup G) (g : Variety.Point G) :
    (S.conjugate g).centralizer = S.centralizer.conjugate g := by
  apply SetLike.coe_injective
  ext x
  constructor
  · intro hx
    change x ∈ S.centralizer.conjugate g
    rw [S.centralizer.mem_conjugate_iff]
    change x ∈ Subgroup.centralizer ((S.conjugate g).toSubgroup : Set (Variety.Point G)) at hx
    change g⁻¹ * x * g ∈ Subgroup.centralizer (S.toSubgroup : Set (Variety.Point G))
    rw [Subgroup.mem_centralizer_iff] at hx ⊢
    intro y hy
    have hy' : g * y * g⁻¹ ∈ (S.conjugate g).toSubgroup := by
      change g * y * g⁻¹ ∈ S.conjugate g
      apply (S.mem_conjugate_iff g _).mpr
      have hcancel : g⁻¹ * (g * y * g⁻¹) * g = y := by group
      rw [hcancel]
      change y ∈ S.toSubgroup at hy
      exact hy
    have hcomm := hx (g * y * g⁻¹) hy'
    have h := congrArg (fun z : Variety.Point G => g⁻¹ * z * g) hcomm
    convert h using 1 <;> group
  · intro hx
    change x ∈ S.centralizer.conjugate g at hx
    rw [S.centralizer.mem_conjugate_iff] at hx
    change g⁻¹ * x * g ∈ Subgroup.centralizer (S.toSubgroup : Set (Variety.Point G)) at hx
    change x ∈ Subgroup.centralizer ((S.conjugate g).toSubgroup : Set (Variety.Point G))
    rw [Subgroup.mem_centralizer_iff] at hx ⊢
    intro y hy
    have hy' : g⁻¹ * y * g ∈ S.toSubgroup :=
      (S.mem_conjugate_iff g y).mp hy
    have hcomm := hx (g⁻¹ * y * g) hy'
    have h := congrArg (fun z : Variety.Point G => g * z * g⁻¹) hcomm
    convert h using 1 <;> group

private theorem centralizer_isConnected_of_le_torus
    {G : Variety k} [AlgebraicGroup G]
    (U T S : ClosedSubgroup G)
    (hUconn : Variety.IsConnected U.carrierVariety)
    (hU : IsUnipotentAlgebraicGroup U.carrierVariety)
    (hUnormal : U.toSubgroup.Normal)
    (hT : IsTorusComplement T U)
    (hS : IsSubtorus S) (hST : S ≤ T) :
    Variety.IsConnected S.centralizer.carrierVariety := by
  obtain ⟨L, hLS, hLcentral⟩ := exists_list_centralizer_le_centralizer S
  let V : ClosedSubgroup G := U.inter (listPointCentralizer L)
  have hVconn : Variety.IsConnected V.carrierVariety :=
    inter_listPointCentralizer_isConnected U S hUconn hU hUnormal hS L hLS
  have hVleC : V ≤ S.centralizer := by
    intro x hx
    exact hLcentral hx.2
  have hprod_eq :
      (T.toSubgroup : Set (Variety.Point G)) *
          (V.toSubgroup : Set (Variety.Point G)) =
        (S.centralizer.toSubgroup : Set (Variety.Point G)) := by
    ext x
    constructor
    · rintro hx
      obtain ⟨t, ht, v, hv, rfl⟩ := Set.mem_mul.mp hx
      have htC : t ∈ S.centralizer := by
        change t ∈ Subgroup.centralizer (S.toSubgroup : Set (Variety.Point G))
        rw [Subgroup.mem_centralizer_iff]
        intro s hs
        exact subtorus_commute_ambient hT.1 (hST hs) ht
      have hvC : v ∈ S.centralizer := hVleC hv
      exact S.centralizer.toSubgroup.mul_mem htC hvC
    · intro hx
      obtain ⟨t, v, ht, hv, hxtv⟩ := hT.2.1 x
      have htC : t ∈ S.centralizer := by
        change t ∈ Subgroup.centralizer (S.toSubgroup : Set (Variety.Point G))
        rw [Subgroup.mem_centralizer_iff]
        intro s hs
        exact subtorus_commute_ambient hT.1 (hST hs) ht
      have hxC : x ∈ Subgroup.centralizer (S.toSubgroup : Set (Variety.Point G)) := hx
      have hvL : v ∈ listPointCentralizer L := by
        rw [mem_listPointCentralizer_iff]
        intro s hs
        have hsS : s ∈ S.toSubgroup := hLS s hs
        have hsC : x ∈ Subgroup.centralizer (S.toSubgroup : Set (Variety.Point G)) := hx
        have hcommx := (Subgroup.mem_centralizer_iff.mp hsC) s hsS
        have hcommt : t * s = s * t :=
          subtorus_commute_ambient hT.1 ht (hST hsS)
        have hcommv : v * s = s * v := by
          rw [hxtv] at hcommx
          calc
            v * s = t⁻¹ * (t * v * s) := by simp [mul_assoc]
            _ = t⁻¹ * (s * (t * v)) := by
              simpa [mul_assoc] using congrArg (fun z => t⁻¹ * z) hcommx.symm
            _ = t⁻¹ * (s * t * v) := by simp [mul_assoc]
            _ = t⁻¹ * (t * s * v) := by
              rw [hcommt.symm]
            _ = s * v := by group
        exact hcommv
      exact Set.mem_mul.mpr ⟨t, ht, v, ⟨hv, hvL⟩, hxtv.symm⟩
  obtain ⟨m, hm⟩ := exists_closedSubgroup_productMorphism_range_eq_pointwise_mul T V
  have hprodconn : Variety.IsConnected
      (Variety.prod T.carrierVariety V.carrierVariety) := by
    have hI := prodSet_irreducible_of_irreducible
      (connectedAlgebraicGroup_irreducible T.carrierVariety hT.1.isConnected)
      (connectedAlgebraicGroup_irreducible V.carrierVariety hVconn)
    have hprod : Variety.prodSet
        (Set.univ : Set (Variety.Point T.carrierVariety))
        (Set.univ : Set (Variety.Point V.carrierVariety)) =
        (Set.univ : Set (Variety.Point (Variety.prod T.carrierVariety V.carrierVariety))) := by
      ext z
      simp [Variety.prodSet]
    rw [hprod] at hI
    exact hI.isConnected
  have hrange : _root_.IsConnected (Set.range m.toFun) := by
    rw [← Set.image_univ]
    exact hprodconn.image m.toFun m.continuous.continuousOn
  have hrangeC : _root_.IsConnected
      (S.centralizer.toSubgroup : Set (Variety.Point G)) := by
    rw [← hprod_eq, ← hm]
    exact hrange
  exact carrier_isConnected_local S.centralizer hrangeC

private theorem centralizer_isConnected_of_subtorus_complement
    {G : Variety k} [AlgebraicGroup G]
    (hsolvable : Group.IsSolvable (Variety.Point G))
    (hconnected : Variety.IsConnected G)
    (U T S : ClosedSubgroup G)
    (hUrad : IsUnipotentRadicalSubgroup U)
    (hT : IsTorusComplement T U)
    (hS : IsSubtorus S) :
    Variety.IsConnected S.centralizer.carrierVariety := by
  have hUconn := hUrad.isConnected_of_solvable_connected hsolvable hconnected
  have hU := hUrad.isUnipotent_of_solvable_connected hsolvable hconnected
  have hUnormal := hUrad.normal_of_solvable_connected hsolvable hconnected
  obtain ⟨u, huU, hT'_, hST'⟩ :=
    diagonalizableClosedSubgroup_conjugate_into_torusComplement
      hsolvable hconnected U T S hUrad hT
      (isDiagonalizableClosedSubgroup_of_isSubtorus_local hS)
  let S0 := S.conjugate u⁻¹
  have hS0 : IsSubtorus S0 := by
    rcases hS with ⟨n, ⟨e⟩⟩
    exact ⟨n, ⟨(S.conjugateIso u⁻¹).comp e⟩⟩
  have hS0T : S0 ≤ T := by
    intro x hx
    have hxS : u * x * u⁻¹ ∈ S.toSubgroup := by
      simpa only [inv_inv] using (S.mem_conjugate_iff u⁻¹ x).mp hx
    have hxT' := hST' hxS
    have hxT := (T.mem_conjugate_iff u (u * x * u⁻¹)).mp hxT'
    have hcancel : u⁻¹ * (u * x * u⁻¹) * u = x := by group
    rw [hcancel] at hxT
    exact hxT
  have hS0conn := centralizer_isConnected_of_le_torus U T S0 hUconn hU hUnormal hT hS0 hS0T
  have hcentEq : S0.centralizer.conjugate u = S.centralizer := by
    calc
      S0.centralizer.conjugate u = (S0.conjugate u).centralizer :=
        (centralizer_conjugate_eq S0 u).symm
      _ = S.centralizer := by
        change ((S.conjugate u⁻¹).conjugate u).centralizer = S.centralizer
        rw [ClosedSubgroup.conjugate_conjugate]
        have hconj : S.conjugate (u * u⁻¹) = S := by
          apply SetLike.coe_injective
          ext x
          rw [show u * u⁻¹ = 1 by group, S.conjugate_one]
        rw [hconj]
  have hcentConj : _root_.IsConnected
      (S0.centralizer.conjugate u : Set (Variety.Point G)) := by
    exact closedSubgroup_conjugate_isConnected_local S0.centralizer u
      (isConnected_of_carrier_local S0.centralizer hS0conn)
  rw [hcentEq] at hcentConj
  exact carrier_isConnected_local S.centralizer hcentConj

public theorem subtorus_centralizer_isConnected_of_isConnected_of_isSolvable
    {G : Variety k} [AlgebraicGroup G]
    (hconnected : Variety.IsConnected G)
    (hsolvable : Group.IsSolvable (Variety.Point G))
    {S : ClosedSubgroup G} (hS : IsSubtorus S) :
    Variety.IsConnected S.centralizer.carrierVariety := by
  obtain ⟨U, hUrad, hUconn, T, hT, hTmax⟩ :=
    exists_maximalTorus_complement_of_solvable_connected hsolvable hconnected
  exact centralizer_isConnected_of_subtorus_complement
    hsolvable hconnected U T S hUrad hT hS

end Theory.AlgebraicGroup
