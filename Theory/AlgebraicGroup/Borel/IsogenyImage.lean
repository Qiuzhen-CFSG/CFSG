module

public import Theory.AlgebraicGroup.Borel.Commutator
public import Theory.AlgebraicGroup.Borel.Defs
public import Theory.AlgebraicGroup.Borel.SemisimpleCenter
public import Theory.AlgebraicGroup.Morphism.Connected
public import Theory.AlgebraicGroup.Morphism.Injectivity
public import Theory.AlgebraicGroup.Reductive.Defs
public import Theory.AlgebraicGroup.Semisimple.Versions
public import Theory.AlgebraicGroup.Tori.Extension

universe u

set_option linter.style.haveILetI false

namespace Theory.AlgebraicGroup

section

open scoped commutatorElement

variable {k : Type u} [Field k] [IsAlgClosed k]

set_option warningAsError false in
public theorem theorem_1_6_2_d
    {G H : Variety k} [AlgebraicGroup G] [AlgebraicGroup H]
    (φ : AlgebraicGroup.Morphism G H) (hφ : Function.Surjective φ.onPoints)
    (B : ClosedSubgroup G) (hB : IsBorelSubgroup B) :
    IsBorelSubgroup ((φ.comp B.inclusion).imageClosedSubgroup) := by sorry

/-- An isogeny from a connected algebraic group maps a Borel subgroup to a
Borel subgroup. -/
public theorem isogeny_image_isBorel
    {K H : Variety k} [AlgebraicGroup K] [AlgebraicGroup H]
    (φ : AlgebraicGroup.Morphism K H) (hφ : IsIsogeny φ)
    (hK : Variety.IsConnected K)
    (B : ClosedSubgroup K) (hB : IsBorelSubgroup B) :
    IsBorelSubgroup (φ.comp B.inclusion).imageClosedSubgroup := by
  let φB := φ.comp B.inclusion
  let imageB := φB.imageClosedSubgroup
  have hBconn : Variety.IsConnected B.carrierVariety := by
    let e := Variety.closedSubvarietyPointHomeomorph B.isZariskiClosed
    let : ConnectedSpace {x : Variety.Point K // x ∈ (B : Set (Variety.Point K))} :=
      Subtype.connectedSpace hB.1
    let : ConnectedSpace (Variety.Point B.carrierVariety) :=
      e.connectedSpace_iff.mpr inferInstance
    exact connectedSpace_iff_univ.mp inferInstance
  have hImageConnected := φB.imageClosedSubgroup_isConnected hBconn
  have hImageSolvable := φB.imageClosedSubgroup_isSolvable hB.2.1
  refine ⟨hImageConnected, hImageSolvable, ?_⟩
  intro S hSconn hSsolv hBS
  let P := φ.closedSubgroupPreimage S
  let φP₀ : AlgebraicGroup.Morphism P.carrierVariety H := φ.comp P.inclusion
  have hφP_mem (x : Variety.Point P.carrierVariety) :
      φP₀.onPoints x ∈ S.toSubgroup := by
    exact (P.pointEquiv x).property
  let φP : AlgebraicGroup.Morphism P.carrierVariety S.carrierVariety :=
    φP₀.codRestrictClosedSubgroup S hφP_mem
  have hφPsurj : Function.Surjective φP.onPoints := by
    intro y
    obtain ⟨x, hx⟩ := hφ.1 (S.inclusion.onPoints y)
    have hxP : x ∈ P.toSubgroup := by
      change φ.onPoints x ∈ S.toSubgroup
      rw [hx]
      exact (S.pointEquiv y).property
    let xp : Variety.Point P.carrierVariety := P.pointEquiv.symm ⟨x, hxP⟩
    refine ⟨xp, S.inclusion_injective ?_⟩
    rw [AlgebraicGroup.Morphism.codRestrictClosedSubgroup_inclusion_apply]
    change φ.onPoints (P.inclusion.onPoints xp) = S.inclusion.onPoints y
    rw [show P.inclusion.onPoints xp = x by
      change (P.pointEquiv xp).val = x
      dsimp only [xp]
      rw [P.pointEquiv.apply_symm_apply]]
    exact hx
  have hSconn' : Variety.IsConnected S.carrierVariety := by
    let e := Variety.closedSubvarietyPointHomeomorph S.isZariskiClosed
    let : ConnectedSpace {x : Variety.Point H // x ∈ (S : Set (Variety.Point H))} :=
      Subtype.connectedSpace hSconn
    let : ConnectedSpace (Variety.Point S.carrierVariety) :=
      e.connectedSpace_iff.mpr inferInstance
    exact connectedSpace_iff_univ.mp inferInstance
  let P₀ := AlgebraicGroup.identityComponentClosedSubgroup P.carrierVariety
  letI : AlgebraicGroup P₀.carrierVariety := P₀.carrierAlgebraicGroup
  let r : AlgebraicGroup.Morphism P₀.carrierVariety S.carrierVariety :=
    φP.comp P₀.inclusion
  have hrsurj : Function.Surjective r.onPoints := by
    exact φ.preimageRestriction_identityComponent_surjective hφ.1 S hSconn'
  have hP₀solv : Group.IsSolvable (Variety.Point P₀.carrierVariety) := by
    have hkerComm (a b : r.kernel) : a * b = b * a := by
      have haKer : φ.onPoints
          (P.inclusion.onPoints (P₀.inclusion.onPoints a.1)) = 1 := by
        have ha := a.2
        change φP.onPoints (P₀.inclusion.onPoints a.1) = 1 at ha
        have ha' := congrArg S.inclusion.onPoints ha
        rw [AlgebraicGroup.Morphism.codRestrictClosedSubgroup_inclusion_apply] at ha'
        change φ.onPoints
          (P.inclusion.onPoints (P₀.inclusion.onPoints a.1)) = 1 at ha'
        exact ha'
      have haCenter := isogeny_kernel_le_center_of_connected φ hφ hK _ haKer
      apply Subtype.ext
      apply P₀.inclusion_injective
      apply P.inclusion_injective
      change
        P.inclusion.onPoints (P₀.inclusion.onPoints a.1) *
            P.inclusion.onPoints (P₀.inclusion.onPoints b.1) =
          P.inclusion.onPoints (P₀.inclusion.onPoints b.1) *
            P.inclusion.onPoints (P₀.inclusion.onPoints a.1)
      exact (Subgroup.mem_center_iff.mp haCenter
        (P.inclusion.onPoints (P₀.inclusion.onPoints b.1))).symm
    let : Group.IsSolvable r.kernel := Group.isSolvable_of_comm hkerComm
    let : Group.IsSolvable (Variety.Point S.carrierVariety) := hSsolv
    exact Group.isSolvable_of_ker_le_range r.kernel.subtype r.onPoints (by
      intro x hx
      exact ⟨⟨x, hx⟩, rfl⟩)
  have hP₀conn : Variety.IsConnected P₀.carrierVariety := by
    let e := Variety.closedSubvarietyPointHomeomorph P₀.isZariskiClosed
    have hcarrier : (P₀ : Set (Variety.Point P.carrierVariety)) =
        AlgebraicGroup.identityComponent P.carrierVariety := by
      ext x
      rfl
    have hconn : _root_.IsConnected
        (P₀ : Set (Variety.Point P.carrierVariety)) := by
      rw [hcarrier]
      exact AlgebraicGroup.identityComponent_isConnected P.carrierVariety
    let : ConnectedSpace {x : Variety.Point P.carrierVariety //
        x ∈ (P₀ : Set (Variety.Point P.carrierVariety))} :=
      Subtype.connectedSpace hconn
    let : ConnectedSpace (Variety.Point P₀.carrierVariety) :=
      e.connectedSpace_iff.mpr inferInstance
    exact connectedSpace_iff_univ.mp inferInstance
  let qK : AlgebraicGroup.Morphism P₀.carrierVariety K :=
    P.inclusion.comp P₀.inclusion
  let Q := qK.imageClosedSubgroup
  have hQconnected := qK.imageClosedSubgroup_isConnected hP₀conn
  have hQsolvable := qK.imageClosedSubgroup_isSolvable hP₀solv
  have hBQ : B ≤ Q := by
    intro x hx
    let bx : Variety.Point B.carrierVariety := B.pointEquiv.symm ⟨x, hx⟩
    have hBPin (z : Variety.Point B.carrierVariety) :
        B.inclusion.onPoints z ∈ P.toSubgroup := by
      have hz : φB.onPoints z ∈ imageB.toSubgroup := by
        change φB.onPoints z ∈ φB.image
        exact ⟨z, rfl⟩
      have hzS : φB.onPoints z ∈ S.toSubgroup := hBS hz
      change φ.onPoints (B.inclusion.onPoints z) ∈ S.toSubgroup at hzS
      exact hzS
    let bP : AlgebraicGroup.Morphism B.carrierVariety P.carrierVariety :=
      B.inclusion.codRestrictClosedSubgroup P hBPin
    have hbP0 : bP.onPoints bx ∈ AlgebraicGroup.identityComponent P.carrierVariety := by
      apply bP.image_identityComponent_subset
      have hBzero : AlgebraicGroup.identityComponent B.carrierVariety = Set.univ :=
        (identityComponent_eq_univ_iff_isConnected B.carrierVariety).mpr hBconn
      exact ⟨bx, by rw [hBzero]; trivial, rfl⟩
    let bx₀ : Variety.Point P₀.carrierVariety :=
      P₀.pointEquiv.symm ⟨bP.onPoints bx, hbP0⟩
    change x ∈ qK.image
    refine ⟨bx₀, ?_⟩
    change P.inclusion.onPoints (P₀.inclusion.onPoints bx₀) = x
    rw [show P₀.inclusion.onPoints bx₀ = bP.onPoints bx by
      change (P₀.pointEquiv bx₀).val = bP.onPoints bx
      dsimp only [bx₀]
      rw [P₀.pointEquiv.apply_symm_apply]]
    rw [AlgebraicGroup.Morphism.codRestrictClosedSubgroup_inclusion_apply]
    change (B.pointEquiv bx).val = x
    dsimp only [bx]
    rw [B.pointEquiv.apply_symm_apply]
  have hQB : Q = B := hB.2.2 Q hQconnected hQsolvable hBQ
  apply SetLike.coe_injective
  apply Set.Subset.antisymm
  · intro y hy
    let sy : Variety.Point S.carrierVariety := S.pointEquiv.symm ⟨y, hy⟩
    obtain ⟨x, hx⟩ := hrsurj sy
    have hxQ : P.inclusion.onPoints (P₀.inclusion.onPoints x) ∈ Q.toSubgroup := by
      change qK.onPoints x ∈ qK.image
      exact ⟨x, rfl⟩
    rw [hQB] at hxQ
    let bx : Variety.Point B.carrierVariety :=
      B.pointEquiv.symm ⟨P.inclusion.onPoints (P₀.inclusion.onPoints x), hxQ⟩
    change y ∈ φB.image
    refine ⟨bx, ?_⟩
    change φ.onPoints (B.inclusion.onPoints bx) = y
    rw [show B.inclusion.onPoints bx =
        P.inclusion.onPoints (P₀.inclusion.onPoints x) by
      change (B.pointEquiv bx).val = _
      dsimp only [bx]
      rw [B.pointEquiv.apply_symm_apply]]
    have hx' := congrArg S.inclusion.onPoints hx
    calc
      φ.onPoints (P.inclusion.onPoints (P₀.inclusion.onPoints x)) =
          S.inclusion.onPoints (r.onPoints x) := by
            have h := AlgebraicGroup.Morphism.codRestrictClosedSubgroup_inclusion_apply
              φP₀ S hφP_mem (P₀.inclusion.onPoints x)
            change S.inclusion.onPoints (r.onPoints x) =
              φ.onPoints (P.inclusion.onPoints (P₀.inclusion.onPoints x)) at h
            exact h.symm
      _ = S.inclusion.onPoints sy := hx'
      _ = y := by
        change (S.pointEquiv sy).val = y
        dsimp only [sy]
        rw [S.pointEquiv.apply_symm_apply]
  · exact hBS

end

section

variable {k : Type u} [Field k] [IsAlgClosed k]

/-- An isogeny maps a maximal torus onto a maximal torus. -/
public theorem isogeny_image_isMaximalTorus
    {K H : Variety k} [AlgebraicGroup K] [AlgebraicGroup H]
    (φ : AlgebraicGroup.Morphism K H) (hφ : IsIsogeny φ)
    (T : ClosedSubgroup K) (hT : IsMaximalTorus T) :
    IsMaximalTorus (φ.comp T.inclusion).imageClosedSubgroup := by
  let φT := φ.comp T.inclusion
  let imageT := φT.imageClosedSubgroup
  have hImageT : IsSubtorus imageT :=
    morphism_image_isTorus (φ.comp T.inclusion) hT.1
  refine ⟨hImageT, ?_⟩
  intro S hS hTS
  let P := φ.closedSubgroupPreimage S
  let φP₀ : AlgebraicGroup.Morphism P.carrierVariety H := φ.comp P.inclusion
  have hφPmem (x : Variety.Point P.carrierVariety) :
      φP₀.onPoints x ∈ S.toSubgroup :=
    (P.pointEquiv x).property
  let φP : AlgebraicGroup.Morphism P.carrierVariety S.carrierVariety :=
    φP₀.codRestrictClosedSubgroup S hφPmem
  let P₀ := AlgebraicGroup.identityComponentClosedSubgroup P.carrierVariety
  letI : AlgebraicGroup P₀.carrierVariety := P₀.carrierAlgebraicGroup
  let r : AlgebraicGroup.Morphism P₀.carrierVariety S.carrierVariety :=
    φP.comp P₀.inclusion
  have hrsurj : Function.Surjective r.onPoints :=
    φ.preimageRestriction_identityComponent_surjective hφ.1 S hS.isConnected
  have hP₀torus : IsSubtorus P₀ :=
    closedSubgroupPreimage_identityComponent_isSubtorus φ hφ.2 S hS
  let qK : AlgebraicGroup.Morphism P₀.carrierVariety K :=
    P.inclusion.comp P₀.inclusion
  let Q := qK.imageClosedSubgroup
  have hQtorus : IsSubtorus Q := morphism_image_isTorus qK hP₀torus
  have hTQ : T ≤ Q := by
    intro x hx
    let tx : Variety.Point T.carrierVariety := T.pointEquiv.symm ⟨x, hx⟩
    have hTPin (z : Variety.Point T.carrierVariety) :
        T.inclusion.onPoints z ∈ P.toSubgroup := by
      have hz : φT.onPoints z ∈ imageT.toSubgroup := by
        change φT.onPoints z ∈ φT.image
        exact ⟨z, rfl⟩
      exact hTS hz
    let tP : AlgebraicGroup.Morphism T.carrierVariety P.carrierVariety :=
      T.inclusion.codRestrictClosedSubgroup P hTPin
    have htP0 : tP.onPoints tx ∈ AlgebraicGroup.identityComponent P.carrierVariety := by
      apply tP.image_identityComponent_subset
      have hTzero : AlgebraicGroup.identityComponent T.carrierVariety = Set.univ :=
        (identityComponent_eq_univ_iff_isConnected T.carrierVariety).mpr hT.1.isConnected
      exact ⟨tx, by rw [hTzero]; trivial, rfl⟩
    let tx₀ : Variety.Point P₀.carrierVariety :=
      P₀.pointEquiv.symm ⟨tP.onPoints tx, htP0⟩
    change x ∈ qK.image
    refine ⟨tx₀, ?_⟩
    change P.inclusion.onPoints (P₀.inclusion.onPoints tx₀) = x
    rw [show P₀.inclusion.onPoints tx₀ = tP.onPoints tx by
      change (P₀.pointEquiv tx₀).val = tP.onPoints tx
      dsimp only [tx₀]
      rw [P₀.pointEquiv.apply_symm_apply]]
    rw [AlgebraicGroup.Morphism.codRestrictClosedSubgroup_inclusion_apply]
    change (T.pointEquiv tx).val = x
    dsimp only [tx]
    rw [T.pointEquiv.apply_symm_apply]
  have hQT : Q = T := hT.2 Q hQtorus hTQ
  apply SetLike.coe_injective
  apply Set.Subset.antisymm
  · intro y hy
    let sy : Variety.Point S.carrierVariety := S.pointEquiv.symm ⟨y, hy⟩
    obtain ⟨x, hx⟩ := hrsurj sy
    have hxQ : P.inclusion.onPoints (P₀.inclusion.onPoints x) ∈ Q.toSubgroup := by
      change qK.onPoints x ∈ qK.image
      exact ⟨x, rfl⟩
    rw [hQT] at hxQ
    let tx : Variety.Point T.carrierVariety :=
      T.pointEquiv.symm ⟨P.inclusion.onPoints (P₀.inclusion.onPoints x), hxQ⟩
    refine ⟨tx, ?_⟩
    have hx' := congrArg S.inclusion.onPoints hx
    change S.inclusion.onPoints (φP.onPoints (P₀.inclusion.onPoints x)) =
      S.inclusion.onPoints sy at hx'
    rw [AlgebraicGroup.Morphism.codRestrictClosedSubgroup_inclusion_apply] at hx'
    have hxH : φ.onPoints (P.inclusion.onPoints (P₀.inclusion.onPoints x)) = y := by
      change φ.onPoints (P.inclusion.onPoints (P₀.inclusion.onPoints x)) =
        (S.pointEquiv sy).val at hx'
      dsimp only [sy] at hx'
      rw [S.pointEquiv.apply_symm_apply] at hx'
      exact hx'
    change φ.onPoints (T.inclusion.onPoints tx) = y
    rw [show T.inclusion.onPoints tx =
        P.inclusion.onPoints (P₀.inclusion.onPoints x) by
      change (T.pointEquiv tx).val =
        P.inclusion.onPoints (P₀.inclusion.onPoints x)
      dsimp only [tx]
      rw [T.pointEquiv.apply_symm_apply]]
    exact hxH
  · exact hTS

end

section

variable {k : Type u} [Field k] [IsAlgClosed k]

omit [IsAlgClosed k] in
/-- The conjugacy-into-Borel conclusion of Theorem 1.6.3, together with
centrality of an isogeny kernel, forces the kernel into the Borel subgroup. -/
public theorem isogeny_kernel_le_borel_of_forall_exists_conjugate_mem
    {K H : Variety k} [AlgebraicGroup K] [AlgebraicGroup H]
    (φ : AlgebraicGroup.Morphism K H) (hφ : IsIsogeny φ)
    (hK : _root_.IsConnected (Set.univ : Set (Variety.Point K)))
    (B : ClosedSubgroup K)
    (hconj : ∀ x : Variety.Point K,
      ∃ g : Variety.Point K, g⁻¹ * x * g ∈ B.toSubgroup) :
    φ.kernel ≤ B.toSubgroup := by
  intro x hx
  exact central_mem_closedSubgroup_of_exists_conjugate_mem B x
    (isogeny_kernel_le_center_of_connected φ hφ hK x hx) (hconj x)

end

section

variable {k : Type u} [Field k] [IsAlgClosed k]

omit [IsAlgClosed k] in
/-- The central kernel of an isogeny from a connected algebraic group
normalizes every closed subgroup. -/
public theorem isogeny_kernel_le_closedSubgroup_normalizer
    {K H : Variety k} [AlgebraicGroup K] [AlgebraicGroup H]
    (φ : AlgebraicGroup.Morphism K H) (hφ : IsIsogeny φ)
    (hK : _root_.IsConnected (Set.univ : Set (Variety.Point K)))
    (B : ClosedSubgroup K) :
    φ.kernel ≤ Subgroup.normalizer (B.toSubgroup : Set (Variety.Point K)) := by
  intro x hx
  exact Subgroup.centralizer_le_normalizer (B.toSubgroup : Set (Variety.Point K))
    (Subgroup.center_le_centralizer (B.toSubgroup : Set (Variety.Point K))
      (isogeny_kernel_le_center_of_connected φ hφ hK x hx))

end

section

variable {k : Type u} [Field k] [IsAlgClosed k]

/-- Proposition 1.10.3(c): an isogeny of connected algebraic groups sends a
semisimple source to a semisimple target. -/
public theorem isogeny_radical_image
    {K H : Variety k} [AlgebraicGroup K] [AlgebraicGroup H]
    (φ : AlgebraicGroup.Morphism K H) (hφ : IsIsogeny φ)
    (hK : _root_.IsConnected (Set.univ : Set (Variety.Point K)))
    (hH : _root_.IsConnected (Set.univ : Set (Variety.Point H))) :
    IsSemisimpleAlgebraicGroup K → IsSemisimpleAlgebraicGroup H := by
  intro hKsemi
  refine ⟨hH, ?_⟩
  intro R hR
  let P := φ.closedSubgroupPreimage R
  letI : AlgebraicGroup P.carrierVariety := P.carrierAlgebraicGroup
  let g := φ.preimageRestriction R
  have hg : Function.Surjective g.onPoints :=
    φ.preimageRestriction_surjective hφ.1 R
  let I := AlgebraicGroup.identityComponentClosedSubgroup P.carrierVariety
  letI : AlgebraicGroup I.carrierVariety := I.carrierAlgebraicGroup
  let iinc : AlgebraicGroup.Morphism I.carrierVariety P.carrierVariety := I.inclusion
  let qi := P.inclusion.comp iinc
  let Q := qi.imageClosedSubgroup
  have hPnormal : P.toSubgroup.Normal := by
    exact hR.1.comap φ.onPoints
  have hIindex : I.toSubgroup.FiniteIndex := by
    simpa [I, AlgebraicGroup.identityComponentClosedSubgroup_carrier] using
      AlgebraicGroup.identityComponentSubgroup_finiteIndex P.carrierVariety
  let : I.toSubgroup.FiniteIndex := hIindex
  have hIonto : Function.Surjective (fun x => g.onPoints (I.pointEquiv x).val) :=
    finiteIndex_subgroup_surjective_of_connected_target P I R g hg hR.2.1
  have hPsolvable : Group.IsSolvable (Variety.Point P.carrierVariety) := by
    let : Group.IsSolvable (Variety.Point R.carrierVariety) := hR.2.2.1
    have hkerComm : ∀ x y : g.kernel, x * y = y * x := by
      intro x y
      apply Subtype.ext
      apply P.inclusion_injective
      have hxker : φ.onPoints (P.inclusion.onPoints x.1) = 1 := by
        rw [← φ.preimageRestriction_inclusion_apply R]
        simpa using congrArg R.inclusion.onPoints x.2
      have hxcenter := isogeny_kernel_le_center_of_connected φ hφ hK
        (P.inclusion.onPoints x.1) hxker
      simpa using
        (Subgroup.mem_center_iff.mp hxcenter (P.inclusion.onPoints y.1)).symm
    let : Group.IsSolvable g.kernel := Group.isSolvable_of_comm hkerComm
    exact Group.isSolvable_of_ker_le_range g.kernel.subtype g.onPoints (by
      intro x hx
      exact ⟨⟨x, hx⟩, rfl⟩)
  let : Group.IsSolvable (Variety.Point P.carrierVariety) := hPsolvable
  have hIsolvable : Group.IsSolvable (Variety.Point I.carrierVariety) :=
    Group.isSolvable_of_isSolvable_injective I.inclusion_injective
  let : Group.IsSolvable (Variety.Point I.carrierVariety) := hIsolvable
  have hQcarrier : (Q : Set (Variety.Point K)) =
      P.inclusion.onPoints '' (I : Set (Variety.Point P.carrierVariety)) := by
    ext x
    constructor
    · intro hx
      change x ∈ qi.image at hx
      rcases hx with ⟨y, rfl⟩
      exact ⟨iinc.onPoints y, (I.pointEquiv y).property, rfl⟩
    · rintro ⟨y, hy, rfl⟩
      change P.inclusion.onPoints y ∈ qi.image
      let z : Variety.Point I.carrierVariety := I.pointEquiv.symm ⟨y, hy⟩
      refine ⟨z, ?_⟩
      change P.inclusion.onPoints (iinc.onPoints z) = P.inclusion.onPoints y
      congr 2
  have hQconnected : _root_.IsConnected (Q : Set (Variety.Point K)) := by
    rw [hQcarrier]
    exact (AlgebraicGroup.identityComponent_isConnected P.carrierVariety).image
      P.inclusion.onPoints P.inclusion.toVariety.continuous.continuousOn
  have hQnormal : Q.toSubgroup.Normal := by
    constructor
    intro x hx z
    change x ∈ (Q : Set (Variety.Point K)) at hx
    change z * x * z⁻¹ ∈ (Q : Set (Variety.Point K))
    rw [hQcarrier] at hx ⊢
    rcases hx with ⟨y, hy, rfl⟩
    let cAmb : AlgebraicGroup.Morphism P.carrierVariety K :=
      { toVariety := (AlgebraicGroup.conjugationByMorphism K z).comp
          P.inclusion.toVariety
        map_one := by
          change z * P.inclusion.onPoints 1 * z⁻¹ = 1
          rw [P.inclusion.onPoints.map_one]
          group
        map_mul := by
          intro a b
          change z * P.inclusion.onPoints (a * b) * z⁻¹ =
            (z * P.inclusion.onPoints a * z⁻¹) *
              (z * P.inclusion.onPoints b * z⁻¹)
          rw [P.inclusion.onPoints.map_mul]
          group }
    have hcP : ∀ a, cAmb.onPoints a ∈ P := by
      intro a
      change z * P.inclusion.onPoints a * z⁻¹ ∈ P
      exact hPnormal.conj_mem _ (P.pointEquiv a).property z
    let c := cAmb.codRestrictClosedSubgroup P hcP
    have hyI : y ∈ AlgebraicGroup.identityComponent P.carrierVariety := by
      exact hy
    have hcy := c.image_identityComponent_subset ⟨y, hyI, rfl⟩
    let w : Variety.Point I.carrierVariety := I.pointEquiv.symm ⟨c.onPoints y, hcy⟩
    refine ⟨c.onPoints y, hcy, ?_⟩
    rw [cAmb.codRestrictClosedSubgroup_inclusion_apply]
    change (AlgebraicGroup.conjugationByMorphism K z).toFun
      (P.inclusion.onPoints y) = _
    rw [AlgebraicGroup.conjugationByMorphism_apply]
  have hQsolvable : Group.IsSolvable (Variety.Point Q.carrierVariety) := by
    have hqi_mem : ∀ x, qi.onPoints x ∈ Q.toSubgroup := by
      intro x
      exact ⟨x, rfl⟩
    let qToQ := qi.codRestrictClosedSubgroup Q hqi_mem
    have hqsurj : Function.Surjective qToQ.onPoints := by
      intro y
      have hy : Q.inclusion.onPoints y ∈ qi.image := (Q.pointEquiv y).property
      rcases hy with ⟨x, hx⟩
      refine ⟨x, ?_⟩
      apply Q.inclusion_injective
      change Q.inclusion.onPoints
        ((qi.codRestrictClosedSubgroup Q hqi_mem).onPoints x) =
          Q.inclusion.onPoints y
      rw [AlgebraicGroup.Morphism.codRestrictClosedSubgroup_inclusion_apply]
      exact hx
    exact Group.isSolvable_of_surjective hqsurj
  have hQradical : IsRadicalSubgroup Q := by
    refine ⟨hQnormal, hQconnected, hQsolvable, ?_⟩
    intro N hNnormal hNconnected hNsolvable
    let fN := φ.comp N.inclusion
    let J := fN.imageClosedSubgroup
    have hJmap : J.toSubgroup = N.toSubgroup.map φ.onPoints := by
      ext y
      constructor
      · intro hy
        change y ∈ fN.image at hy
        rcases hy with ⟨x, rfl⟩
        exact ⟨N.inclusion.onPoints x, (N.pointEquiv x).property, rfl⟩
      · rintro ⟨x, hx, rfl⟩
        change φ.onPoints x ∈ fN.image
        let z : Variety.Point N.carrierVariety := N.pointEquiv.symm ⟨x, hx⟩
        refine ⟨z, ?_⟩
        change φ.onPoints (N.inclusion.onPoints z) = φ.onPoints x
        congr 2
    have hJnormal : J.toSubgroup.Normal := by
      rw [hJmap]
      exact hNnormal.map φ.onPoints hφ.1
    have hJconnected : _root_.IsConnected (J : Set (Variety.Point H)) := by
      change _root_.IsConnected (J.toSubgroup : Set (Variety.Point H))
      rw [hJmap]
      exact hNconnected.image φ.onPoints φ.toVariety.continuous.continuousOn
    have hJsolvable : Group.IsSolvable (Variety.Point J.carrierVariety) := by
      let : Group.IsSolvable (Variety.Point N.carrierVariety) := hNsolvable
      have hfN_mem : ∀ x, fN.onPoints x ∈ J.toSubgroup := by
        intro x
        exact ⟨x, rfl⟩
      let fToJ := fN.codRestrictClosedSubgroup J hfN_mem
      have hsurj : Function.Surjective fToJ.onPoints := by
        intro y
        have hy : J.inclusion.onPoints y ∈ fN.image := (J.pointEquiv y).property
        rcases hy with ⟨x, hx⟩
        refine ⟨x, ?_⟩
        apply J.inclusion_injective
        change J.inclusion.onPoints
          ((fN.codRestrictClosedSubgroup J hfN_mem).onPoints x) =
            J.inclusion.onPoints y
        rw [AlgebraicGroup.Morphism.codRestrictClosedSubgroup_inclusion_apply]
        exact hx
      exact Group.isSolvable_of_surjective hsurj
    have hJR : J ≤ R := hR.2.2.2 J hJnormal hJconnected hJsolvable
    have hNP : ∀ x, x ∈ N → x ∈ P := by
      intro x hx
      change φ.onPoints x ∈ R
      apply hJR
      change φ.onPoints x ∈ fN.image
      let z : Variety.Point N.carrierVariety := N.pointEquiv.symm ⟨x, hx⟩
      exact ⟨z, by
        change φ.onPoints (N.inclusion.onPoints z) = φ.onPoints x
        congr 2⟩
    let nP := N.inclusion.codRestrictClosedSubgroup P (fun x => hNP _ (N.pointEquiv x).property)
    have hNvar : Variety.IsConnected N.carrierVariety := by
      let e := Variety.closedSubvarietyPointHomeomorph N.isZariskiClosed
      let : ConnectedSpace {x : Variety.Point K // x ∈ (N : Set (Variety.Point K))} :=
        Subtype.connectedSpace hNconnected
      let : ConnectedSpace (Variety.Point N.carrierVariety) :=
        e.connectedSpace_iff.mpr inferInstance
      exact connectedSpace_iff_univ.mp inferInstance
    intro x hx
    rw [hQcarrier]
    let z : Variety.Point N.carrierVariety := N.pointEquiv.symm ⟨x, hx⟩
    have hz0 : z ∈ AlgebraicGroup.identityComponent N.carrierVariety := by
      rw [(identityComponent_eq_univ_iff_isConnected N.carrierVariety).mpr hNvar]
      trivial
    have hnP0 := nP.image_identityComponent_subset ⟨z, hz0, rfl⟩
    refine ⟨nP.onPoints z, hnP0, ?_⟩
    rw [N.inclusion.codRestrictClosedSubgroup_inclusion_apply]
    congr 2
  have hQbot : Q.toSubgroup = ⊥ := hKsemi.2 Q hQradical
  have hIbot : I.toSubgroup = ⊥ := by
    apply le_antisymm
    · intro x hx
      have hqx : qi.onPoints (I.pointEquiv.symm ⟨x, hx⟩) ∈ Q :=
        Set.mem_range_self _
      change qi.onPoints (I.pointEquiv.symm ⟨x, hx⟩) ∈ Q.toSubgroup at hqx
      rw [hQbot] at hqx
      have hqone : qi.onPoints (I.pointEquiv.symm ⟨x, hx⟩) = 1 := hqx
      have hz : iinc.onPoints (I.pointEquiv.symm ⟨x, hx⟩) = x := by
        change (I.pointEquiv (I.pointEquiv.symm ⟨x, hx⟩)).val = x
        rw [I.pointEquiv.apply_symm_apply]
      have hqone' : P.inclusion.onPoints
          (iinc.onPoints (I.pointEquiv.symm ⟨x, hx⟩)) = 1 := by
        dsimp [qi, AlgebraicGroup.Morphism.comp,
          AlgebraicGroup.Morphism.onPoints, Variety.Morphism.comp] at hqone
        exact hqone
      change x = 1
      apply P.inclusion_injective
      rw [← hz]
      exact hqone'
    · exact bot_le
  apply SetLike.coe_injective
  apply Set.eq_singleton_iff_unique_mem.mpr
  refine ⟨R.toSubgroup.one_mem, ?_⟩
  intro y hy
  let yR : Variety.Point R.carrierVariety := R.pointEquiv.symm ⟨y, hy⟩
  obtain ⟨x, hx⟩ := hIonto yR
  have hxbot : I.pointEquiv x = 1 := by
    apply Subtype.ext
    have hxmem : (I.pointEquiv x).val ∈
        (⊥ : Subgroup (Variety.Point P.carrierVariety)) := by
      rw [← hIbot]
      exact (I.pointEquiv x).property
    exact hxmem
  calc
    y = R.inclusion.onPoints yR := by
      change y = (R.pointEquiv (R.pointEquiv.symm ⟨y, hy⟩)).val
      rw [R.pointEquiv.apply_symm_apply]
    _ = R.inclusion.onPoints (g.onPoints (I.pointEquiv x).val) :=
      congrArg R.inclusion.onPoints hx.symm
    _ = φ.onPoints (P.inclusion.onPoints (I.pointEquiv x).val) :=
      φ.preimageRestriction_inclusion_apply R _
    _ = 1 := by rw [hxbot]; simp

end

open scoped Pointwise

section

variable {k : Type u} [Field k] [IsAlgClosed k]

/-- Two root-decomposed closed subgroups with dense pointwise product force the
whole torus and all-root subgroup to generate the connected ambient group. -/
public theorem rootSubgroupGenerated_sup_torus_eq_top_of_dense_decomposition_product
    {K : Variety k} [AlgebraicGroup K]
    [Nonempty (Variety.Point K)] [PreirreducibleSpace (Variety.Point K)]
    (T B Bopp : ClosedSubgroup K)
    (D : RootGroupData K T) (P Popp : Set D.Root)
    (hK : _root_.IsConnected (Set.univ : Set (Variety.Point K)))
    (hBform : ∀ x, x ∈ B ↔ ∃ t u,
      t ∈ T ∧ u ∈ RootSubgroupGenerated D P ∧ x = t * u)
    (hBoppform : ∀ x, x ∈ Bopp ↔ ∃ t u,
      t ∈ T ∧ u ∈ RootSubgroupGenerated D Popp ∧ x = t * u)
    (hdense : Dense
      ((B.toSubgroup : Set (Variety.Point K)) *
        (Bopp.toSubgroup : Set (Variety.Point K)))) :
    RootSubgroupGenerated D Set.univ ⊔ T.toSubgroup = ⊤ := by
  apply closedSubgroup_product_dense_contained_subgroup_eq_top
    (RootSubgroupGenerated D Set.univ ⊔ T.toSubgroup) B Bopp hK
  · exact closedSubgroup_le_rootSubgroupGenerated_sup_torus_of_decomposition
      T B D P hBform
  · exact closedSubgroup_le_rootSubgroupGenerated_sup_torus_of_decomposition
      T Bopp D Popp hBoppform
  · exact hdense

end

open scoped Pointwise

section

variable {k : Type u} [Field k] [IsAlgClosed k]

omit [IsAlgClosed k] in
/-- Two subgroups with root decompositions whose pointwise product is open
force the torus and all root subgroups to generate the connected ambient
algebraic group.  For opposite Borel subgroups, the remaining geometric input
is precisely openness of the big cell. -/
public theorem rootSubgroupGenerated_sup_torus_eq_top_of_open_decomposition_product
    {K : Variety k} [AlgebraicGroup K] (T B Bopp : ClosedSubgroup K)
    (D : RootGroupData K T) (P Popp : Set D.Root)
    (hK : _root_.IsConnected (Set.univ : Set (Variety.Point K)))
    (hBform : ∀ x, x ∈ B ↔ ∃ t u,
      t ∈ T ∧ u ∈ RootSubgroupGenerated D P ∧ x = t * u)
    (hBoppform : ∀ x, x ∈ Bopp ↔ ∃ t u,
      t ∈ T ∧ u ∈ RootSubgroupGenerated D Popp ∧ x = t * u)
    (hopen : IsOpen
      ((B.toSubgroup : Set (Variety.Point K)) *
        (Bopp.toSubgroup : Set (Variety.Point K)))) :
    RootSubgroupGenerated D Set.univ ⊔ T.toSubgroup = ⊤ := by
  apply subgroup_eq_top_of_contains_subgroups_with_open_product
    (RootSubgroupGenerated D Set.univ ⊔ T.toSubgroup)
      B.toSubgroup Bopp.toSubgroup hK
  · exact closedSubgroup_le_rootSubgroupGenerated_sup_torus_of_decomposition
      T B D P hBform
  · exact closedSubgroup_le_rootSubgroupGenerated_sup_torus_of_decomposition
      T Bopp D Popp hBoppform
  · exact hopen

end

section

/-! A connected nonzero-pairing graph is irreducible in the source's
set-theoretic sense.  The closure premise keeps the graph inside the chosen
root set; it is independent of any algebraic-group component conclusion. -/

public theorem isPairingIrreducible_of_connected
    {ι S : Type*} [Zero S]
    (pairing : ι → ι → S) (roots : Set ι)
    (hnonempty : roots.Nonempty)
    (hconn : ∀ α ∈ roots, ∀ β ∈ roots,
      Relation.ReflTransGen
        (fun i j : ι => pairing i j ≠ 0 ∨ pairing j i ≠ 0) α β)
    (hclosed : ∀ {x y : ι}, x ∈ roots →
      (pairing x y ≠ 0 ∨ pairing y x ≠ 0) → y ∈ roots) :
    IsPairingIrreducible pairing roots := by
  refine ⟨hnonempty, ?_⟩
  intro roots₁ roots₂ hUnion hDisjoint h₁ h₂
  obtain ⟨a, ha⟩ := h₁
  obtain ⟨b, hb⟩ := h₂
  have haRoots : a ∈ roots := by rw [hUnion]; exact Or.inl ha
  have hbRoots : b ∈ roots := by rw [hUnion]; exact Or.inr hb
  by_contra hcross
  push Not at hcross
  have hstep_mem : ∀ {x y : ι}, x ∈ roots₁ → y ∈ roots →
      (pairing x y ≠ 0 ∨ pairing y x ≠ 0) → y ∈ roots₁ := by
    intro x y hx hy hxy
    have hyUnion : y ∈ roots₁ ∨ y ∈ roots₂ := by
      have hy' : y ∈ roots₁ ∪ roots₂ := by simpa [hUnion] using hy
      exact hy'
    rcases hyUnion with hy1 | hy2
    · exact hy1
    · exact False.elim <| hxy.elim
        (fun hxy' => (hxy' (hcross x hx y hy2).1).elim)
        (fun hyx' => (hyx' (hcross x hx y hy2).2).elim)
  have hpath_mem : ∀ {x y : ι}, x ∈ roots₁ →
      Relation.ReflTransGen
        (fun i j : ι => pairing i j ≠ 0 ∨ pairing j i ≠ 0) x y → y ∈ roots₁ := by
    intro x y hx hxy
    induction hxy with
    | refl => exact hx
    | @tail z w hxy hstep ih =>
        exact hstep_mem ih (hclosed (by
          have : z ∈ roots₁ := ih
          rw [hUnion]
          exact Or.inl this) hstep) hstep
  exact (Set.disjoint_left.1 hDisjoint)
    (hpath_mem ha (hconn a haRoots b hbRoots)) hb

end

section

variable {k : Type u} [Field k] [IsAlgClosed k]

/-- Proposition 1.10.3(d), the forward Borel-restriction implication. -/
public theorem borel_restriction_iso_of_global_isomorphism
    {K H : Variety k} [AlgebraicGroup K] [AlgebraicGroup H]
    (φ : AlgebraicGroup.Morphism K H) (_hφ : IsIsogeny φ)
    (_hK : _root_.IsConnected (Set.univ : Set (Variety.Point K)))
    (_hH : _root_.IsConnected (Set.univ : Set (Variety.Point H)))
    (_hKsemi : IsSemisimpleAlgebraicGroup K)
    (_hHsemi : IsSemisimpleAlgebraicGroup H)
    (B T : ClosedSubgroup K) (_hB : IsBorelSubgroup B)
    (_hT : IsMaximalTorus T) :
    let φB := φ.comp B.inclusion
    let imageB := φB.imageClosedSubgroup
    (∃ e : AlgebraicGroup.Iso K H,
        ∀ x, e.hom.onPoints x = φ.onPoints x) →
      ∃ eB : AlgebraicGroup.Iso B.carrierVariety imageB.carrierVariety,
        ∀ x, imageB.inclusion.onPoints (eB.hom.onPoints x) =
          φ.onPoints (B.inclusion.onPoints x) := by
  dsimp
  intro he
  exact isogeny_borel_restriction_iso_of_iso φ B he.choose he.choose_spec

end

section

variable {k : Type u} [Field k] [IsAlgClosed k]

omit [IsAlgClosed k] in
/-- Positive and negative root decompositions identify the subgroup generated
by the two decomposed subgroups with the subgroup generated by the torus and
all root subgroups. -/
public theorem closedSubgroup_sup_eq_rootSubgroupGenerated_sup_torus_of_opposite_decompositions
    {K : Variety k} [AlgebraicGroup K] (T B Bopp : ClosedSubgroup K)
    (D : RootGroupData K T) (P : Set D.Root)
    (hP : IsPositiveSystem D P)
    (hBform : ∀ x, x ∈ B ↔ ∃ t u,
      t ∈ T ∧ u ∈ RootSubgroupGenerated D P ∧ x = t * u)
    (hBoppform : ∀ x, x ∈ Bopp ↔ ∃ t u,
      t ∈ T ∧ u ∈ RootSubgroupGenerated D (D.neg ⁻¹' P) ∧ x = t * u) :
    B.toSubgroup ⊔ Bopp.toSubgroup =
      RootSubgroupGenerated D Set.univ ⊔ T.toSubgroup := by
  apply le_antisymm
  · exact sup_le
      (closedSubgroup_le_rootSubgroupGenerated_sup_torus_of_decomposition
        T B D P hBform)
      (closedSubgroup_le_rootSubgroupGenerated_sup_torus_of_decomposition
        T Bopp D (D.neg ⁻¹' P) hBoppform)
  · apply sup_le
    · rw [← rootSubgroupGenerated_sup_negPreimage_eq_univ_of_isPositiveSystem
        D P hP]
      apply sup_le
      · intro x hx
        apply Subgroup.mem_sup_left
        exact (hBform x).mpr
          ⟨1, x, T.one_mem, hx, (one_mul x).symm⟩
      · intro x hx
        apply Subgroup.mem_sup_right
        exact (hBoppform x).mpr
          ⟨1, x, T.one_mem, hx, (one_mul x).symm⟩
    · intro t ht
      apply Subgroup.mem_sup_left
      exact (hBform t).mpr
        ⟨t, 1, ht, (RootSubgroupGenerated D P).one_mem, (mul_one t).symm⟩

end

section

variable {k : Type u} [Field k] [IsAlgClosed k]

omit [IsAlgClosed k] in
/-- The Plücker conjugation morphism is injective on a root subgroup whose
root weight is nontrivial. -/
public theorem centerPluckerConjugationMorphism_rootSubgroup_injective
    {K : Variety k} [AlgebraicGroup K]
    (hK : IsSemisimpleAlgebraicGroup K)
    (T X : ClosedSubgroup K) (χ : TorusWeight T)
    (hX : IsTorusRootSubgroup T X)
    (hEq : RootWeightEquation T X χ) (hχ : χ ≠ 1) :
    Function.Injective
      ((ClosedSubgroup.rightTranslateVanishingPluckerConjugationMorphism
        ((ClosedSubgroup.top (G := K)).centralizer)).comp X.inclusion).onPoints := by
  let Z : ClosedSubgroup K := (ClosedSubgroup.top (G := K)).centralizer
  let p := Z.rightTranslateVanishingPluckerConjugationMorphism
  let fX := p.comp X.inclusion
  have hpKernel : p.kernel = Subgroup.center (Variety.Point K) :=
    centerPluckerConjugationMorphism_kernel_eq hK
  have hinter :=
    rootSubgroup_inf_center_eq_bot_of_weight_ne_one T X χ hX hEq hχ
  have hfKernel : fX.kernel = ⊥ := by
    apply le_antisymm
    · intro x hx
      apply Subgroup.mem_bot.mpr
      apply X.inclusion_injective
      rw [map_one]
      apply Subgroup.mem_bot.mp
      rw [← hinter]
      constructor
      · exact (X.pointEquiv x).property
      · rw [← hpKernel]
        exact hx
    · exact bot_le
  apply (MonoidHom.ker_eq_bot_iff fX.onPoints).mp
  exact hfKernel

end

section

variable {k : Type u} [Field k] [IsAlgClosed k]

public theorem universalVersion_center_finite
    {Ku : Variety k} [AlgebraicGroup Ku]
    (hKu : IsUniversalVersion Ku) :
    Finite (Subgroup.center (Variety.Point Ku)) :=
  connectedSemisimple_center_finite hKu.1

end

section

variable {k : Type u} [Field k] [IsAlgClosed k]

omit [IsAlgClosed k] in
/-- A nontrivial root weight produces a center-invariant ambient polynomial
whose restriction to the chosen root parametrization is the affine parameter. -/
public theorem rootParameter_exists_centerInvariantPolynomial
    {K : Variety k} [AlgebraicGroup K]
    (T X : ClosedSubgroup K) (χ : TorusWeight T)
    (hEq : RootWeightEquation T X χ) (hχ : χ ≠ 1)
    (x : OneParameterParametrization X.carrierVariety) :
    ∃ F : Variety.PolynomialFunction K,
      F ∈ AlgebraicGroup.rightInvariantCoordinateRing
        ((ClosedSubgroup.top (G := K)).centralizer) ∧
      ∀ t : k, F (X.includePoint (x.value t)) = t := by
  have hpointNe : χ.pointCharacter ≠ (1 : TorusWeight T).pointCharacter := by
    intro heq
    exact hχ (TorusCharacter.pointCharacter_injective heq)
  obtain ⟨s, hs⟩ : ∃ s, χ.pointCharacter s ≠ 1 := by
    by_contra hall
    simp only [not_exists, not_not] at hall
    apply hpointNe
    ext y
    rw [show (1 : TorusWeight T).pointCharacter y = 1 by rfl]
    exact hall y
  let c : k := χ.pointCharacter s
  have hc : c - 1 ≠ 0 := sub_ne_zero.mpr hs
  obtain ⟨A, hA⟩ :=
    oneParameterParametrization_exists_ambient_parameterPolynomial X x
  let delta : Variety.Morphism K K :=
    (AlgebraicGroup.commutatorMorphism K).comp
      ((Variety.Morphism.const K K (T.includePoint s)⁻¹).pair
        (Variety.Morphism.id K))
  have hdelta_apply (g : Variety.Point K) :
      delta.toFun g = (T.includePoint s)⁻¹ * g * T.includePoint s * g⁻¹ := by
    change (AlgebraicGroup.commutatorMorphism K).toFun
      ((Variety.prodPointEquiv K K).symm ((T.includePoint s)⁻¹, g)) = _
    simpa using
      AlgebraicGroup.commutatorMorphism_apply K (T.includePoint s)⁻¹ g
  let F : Variety.PolynomialFunction K :=
    (c - 1)⁻¹ • Variety.PolynomialFunction.pullback delta A
  refine ⟨F, ?_, ?_⟩
  · rw [AlgebraicGroup.mem_rightInvariantCoordinateRing_iff]
    intro g z hz
    dsimp [F]
    simp only [polynomialFunction_smul_apply]
    change (c - 1)⁻¹ * A (delta.toFun (g * z)) =
      (c - 1)⁻¹ * A (delta.toFun g)
    congr 2
    rw [hdelta_apply, hdelta_apply]
    change z ∈ Subgroup.centralizer
      ((ClosedSubgroup.top (G := K)).toSubgroup : Set (Variety.Point K)) at hz
    rw [show (ClosedSubgroup.top (G := K)).toSubgroup = ⊤ by rfl,
      Subgroup.coe_top, Subgroup.centralizer_univ] at hz
    have hzs := Subgroup.mem_center_iff.mp hz (T.includePoint s)
    rw [mul_inv_rev]
    calc
      (T.includePoint s)⁻¹ * (g * z) * T.includePoint s * (z⁻¹ * g⁻¹) =
          (T.includePoint s)⁻¹ * g * (z * T.includePoint s) *
            (z⁻¹ * g⁻¹) := by
        simp only [mul_assoc]
      _ = (T.includePoint s)⁻¹ * g * (T.includePoint s * z) *
          (z⁻¹ * g⁻¹) := by
        rw [hzs]
      _ = (T.includePoint s)⁻¹ * g * T.includePoint s * g⁻¹ := by
        simp only [mul_assoc]
        rw [mul_inv_cancel_left]
  · intro t
    dsimp [F]
    simp only [polynomialFunction_smul_apply]
    change (c - 1)⁻¹ * A (delta.toFun (X.includePoint (x.value t))) = t
    have hconj := hEq x t s
    have hdelta : delta.toFun (X.includePoint (x.value t)) =
        X.includePoint (x.value ((c - 1) * t)) := by
      rw [hdelta_apply]
      rw [hconj]
      change X.inclusion.onPoints (x.hom.onPoints (kPlusPoint (c * t))) *
          (X.inclusion.onPoints (x.hom.onPoints (kPlusPoint t)))⁻¹ = _
      rw [← map_inv, ← map_mul]
      change X.inclusion.onPoints _ = X.inclusion.onPoints _
      refine congrArg X.inclusion.onPoints ?_
      rw [← map_inv, ← map_mul]
      refine congrArg x.hom.onPoints ?_
      apply Variety.Point.ext
      funext i
      rw [show i = PUnit.unit by rfl]
      change c * t + -t = (c - 1) * t
      ring
    rw [hdelta, hA]
    field_simp

end

section

variable {k : Type u} [Field k] [IsAlgClosed k]

/-- A conjugacy-into-Borel hypothesis transfers a Borel restriction
isomorphism of an isogeny to ambient point injectivity. -/
public theorem isogeny_injective_of_borel_restriction_iso_of_forall_exists_conjugate_mem
    {K H : Variety k} [AlgebraicGroup K] [AlgebraicGroup H]
    (φ : AlgebraicGroup.Morphism K H) (hφ : IsIsogeny φ)
    (hK : _root_.IsConnected (Set.univ : Set (Variety.Point K)))
    (B : ClosedSubgroup K)
    (hconj : ∀ x : Variety.Point K,
      ∃ g : Variety.Point K, g⁻¹ * x * g ∈ B.toSubgroup)
    (eB : AlgebraicGroup.Iso B.carrierVariety
      (φ.comp B.inclusion).imageClosedSubgroup.carrierVariety)
    (heB : ∀ x,
      (φ.comp B.inclusion).imageClosedSubgroup.inclusion.onPoints
        (eB.hom.onPoints x) = φ.onPoints (B.inclusion.onPoints x)) :
    Function.Injective φ.onPoints := by
  exact φ.injective_of_closedSubgroup_image_iso B
    (isogeny_kernel_le_borel_of_forall_exists_conjugate_mem φ hφ hK B hconj)
    eB heB

/-- A Borel-restriction isomorphism extends to a global algebraic-group
isomorphism once conjugacy into the Borel and pullback surjectivity are
available. -/
public theorem isogeny_iso_of_borel_restriction_iso_of_forall_exists_conjugate_mem_of_pullback_surjective
    {K H : Variety k} [AlgebraicGroup K] [AlgebraicGroup H]
    (φ : AlgebraicGroup.Morphism K H) (hφ : IsIsogeny φ)
    (hK : _root_.IsConnected (Set.univ : Set (Variety.Point K)))
    (B : ClosedSubgroup K)
    (hconj : ∀ x : Variety.Point K,
      ∃ g : Variety.Point K, g⁻¹ * x * g ∈ B.toSubgroup)
    (eB : AlgebraicGroup.Iso B.carrierVariety
      (φ.comp B.inclusion).imageClosedSubgroup.carrierVariety)
    (heB : ∀ x,
      (φ.comp B.inclusion).imageClosedSubgroup.inclusion.onPoints
        (eB.hom.onPoints x) = φ.onPoints (B.inclusion.onPoints x))
    (hpull : Function.Surjective φ.toVariety.pullbackRingHom) :
    ∃ e : AlgebraicGroup.Iso K H, e.hom = φ := by
  have hinj : Function.Injective φ.onPoints :=
    isogeny_injective_of_borel_restriction_iso_of_forall_exists_conjugate_mem
      φ hφ hK B hconj eB heB
  exact isogeny_iso_of_injective_of_pullback_surjective φ hφ hinj hpull

end

section

variable {k : Type u} [Field k] [IsAlgClosed k]

omit [IsAlgClosed k] in
/-- Normalizer equality is the exact additional hypothesis needed to turn the
unconditional central-kernel containment into containment in a closed subgroup.
-/
public theorem isogeny_kernel_le_closedSubgroup_of_normalizer_eq
    {K H : Variety k} [AlgebraicGroup K] [AlgebraicGroup H]
    (φ : AlgebraicGroup.Morphism K H) (hφ : IsIsogeny φ)
    (hK : _root_.IsConnected (Set.univ : Set (Variety.Point K)))
    (B : ClosedSubgroup K)
    (hself : Subgroup.normalizer (B.toSubgroup : Set (Variety.Point K)) =
      B.toSubgroup) :
    φ.kernel ≤ B.toSubgroup := by
  rw [← hself]
  exact isogeny_kernel_le_closedSubgroup_normalizer φ hφ hK B

end

section

variable {k : Type u} [Field k] [IsAlgClosed k]

set_option maxHeartbeats 800000 in
public theorem semisimple_centerQuotient_isogeny
    {K : Variety k} [AlgebraicGroup K]
    (hK : IsSemisimpleAlgebraicGroup K) :
    ∃ Q : Variety k, ∃ _ : AlgebraicGroup Q,
      ∃ q : AlgebraicGroup.Morphism K Q,
        IsIsogeny q ∧
          q.kernel = Subgroup.center (Variety.Point K) ∧
          IsSemisimpleAlgebraicGroup Q := by
  let Z : ClosedSubgroup K := (ClosedSubgroup.top (G := K)).centralizer
  let p := Z.rightTranslateVanishingPluckerConjugationMorphism
  have hpKernel : p.kernel = Subgroup.center (Variety.Point K) :=
    centerPluckerConjugationMorphism_kernel_eq hK
  let Q := p.imageClosedSubgroup
  letI : AlgebraicGroup Q.carrierVariety := Q.carrierAlgebraicGroup
  have hpMem (x : Variety.Point K) : p.onPoints x ∈ Q.toSubgroup := by
    change p.onPoints x ∈ p.image
    exact ⟨x, rfl⟩
  let q : AlgebraicGroup.Morphism K Q.carrierVariety :=
    p.codRestrictClosedSubgroup Q hpMem
  have hqSurjective : Function.Surjective q.onPoints :=
    AlgebraicGroup.Morphism.codRestrictImageClosedSubgroup_surjective p hpMem
  have hqKernel : q.kernel = Subgroup.center (Variety.Point K) := by
    calc
      q.kernel = p.kernel :=
        AlgebraicGroup.Morphism.codRestrictClosedSubgroup_kernel_eq p Q hpMem
      _ = Subgroup.center (Variety.Point K) := hpKernel
  let : Finite (Subgroup.center (Variety.Point K)) :=
    connectedSemisimple_center_finite hK
  have hqFinite : Finite q.kernel := by
    rw [hqKernel]
    infer_instance
  have hqIsogeny : IsIsogeny q := ⟨hqSurjective, hqFinite⟩
  have hQconnected : Variety.IsConnected Q.carrierVariety :=
    connected_of_surjective_morphism q hK.1 hqSurjective
  have hQsemisimple : IsSemisimpleAlgebraicGroup Q.carrierVariety :=
    isogeny_radical_image q hqIsogeny hK.1 hQconnected hK
  exact ⟨Q.carrierVariety, inferInstance, q, hqIsogeny, hqKernel, hQsemisimple⟩

end

section

variable {k : Type u} [Field k] [IsAlgClosed k]

/-- Theorem 1.10.4(d): an adjoint version has trivial center. -/
public theorem adjointVersion_center_eq_bot
    {Ka : Variety k} [AlgebraicGroup Ka]
    (hKa : IsAdjointVersion Ka) :
    Subgroup.center (Variety.Point Ka) = ⊥ := by
  obtain ⟨Q, _, q, hq, hqKernel, _hQ⟩ :=
    semisimple_centerQuotient_isogeny hKa.1
  have hqInjective : Function.Injective q.onPoints := hKa.2 q hq
  have hqKernelBot : q.kernel = (⊥ : Subgroup (Variety.Point Ka)) :=
    (MonoidHom.ker_eq_bot_iff q.onPoints).2 hqInjective
  calc
    Subgroup.center (Variety.Point Ka) = q.kernel := hqKernel.symm
    _ = ⊥ := hqKernelBot

end

open scoped Pointwise

section

variable {k : Type u} [Field k] [IsAlgClosed k]

/-- A dense product of opposite decomposed subgroups forces the torus and all
root subgroups to generate the connected ambient group. -/
public theorem rootSubgroupGenerated_sup_torus_eq_top_of_dense_opposite_decomposition_product
    {K : Variety k} [AlgebraicGroup K]
    [Nonempty (Variety.Point K)] [PreirreducibleSpace (Variety.Point K)]
    (T B Bopp : ClosedSubgroup K)
    (D : RootGroupData K T) (P : Set D.Root)
    (hP : IsPositiveSystem D P)
    (hK : _root_.IsConnected (Set.univ : Set (Variety.Point K)))
    (hBform : ∀ x, x ∈ B ↔ ∃ t u,
      t ∈ T ∧ u ∈ RootSubgroupGenerated D P ∧ x = t * u)
    (hBoppform : ∀ x, x ∈ Bopp ↔ ∃ t u,
      t ∈ T ∧ u ∈ RootSubgroupGenerated D (D.neg ⁻¹' P) ∧ x = t * u)
    (hdense : Dense
      ((B.toSubgroup : Set (Variety.Point K)) *
        (Bopp.toSubgroup : Set (Variety.Point K)))) :
    RootSubgroupGenerated D Set.univ ⊔ T.toSubgroup = ⊤ := by
  have hsup : B.toSubgroup ⊔ Bopp.toSubgroup = ⊤ := by
    apply closedSubgroup_product_dense_contained_subgroup_eq_top
      (B.toSubgroup ⊔ Bopp.toSubgroup) B Bopp hK
    · exact le_sup_left
    · exact le_sup_right
    · exact hdense
  rw [closedSubgroup_sup_eq_rootSubgroupGenerated_sup_torus_of_opposite_decompositions
    T B Bopp D P hP hBform hBoppform] at hsup
  exact hsup

end

end Theory.AlgebraicGroup
