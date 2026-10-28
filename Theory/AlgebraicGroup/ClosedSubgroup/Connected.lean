module

public import Theory.AlgebraicGroup.ClosedSubgroup.Conjugation
public import Theory.AlgebraicGroup.Dimension.Fiber

universe u

set_option linter.style.haveILetI false

/-! Identity components of closed subgroups in the ambient algebraic group. -/

namespace Theory.AlgebraicGroup

section

variable {k : Type u} [Field k] [IsAlgClosed k]

/-- The identity component of a closed subgroup, viewed as a closed subgroup
of the original ambient algebraic group. -/
@[expose]
public def ClosedSubgroup.identityComponentAmbient
    {G : Variety k} [AlgebraicGroup G] (H : ClosedSubgroup G) :
    ClosedSubgroup G :=
  let H0 := AlgebraicGroup.identityComponentClosedSubgroup H.carrierVariety
  letI : AlgebraicGroup H0.carrierVariety := H0.carrierAlgebraicGroup
  (H.inclusion.comp H0.inclusion).imageClosedSubgroup

end

section

variable {k : Type u} [Field k] [IsAlgClosed k]

omit [IsAlgClosed k] in
/-- A connected nontrivial closed subgroup has positive dimension. -/
public lemma connected_closedSubgroup_dimension_pos_of_ne_bot
    {G : Variety k} [AlgebraicGroup G] (C : ClosedSubgroup G)
    (hconn : _root_.IsConnected (C : Set (Variety.Point G)))
    (hne : C.toSubgroup ≠ ⊥) :
    0 < Variety.dimension C.carrierVariety := by
  by_contra hdim
  have hdim0 : Variety.dimension C.carrierVariety = 0 :=
    le_antisymm (not_lt.mp hdim) (by simp)
  have hfinitePoints : Finite (Variety.Point C.carrierVariety) :=
    (dimension_zero_iff_finite_points C.carrierVariety).mp hdim0
  let : Finite C.toSubgroup :=
    (Equiv.finite_iff C.pointEquiv).mp hfinitePoints
  let : T1Space (Variety.Point G) :=
    ⟨fun y ↦ Variety.isClosed_iff_isZariskiClosed.mpr
      (isZariskiClosed_singleton G y)⟩
  have hsub : (C : Set (Variety.Point G)).Subsingleton := by
    rw [← Set.not_nontrivial_iff]
    intro hnontrivial
    have hfiniteSet : Set.Finite (C : Set (Variety.Point G)) := Set.toFinite _
    exact hfiniteSet.not_infinite
      (hconn.isPreconnected.infinite_of_nontrivial hnontrivial)
  apply hne
  apply le_antisymm
  · intro x hx
    exact Subgroup.mem_bot.mpr (hsub hx C.toSubgroup.one_mem)
  · exact bot_le

end

section

variable {k : Type u} [Field k] [IsAlgClosed k]

/-- Ambient membership in the identity component of a closed subgroup. -/
public lemma ClosedSubgroup.mem_identityComponentAmbient_iff
    {G : Variety k} [AlgebraicGroup G]
    (H : ClosedSubgroup G) (x : Variety.Point G) :
    x ∈ H.identityComponentAmbient ↔
      ∃ y : Variety.Point H.carrierVariety,
        y ∈ AlgebraicGroup.identityComponent H.carrierVariety ∧
        H.inclusion.onPoints y = x := by
  let H0 := AlgebraicGroup.identityComponentClosedSubgroup H.carrierVariety
  letI : AlgebraicGroup H0.carrierVariety := H0.carrierAlgebraicGroup
  change x ∈ (H.inclusion.comp H0.inclusion).image ↔ _
  constructor
  · rintro ⟨z, rfl⟩
    exact ⟨H0.inclusion.onPoints z, (H0.pointEquiv z).property, rfl⟩
  · rintro ⟨y, hy, rfl⟩
    let z : Variety.Point H0.carrierVariety :=
      H0.pointEquiv.symm ⟨y, hy⟩
    exact ⟨z, by rfl⟩

end

section

variable {k : Type u} [Field k] [IsAlgClosed k]

/-- The ambient identity component of a closed subgroup is connected. -/
public lemma ClosedSubgroup.identityComponentAmbient_isConnected
    {G : Variety k} [AlgebraicGroup G] (H : ClosedSubgroup G) :
    _root_.IsConnected
      (H.identityComponentAmbient : Set (Variety.Point G)) := by
  let H0 := AlgebraicGroup.identityComponentClosedSubgroup H.carrierVariety
  letI : AlgebraicGroup H0.carrierVariety := H0.carrierAlgebraicGroup
  let q : AlgebraicGroup.Morphism H0.carrierVariety G :=
    H.inclusion.comp H0.inclusion
  have hsource : _root_.IsConnected
      (Set.univ : Set (Variety.Point H0.carrierVariety)) :=
    identityComponentClosedSubgroup_carrier_isConnected H.carrierVariety
  have himage := hsource.image q.onPoints
    q.toVariety.continuous.continuousOn
  change _root_.IsConnected (q.image : Set (Variety.Point G))
  rw [q.image_carrier]
  simpa [Set.image_univ, q, H0] using himage

end

section

variable {k : Type u} [Field k] [IsAlgClosed k]

/-- The ambient identity component is contained in its closed subgroup. -/
public lemma ClosedSubgroup.identityComponentAmbient_le
    {G : Variety k} [AlgebraicGroup G] (H : ClosedSubgroup G) :
    H.identityComponentAmbient ≤ H := by
  intro x hx
  have hx' := (ClosedSubgroup.mem_identityComponentAmbient_iff H x).mp hx
  rcases hx' with ⟨y, _, rfl⟩
  exact (H.pointEquiv y).property

end

section

variable {k : Type u} [Field k] [IsAlgClosed k]

/-- The ambient identity component is normal in its closed subgroup. -/
public lemma ClosedSubgroup.identityComponentAmbient_normal
    {G : Variety k} [AlgebraicGroup G] (H : ClosedSubgroup G) :
    (H.identityComponentAmbient.toSubgroup.subgroupOf H.toSubgroup).Normal := by
  let H0 := AlgebraicGroup.identityComponentClosedSubgroup H.carrierVariety
  let e : Variety.Point H.carrierVariety ≃* H.toSubgroup :=
    Equiv.mulEquiv H.pointEquiv
  have hEq :
      H.identityComponentAmbient.toSubgroup.subgroupOf H.toSubgroup =
        H0.toSubgroup.map e.toMonoidHom := by
    ext z
    constructor
    · intro hz
      have hz' :=
        (ClosedSubgroup.mem_identityComponentAmbient_iff H z.val).mp hz
      rcases hz' with ⟨y, hy, hyz⟩
      refine Subgroup.mem_map.mpr ⟨y, hy, ?_⟩
      apply Subtype.ext
      exact hyz
    · intro hz
      rcases Subgroup.mem_map.mp hz with ⟨y, hy, hyz⟩
      apply (ClosedSubgroup.mem_identityComponentAmbient_iff H z.val).mpr
      refine ⟨y, hy, ?_⟩
      exact congrArg Subtype.val hyz
  rw [hEq]
  exact Subgroup.Normal.map
    (AlgebraicGroup.identityComponentClosedSubgroup_isNormal H.carrierVariety)
    e.toMonoidHom e.surjective

end

section

variable {k : Type u} [Field k] [IsAlgClosed k]

/-- A closed subgroup and its ambient identity component have the same
dimension. -/
public lemma ClosedSubgroup.dimension_identityComponentAmbient
    {G : Variety k} [AlgebraicGroup G] (H : ClosedSubgroup G) :
    Variety.dimension H.identityComponentAmbient.carrierVariety =
      Variety.dimension H.carrierVariety := by
  let H0 := AlgebraicGroup.identityComponentClosedSubgroup H.carrierVariety
  letI : AlgebraicGroup H0.carrierVariety := H0.carrierAlgebraicGroup
  let q : AlgebraicGroup.Morphism H0.carrierVariety G :=
    H.inclusion.comp H0.inclusion
  have hqinj : Function.Injective q.onPoints :=
    H.inclusion_injective.comp H0.inclusion_injective
  let : Subsingleton q.kernelClosedSubgroup.toSubgroup := by
    constructor
    intro x y
    apply Subtype.ext
    apply hqinj
    have hx : q.onPoints x.val = 1 := x.property
    have hy : q.onPoints y.val = 1 := y.property
    rw [hx, hy]
  let : Subsingleton
      (Variety.Point q.kernelClosedSubgroup.carrierVariety) :=
    q.kernelClosedSubgroup.pointEquiv.subsingleton
  let : Finite (Variety.Point q.kernelClosedSubgroup.carrierVariety) :=
    Finite.of_subsingleton
  have hkerDim :
      Variety.dimension q.kernelClosedSubgroup.carrierVariety = 0 :=
    (dimension_zero_iff_finite_points q.kernelClosedSubgroup.carrierVariety).2 inferInstance
  have hdim := morphism_dimension_eq_kernel_add_image q
  change Variety.dimension q.imageClosedSubgroup.carrierVariety = _
  rw [hkerDim, zero_add] at hdim
  rw [← hdim]
  exact AlgebraicGroup.dimension_identityComponentClosedSubgroup H.carrierVariety

end

section

variable {k : Type u} [Field k] [IsAlgClosed k]

/-- A connected closed subgroup contained in `H` lies in the ambient identity
component of `H`. -/
public lemma connected_closedSubgroup_le_identityComponentAmbient
    {G : Variety k} [AlgebraicGroup G]
    (K H : ClosedSubgroup G)
    (hK : _root_.IsConnected (K : Set (Variety.Point G)))
    (hKH : K ≤ H) : K ≤ H.identityComponentAmbient := by
  let e := Variety.closedSubvarietyPointHomeomorph H.isZariskiClosed
  let f : {x : Variety.Point G // x ∈ K} →
      Variety.Point H.carrierVariety :=
    fun x ↦ e.symm ⟨x.1, hKH x.2⟩
  let : ConnectedSpace {x : Variety.Point G // x ∈ K} :=
    Subtype.connectedSpace hK
  have hf : Continuous f := by
    exact e.symm.continuous.comp
      (continuous_subtype_val.subtype_mk fun x ↦ hKH x.2)
  have hrange : _root_.IsConnected (Set.range f) := isConnected_range hf
  have hOne : (1 : Variety.Point H.carrierVariety) ∈ Set.range f := by
    refine ⟨⟨1, K.toSubgroup.one_mem⟩, ?_⟩
    apply H.inclusion_injective
    change (e (f ⟨1, K.toSubgroup.one_mem⟩)).val = 1
    simp [f]
  intro x hx
  apply (ClosedSubgroup.mem_identityComponentAmbient_iff H x).mpr
  let z : {x : Variety.Point G // x ∈ K} := ⟨x, hx⟩
  refine ⟨f z, ?_, ?_⟩
  · have hsubset := hrange.subset_connectedComponent hOne
    exact hsubset ⟨z, rfl⟩
  · change (e (f z)).val = x
    simp [f, z]

end

section

variable {k : Type u} [Field k] [IsAlgClosed k]

/-- Dimension is monotone when a connected closed subgroup is contained in an
arbitrary closed subgroup. -/
public lemma connected_closedSubgroup_dimension_le_of_le
    {G : Variety k} [AlgebraicGroup G]
    (K H : ClosedSubgroup G)
    (hK : _root_.IsConnected (K : Set (Variety.Point G)))
    (hKH : K ≤ H) :
    Variety.dimension K.carrierVariety ≤
      Variety.dimension H.carrierVariety := by
  have hKH0 := connected_closedSubgroup_le_identityComponentAmbient K H hK hKH
  have hH0connected := ClosedSubgroup.identityComponentAmbient_isConnected H
  have hdim : Variety.dimension K.carrierVariety ≤
      Variety.dimension H.identityComponentAmbient.carrierVariety := by
    by_cases hEq : K = H.identityComponentAmbient
    · rw [hEq]
    · exact (connected_closedSubgroup_dimension_lt_of_le_of_ne
        K H.identityComponentAmbient hKH0 hEq hK hH0connected).le
  rwa [ClosedSubgroup.dimension_identityComponentAmbient] at hdim

end

section

variable {k : Type u} [Field k] [IsAlgClosed k]

/-- If a connected subgroup properly extends `H°` and lies in `K`, then
`dim H < dim K`. -/
public lemma
    closedSubgroup_dimension_lt_of_identityComponentAmbient_lt_connected_le
    {G : Variety k} [AlgebraicGroup G]
    (H J K : ClosedSubgroup G)
    (hJ : _root_.IsConnected (J : Set (Variety.Point G)))
    (hH0J : H.identityComponentAmbient ≤ J)
    (hne : H.identityComponentAmbient ≠ J)
    (hJK : J ≤ K) :
    Variety.dimension H.carrierVariety <
      Variety.dimension K.carrierVariety := by
  have hH0connected := ClosedSubgroup.identityComponentAmbient_isConnected H
  have hstrict := connected_closedSubgroup_dimension_lt_of_le_of_ne
    H.identityComponentAmbient J hH0J hne hH0connected hJ
  have hle := connected_closedSubgroup_dimension_le_of_le J K hJ hJK
  rw [ClosedSubgroup.dimension_identityComponentAmbient] at hstrict
  exact hstrict.trans_le hle

end

section

variable {k : Type u} [Field k] [IsAlgClosed k]

/-- If the ambient identity component of `H` lies in `K` and `K` has no
larger dimension than `H`, then the identity components of `H` and `K` agree. -/
public lemma ClosedSubgroup.identityComponentAmbient_eq_of_le_of_dimension_le
    {G : Variety k} [AlgebraicGroup G]
    (H K : ClosedSubgroup G)
    (hle : H.identityComponentAmbient ≤ K)
    (hdim : Variety.dimension K.carrierVariety ≤
      Variety.dimension H.carrierVariety) :
    K.identityComponentAmbient = H.identityComponentAmbient := by
  have hHconn : _root_.IsConnected
      (H.identityComponentAmbient : Set (Variety.Point G)) :=
    ClosedSubgroup.identityComponentAmbient_isConnected H
  have hKH : H.identityComponentAmbient ≤ K.identityComponentAmbient :=
    connected_closedSubgroup_le_identityComponentAmbient
      H.identityComponentAmbient K hHconn hle
  have hdimHK : Variety.dimension H.carrierVariety =
      Variety.dimension K.carrierVariety := by
    apply le_antisymm
    · calc
        Variety.dimension H.carrierVariety =
            Variety.dimension H.identityComponentAmbient.carrierVariety :=
          (ClosedSubgroup.dimension_identityComponentAmbient H).symm
        _ ≤ Variety.dimension K.carrierVariety :=
          connected_closedSubgroup_dimension_le_of_le
            H.identityComponentAmbient K hHconn hle
    · exact hdim
  have hKH' : K.identityComponentAmbient ≤ H.identityComponentAmbient := by
    by_contra hnot
    have hne : H.identityComponentAmbient ≠ K.identityComponentAmbient := by
      intro heq
      apply hnot
      simpa only [heq] using
        (show K.identityComponentAmbient ≤ K.identityComponentAmbient from
          fun x hx => hx)
    have hlt := closedSubgroup_dimension_lt_of_identityComponentAmbient_lt_connected_le
      H K.identityComponentAmbient K
      (ClosedSubgroup.identityComponentAmbient_isConnected K) hKH hne
      (ClosedSubgroup.identityComponentAmbient_le K)
    exact (not_lt_of_ge hdimHK.symm.le) hlt
  apply SetLike.coe_injective
  exact Set.Subset.antisymm hKH' hKH

end

section

variable {k : Type u} [Field k] [IsAlgClosed k]

/-- The ambient identity component of a normal closed subgroup is normal in
the ambient algebraic group. -/
public theorem ClosedSubgroup.identityComponentAmbient_normal_of_normal
    {G : Variety k} [AlgebraicGroup G]
    (H : ClosedSubgroup G) (hH : H.toSubgroup.Normal) :
    H.identityComponentAmbient.toSubgroup.Normal := by
  let I := H.identityComponentAmbient
  have hIconn : _root_.IsConnected (I : Set (Variety.Point G)) :=
    ClosedSubgroup.identityComponentAmbient_isConnected H
  constructor
  intro x hx g
  have hConjConn : _root_.IsConnected
      (I.conjugate g : Set (Variety.Point G)) := by
    have hcarrier : (I.conjugate g : Set (Variety.Point G)) =
        (AlgebraicGroup.conjugationByMorphism G g).toFun ''
          (I : Set (Variety.Point G)) := by
      ext y
      constructor
      · intro hy
        have hy' := (ClosedSubgroup.mem_conjugate_iff I g y).mp hy
        refine ⟨g⁻¹ * y * g, hy', ?_⟩
        rw [AlgebraicGroup.conjugationByMorphism_apply]
        simp [mul_assoc]
      · rintro ⟨z, hz, rfl⟩
        change z ∈ I.toSubgroup at hz
        apply (ClosedSubgroup.mem_conjugate_iff I g _).mpr
        rw [AlgebraicGroup.conjugationByMorphism_apply]
        simpa [mul_assoc] using hz
    rw [hcarrier]
    exact hIconn.image _
      (AlgebraicGroup.conjugationByMorphism G g).continuous.continuousOn
  have hConjH : I.conjugate g ≤ H := by
    intro y hy
    have hyI := (ClosedSubgroup.mem_conjugate_iff I g y).mp hy
    have hyH : g⁻¹ * y * g ∈ H :=
      (ClosedSubgroup.identityComponentAmbient_le H) hyI
    have hconj := hH.conj_mem (g⁻¹ * y * g) hyH g
    change y ∈ H.toSubgroup
    simpa [mul_assoc] using hconj
  have hConjI : I.conjugate g ≤ I :=
    connected_closedSubgroup_le_identityComponentAmbient
      (I.conjugate g) H hConjConn hConjH
  apply hConjI
  apply (ClosedSubgroup.mem_conjugate_iff I g _).mpr
  simpa [mul_assoc] using hx

end

end Theory.AlgebraicGroup
