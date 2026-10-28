module

public import Theory.AlgebraicGroup.Automorphisms.Steinberg
public import Theory.AlgebraicGroup.Automorphisms.FiniteKernel
public import Theory.AlgebraicGroup.Automorphisms.ReductiveNormalizerEquivariance
public import Theory.AlgebraicGroup.ClosedSubgroup.Normalizer
public import Theory.AlgebraicGroup.Morphism.Connected
public import Theory.AlgebraicGroup.Morphism.Solvable
public import Theory.AlgebraicGroup.Parabolic.Defs
public import Theory.AlgebraicGroup.Parabolic.Transitivity
public import Theory.AlgebraicGroup.Unipotent.Radical

/-!
# Equivariant descent for Borel--Tits

The connected radical is characterized by maximality among connected normal
unipotent closed subgroups, also when the ambient subgroup is disconnected.
For quotient lifting, connectedness follows by comparing a preimage with its
identity component, and unipotence follows from functorial Jordan decomposition.
All quotient maps below are actual algebraic-group morphisms. Borel conjugacy
transfers lifted parabolics from a parabolic source to the ambient group.
Exact normalizer equivariance holds for invariant unipotent subgroups under
reductive Steinberg maps, without point-injectivity. Connected kernels are
automatically invariant under an equivariant surjective endomorphism, so full
preimages preserve invariance. No finite-generation or quotient-existence
assertion is implicit in these transfer statements.

Source: GLS, volume 3, §§1.2, 1.6, 2.1 and the proof of Theorem 3.1.3.
-/

universe u
namespace Theory.AlgebraicGroup.BorelTitsDescent
variable {k : Type u} [Field k] [IsAlgClosed k]

set_option linter.unusedSectionVars false

/-- The connected unipotent radical of a possibly disconnected ambient subgroup.
Unlike `IsUnipotentRadicalOf`, maximality here requires connectedness. -/
@[expose] public def IsConnectedUnipotentRadicalOf
    {G : Variety k} [AlgebraicGroup G] (H U : ClosedSubgroup G) : Prop :=
  U ≤ H ∧ _root_.IsConnected (U : Set (Variety.Point G)) ∧
    IsUnipotentAlgebraicGroup U.carrierVariety ∧
    (∀ h, h ∈ H → ∀ x, x ∈ U → h * x * h⁻¹ ∈ U) ∧
    ∀ V : ClosedSubgroup G, V ≤ H →
      _root_.IsConnected (V : Set (Variety.Point G)) →
      IsUnipotentAlgebraicGroup V.carrierVariety →
      (∀ h, h ∈ H → ∀ x, x ∈ V → h * x * h⁻¹ ∈ V) → V ≤ U

/-- Relative normality gives the normalizer inclusion used in the radical chain. -/
public theorem radical_normalizer_le
    {G : Variety k} [AlgebraicGroup G] {H U : ClosedSubgroup G}
    (hU : IsConnectedUnipotentRadicalOf H U) : H ≤ U.normalizer := by
  intro h hh
  change h ∈ Subgroup.normalizer (U.toSubgroup : Set (Variety.Point G))
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · exact hU.2.2.2.1 h hh x
  · intro hx
    have hm := hU.2.2.2.1 h⁻¹ (H.toSubgroup.inv_mem hh)
      (h * x * h⁻¹) hx
    change x ∈ U
    simpa [mul_assoc] using hm

/-- Connected radicals are unique, including for disconnected ambient groups. -/
public theorem connected_radical_unique
    {G : Variety k} [AlgebraicGroup G] {H U V : ClosedSubgroup G}
    (hU : IsConnectedUnipotentRadicalOf H U)
    (hV : IsConnectedUnipotentRadicalOf H V) : U = V := by
  apply SetLike.coe_injective
  exact Set.Subset.antisymm
    (hV.2.2.2.2 U hU.1 hU.2.1 hU.2.2.1 hU.2.2.2.1)
    (hU.2.2.2.2 V hV.1 hV.2.1 hV.2.2.1 hV.2.2.2.1)

/-- A connected kernel and a connected target subgroup have connected preimage. -/
public theorem preimage_connected
    {G Q : Variety k} [AlgebraicGroup G] [AlgebraicGroup Q]
    (q : AlgebraicGroup.Morphism G Q) (hq : Function.Surjective q.onPoints)
    (hker : _root_.IsConnected
      (q.kernelClosedSubgroup : Set (Variety.Point G)))
    (S : ClosedSubgroup Q) (hS : _root_.IsConnected (S : Set (Variety.Point Q))) :
    _root_.IsConnected (q.closedSubgroupPreimage S : Set (Variety.Point G)) := by
  let P := q.closedSubgroupPreimage S
  let I := P.identityComponentAmbient
  have hKI : q.kernelClosedSubgroup ≤ I :=
    connected_closedSubgroup_le_identityComponentAmbient _ P hker (by
      intro x hx
      change q.onPoints x ∈ S.toSubgroup
      change q.onPoints x = 1 at hx
      rw [hx]
      exact S.toSubgroup.one_mem)
  have hImage := q.closedSubgroupPreimage_identityComponent_image_eq hq S hS
  have hPI : P ≤ I := by
    intro x hx
    have hximage : q.onPoints x ∈ (q.comp I.inclusion).imageClosedSubgroup := by
      rw [hImage]
      exact hx
    obtain ⟨y, hy⟩ := hximage
    have hxy : x * (I.inclusion.onPoints y)⁻¹ ∈ q.kernelClosedSubgroup := by
      change q.onPoints (x * (I.inclusion.onPoints y)⁻¹) = 1
      change q.onPoints (I.inclusion.onPoints y) = q.onPoints x at hy
      simp only [map_mul, map_inv, hy, mul_inv_cancel]
    have hm := I.toSubgroup.mul_mem (hKI hxy) (I.pointEquiv y).property
    change x * (I.inclusion.onPoints y)⁻¹ * I.inclusion.onPoints y ∈ I at hm
    simpa [mul_assoc] using hm
  have heq : P = I := SetLike.coe_injective
    (Set.Subset.antisymm hPI P.identityComponentAmbient_le)
  rw [show q.closedSubgroupPreimage S = I from heq]
  exact P.identityComponentAmbient_isConnected

/-- Unipotence is closed under extensions by unipotent kernels. -/
public theorem unipotent_of_kernel_and_target
    {G Q : Variety k} [AlgebraicGroup G] [AlgebraicGroup Q]
    (q : AlgebraicGroup.Morphism G Q)
    (hker : IsUnipotentAlgebraicGroup q.kernelClosedSubgroup.carrierVariety)
    (hQ : IsUnipotentAlgebraicGroup Q) : IsUnipotentAlgebraicGroup G := by
  intro x
  let d := jordanDecomposition x
  let t : JordanDecomposition (q.onPoints x) :=
    { semisimplePart := 1
      unipotentPart := q.onPoints x
      eq_mul := by simp
      commute := Commute.one_left _
      semisimple := one_isSemisimpleElement Q
      unipotent := hQ _ }
  have hs : q.onPoints d.semisimplePart = 1 :=
    (q.maps_jordanComponents x d t).1.symm
  have hsK : d.semisimplePart ∈ q.kernelClosedSubgroup := hs
  have hu : IsUnipotentElement G d.semisimplePart :=
    (closedSubgroup_unipotentElement_iff q.kernelClosedSubgroup hsK).mpr (hker _)
  have heq := semisimple_unipotent_eq_one d.semisimplePart d.semisimple hu
  rw [d.eq_mul, heq, one_mul]
  exact d.unipotent

/-- Unipotent target subgroups lift through unipotent kernels. -/
public theorem preimage_unipotent
    {G Q : Variety k} [AlgebraicGroup G] [AlgebraicGroup Q]
    (q : AlgebraicGroup.Morphism G Q)
    (hker : IsUnipotentAlgebraicGroup q.kernelClosedSubgroup.carrierVariety)
    (S : ClosedSubgroup Q) (hS : IsUnipotentAlgebraicGroup S.carrierVariety) :
    IsUnipotentAlgebraicGroup (q.closedSubgroupPreimage S).carrierVariety := by
  let P := q.closedSubgroupPreimage S
  let : AlgebraicGroup P.carrierVariety := P.carrierAlgebraicGroup
  let r := q.preimageRestriction S
  let : AlgebraicGroup r.kernelClosedSubgroup.carrierVariety :=
    r.kernelClosedSubgroup.carrierAlgebraicGroup
  apply unipotent_of_kernel_and_target r _ hS
  intro x
  let z := r.kernelClosedSubgroup.inclusion.onPoints x
  have hz : r.onPoints z = 1 := (r.kernelClosedSubgroup.pointEquiv x).property
  have hzq : P.inclusion.onPoints z ∈ q.kernelClosedSubgroup := by
    change q.onPoints (P.inclusion.onPoints z) = 1
    rw [← q.preimageRestriction_inclusion_apply S]
    change S.inclusion.onPoints (r.onPoints z) = 1
    rw [hz, map_one]
  have huG := (closedSubgroup_unipotentElement_iff q.kernelClosedSubgroup hzq).mpr
    (hker _)
  have huP : IsUnipotentElement P.carrierVariety z := by
    simpa using (closedSubgroup_unipotentElement_iff P (P.pointEquiv z).property).mp huG
  have huK := (closedSubgroup_unipotentElement_iff r.kernelClosedSubgroup
    (r.kernelClosedSubgroup.pointEquiv x).property).mp huP
  simpa [z] using huK

/-- The full connected-unipotent-normal lifting statement. -/
public theorem preimage_connected_unipotent_normal
    {G Q : Variety k} [AlgebraicGroup G] [AlgebraicGroup Q]
    (q : AlgebraicGroup.Morphism G Q) (hq : Function.Surjective q.onPoints)
    (hkerC : _root_.IsConnected (q.kernelClosedSubgroup : Set (Variety.Point G)))
    (hkerU : IsUnipotentAlgebraicGroup q.kernelClosedSubgroup.carrierVariety)
    (S : ClosedSubgroup Q) (hSC : _root_.IsConnected (S : Set (Variety.Point Q)))
    (hSU : IsUnipotentAlgebraicGroup S.carrierVariety) (hSN : S.toSubgroup.Normal) :
    _root_.IsConnected (q.closedSubgroupPreimage S : Set (Variety.Point G)) ∧
      IsUnipotentAlgebraicGroup (q.closedSubgroupPreimage S).carrierVariety ∧
      (q.closedSubgroupPreimage S).toSubgroup.Normal :=
  ⟨preimage_connected q hq hkerC S hSC, preimage_unipotent q hkerU S hSU,
    q.closedSubgroupPreimage_normal hSN⟩

/-- Equivariance preserves stability of full preimages. -/
public theorem preimage_stable
    {G Q : Variety k} [AlgebraicGroup G] [AlgebraicGroup Q]
    (q : AlgebraicGroup.Morphism G Q)
    (sigma : AlgebraicGroup.Morphism G G) (tau : AlgebraicGroup.Morphism Q Q)
    (heq : ∀ x, q.onPoints (sigma.onPoints x) = tau.onPoints (q.onPoints x))
    (S : ClosedSubgroup Q) (hS : ∀ x, x ∈ S → tau.onPoints x ∈ S) :
    ∀ x, x ∈ q.closedSubgroupPreimage S →
      sigma.onPoints x ∈ q.closedSubgroupPreimage S := by
  intro x hx
  change q.onPoints (sigma.onPoints x) ∈ S
  rw [heq]
  exact hS _ hx

/-- A nontrivial connected kernel strictly decreases dimension. -/
public theorem quotient_dimension_lt
    {G Q : Variety k} [AlgebraicGroup G] [AlgebraicGroup Q]
    (q : AlgebraicGroup.Morphism G Q) (hq : Function.Surjective q.onPoints)
    (hker : _root_.IsConnected (q.kernelClosedSubgroup : Set (Variety.Point G)))
    (hne : q.kernel ≠ ⊥) : Variety.dimension Q < Variety.dimension G := by
  have himage : Variety.dimension q.imageClosedSubgroup.carrierVariety =
      Variety.dimension Q := by
    apply (closedSubgroup_dimension_eq_iff_contains_identityComponent Q _).2
    intro x _
    exact hq x
  have hpos := connected_closedSubgroup_dimension_pos_of_ne_bot
    q.kernelClosedSubgroup hker hne
  rw [morphism_dimension_eq_kernel_add_image q, himage]
  simpa only [zero_add] using
    (Cardinal.add_lt_add_iff_of_right_lt_aleph0
      (variety_dimension_lt_aleph0 Q)).mpr hpos

private theorem carrier_connected
    {G : Variety k} [AlgebraicGroup G] (H : ClosedSubgroup G)
    (hH : _root_.IsConnected (H : Set (Variety.Point G))) :
    Variety.IsConnected H.carrierVariety := by
  let e := Variety.closedSubvarietyPointHomeomorph H.isZariskiClosed
  let : ConnectedSpace {x : Variety.Point G // x ∈ (H : Set (Variety.Point G))} :=
    Subtype.connectedSpace hH
  let : ConnectedSpace (Variety.Point H.carrierVariety) :=
    e.connectedSpace_iff.mpr inferInstance
  exact connectedSpace_iff_univ.mp inferInstance

/-- Stability of a connected subgroup under a surjective endomorphism is
already invariance: the restricted kernel is finite, so dimensions agree. -/
public theorem connected_stable_is_invariant
    {G : Variety k} [AlgebraicGroup G]
    (sigma : AlgebraicGroup.Morphism G G) (hsigma : Function.Surjective sigma.onPoints)
    (H : ClosedSubgroup G) (hH : _root_.IsConnected (H : Set (Variety.Point G)))
    (hstable : ∀ x, x ∈ H → sigma.onPoints x ∈ H) :
    sigma.onPoints '' (H : Set (Variety.Point G)) = H := by
  let r := (sigma.comp H.inclusion).codRestrictClosedSubgroup H
    (fun x => hstable _ (H.pointEquiv x).property)
  have hr (x) : H.inclusion.onPoints (r.onPoints x) =
      sigma.onPoints (H.inclusion.onPoints x) :=
    Morphism.codRestrictClosedSubgroup_inclusion_apply _ _ _ _
  let : Finite sigma.kernel := surjectiveEndomorphism_kernel_finite sigma hsigma
  let j : r.kernel → sigma.kernel := fun x => ⟨H.inclusion.onPoints x, by
    change sigma.onPoints (H.inclusion.onPoints x) = 1
    rw [← hr, show r.onPoints x = 1 from x.property, map_one]⟩
  have hj : Function.Injective j := by
    intro x y hxy
    apply Subtype.ext
    apply H.inclusion_injective
    exact congrArg (fun z : sigma.kernel => (z : Variety.Point G)) hxy
  have hrsurj := connected_endomorphism_surjective_of_finiteKernel r
    (carrier_connected H hH) (Finite.of_injective j hj)
  apply Set.Subset.antisymm
  · rintro _ ⟨x, hx, rfl⟩
    exact hstable x hx
  · intro x hx
    obtain ⟨y, hy⟩ := hrsurj (H.pointEquiv.symm ⟨x, hx⟩)
    refine ⟨H.inclusion.onPoints y, (H.pointEquiv y).property, ?_⟩
    rw [← hr, hy]
    exact congrArg Subtype.val (H.pointEquiv.apply_symm_apply ⟨x, hx⟩)

/-- The normalizer of an invariant subgroup is stable under any endomorphism. -/
public theorem normalizer_stable
    {G : Variety k} [AlgebraicGroup G]
    (sigma : AlgebraicGroup.Morphism G G) (X : ClosedSubgroup G)
    (hX : sigma.onPoints '' (X : Set (Variety.Point G)) = X) :
    ∀ x, x ∈ X.normalizer → sigma.onPoints x ∈ X.normalizer := by
  have hmap : X.toSubgroup.map sigma.onPoints = X.toSubgroup :=
    SetLike.coe_injective hX
  intro x hx
  have hm := Subgroup.le_normalizer_map (H := X.toSubgroup) sigma.onPoints
    (Subgroup.mem_map_of_mem sigma.onPoints hx)
  rwa [hmap] at hm

/-- Point-bijective endomorphisms preserve normalizers exactly. -/
public theorem normalizer_invariant_of_bijective
    {G : Variety k} [AlgebraicGroup G]
    (sigma : AlgebraicGroup.Morphism G G) (hsigma : Function.Bijective sigma.onPoints)
    (X : ClosedSubgroup G)
    (hX : sigma.onPoints '' (X : Set (Variety.Point G)) = X) :
    sigma.onPoints '' (X.normalizer : Set (Variety.Point G)) = X.normalizer := by
  have hmap : X.toSubgroup.map sigma.onPoints = X.toSubgroup :=
    SetLike.coe_injective hX
  have hm := Subgroup.map_normalizer_eq_of_bijective X.toSubgroup hsigma
  rw [hmap] at hm
  exact congrArg (fun S : Subgroup (Variety.Point G) => (S : Set (Variety.Point G))) hm

/-- A surjective endomorphism preserves the connected unipotent radical of
any invariant closed subgroup, even if that subgroup is disconnected. -/
public theorem connected_radical_invariant
    {G : Variety k} [AlgebraicGroup G]
    (sigma : AlgebraicGroup.Morphism G G) (hsigma : Function.Surjective sigma.onPoints)
    {H U : ClosedSubgroup G}
    (hH : sigma.onPoints '' (H : Set (Variety.Point G)) = H)
    (hU : IsConnectedUnipotentRadicalOf H U) :
    sigma.onPoints '' (U : Set (Variety.Point G)) = U := by
  let f := sigma.comp U.inclusion
  let V := f.imageClosedSubgroup
  have hmem (x : Variety.Point G) : x ∈ V ↔
      ∃ y, y ∈ U ∧ sigma.onPoints y = x := by
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨U.inclusion.onPoints y, (U.pointEquiv y).property, rfl⟩
    · rintro ⟨y, hy, rfl⟩
      exact ⟨U.pointEquiv.symm ⟨y, hy⟩,
        congrArg sigma.onPoints (congrArg Subtype.val
          (U.pointEquiv.apply_symm_apply ⟨y, hy⟩))⟩
  have hVH : V ≤ H := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := (hmem x).mp hx
    rw [← hH]
    exact ⟨y, hU.1 hy, rfl⟩
  have hVC := f.imageClosedSubgroup_isConnected (carrier_connected U hU.2.1)
  have hVU : IsUnipotentAlgebraicGroup V.carrierVariety := by
    obtain ⟨r, hr, _, _⟩ := f.closedImageProjection_exists
    exact hU.2.2.1.of_surjective r hr
  have hVN : ∀ h, h ∈ H → ∀ x, x ∈ V → h * x * h⁻¹ ∈ V := by
    intro h hh x hx
    change h ∈ (H : Set (Variety.Point G)) at hh
    rw [← hH] at hh
    obtain ⟨a, ha, rfl⟩ := hh
    obtain ⟨b, hb, rfl⟩ := (hmem x).mp hx
    apply (hmem _).mpr
    exact ⟨a * b * a⁻¹, hU.2.2.2.1 a ha b hb, by simp only [map_mul, map_inv]⟩
  have hVUle := hU.2.2.2.2 V hVH hVC hVU hVN
  apply connected_stable_is_invariant sigma hsigma U hU.2.1
  intro x hx
  exact hVUle ((hmem _).mpr ⟨x, hx, rfl⟩)

/-- Every closed subgroup has a connected unipotent radical in the ambient group. -/
public theorem exists_connected_radical
    {G : Variety k} [AlgebraicGroup G] (H : ClosedSubgroup G) :
    ∃ U : ClosedSubgroup G, IsConnectedUnipotentRadicalOf H U := by
  obtain ⟨W, hWN, hWC, hWU, hWmax⟩ :=
    exists_ambient_unipotent_radical (G := H.carrierVariety)
  let : AlgebraicGroup W.carrierVariety := W.carrierAlgebraicGroup
  let f := H.inclusion.comp W.inclusion
  let U := f.imageClosedSubgroup
  have hmem (x : Variety.Point G) : x ∈ U ↔
      ∃ y, y ∈ W ∧ H.inclusion.onPoints y = x := by
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨W.inclusion.onPoints y, (W.pointEquiv y).property, rfl⟩
    · rintro ⟨y, hy, rfl⟩
      exact ⟨W.pointEquiv.symm ⟨y, hy⟩,
        congrArg H.inclusion.onPoints (congrArg Subtype.val
          (W.pointEquiv.apply_symm_apply ⟨y, hy⟩))⟩
  have hUH : U ≤ H := by
    intro x hx
    obtain ⟨y, _, rfl⟩ := (hmem x).mp hx
    exact (H.pointEquiv y).property
  have hUC := f.imageClosedSubgroup_isConnected (carrier_connected W hWC)
  have hUU : IsUnipotentAlgebraicGroup U.carrierVariety := by
    obtain ⟨r, hr, _, _⟩ := f.closedImageProjection_exists
    exact hWU.of_surjective r hr
  refine ⟨U, hUH, hUC, hUU, ?_, ?_⟩
  · intro h hh x hx
    obtain ⟨y, hy, rfl⟩ := (hmem x).mp hx
    let a := H.pointEquiv.symm ⟨h, hh⟩
    have ha : H.inclusion.onPoints a = h :=
      congrArg Subtype.val (H.pointEquiv.apply_symm_apply ⟨h, hh⟩)
    apply (hmem _).mpr
    refine ⟨a * y * a⁻¹, hWN.conj_mem y hy a, ?_⟩
    simp only [map_mul, map_inv, ha]
  · intro V hVH hVC hVU hVN
    let j := V.inclusion.codRestrictClosedSubgroup H
      (fun x => hVH (V.pointEquiv x).property)
    let L := j.imageClosedSubgroup
    let : AlgebraicGroup L.carrierVariety := L.carrierAlgebraicGroup
    have hj (x) : H.inclusion.onPoints (j.onPoints x) = V.inclusion.onPoints x :=
      Morphism.codRestrictClosedSubgroup_inclusion_apply _ _ _ _
    have hL (x : Variety.Point H.carrierVariety) :
        x ∈ L ↔ H.inclusion.onPoints x ∈ V := by
      constructor
      · rintro ⟨y, rfl⟩
        rw [hj]
        exact (V.pointEquiv y).property
      · intro hx
        refine ⟨V.pointEquiv.symm ⟨H.inclusion.onPoints x, hx⟩, ?_⟩
        apply H.inclusion_injective
        rw [hj]
        exact congrArg Subtype.val
          (V.pointEquiv.apply_symm_apply ⟨H.inclusion.onPoints x, hx⟩)
    have hLN : L.toSubgroup.Normal := by
      constructor
      intro x hx g
      apply (hL _).mpr
      simp only [map_mul, map_inv]
      exact hVN _ (H.pointEquiv g).property _ ((hL x).mp hx)
    have hLC := j.imageClosedSubgroup_isConnected (carrier_connected V hVC)
    have hLU : IsUnipotentAlgebraicGroup L.carrierVariety := by
      obtain ⟨r, hr, _, _⟩ := j.closedImageProjection_exists
      exact hVU.of_surjective r hr
    have hLW := hWmax L hLN hLC hLU
    intro x hx
    let y := H.pointEquiv.symm ⟨x, hVH hx⟩
    have hy : H.inclusion.onPoints y = x :=
      congrArg Subtype.val (H.pointEquiv.apply_symm_apply ⟨x, hVH hx⟩)
    apply (hmem x).mpr
    refine ⟨y, hLW ((hL y).mpr ?_), hy⟩
    rwa [hy]

/-- The complete radical-chain step for a point-bijective Steinberg map. -/
public theorem invariant_normalizer_radical_of_bijective
    {G : Variety k} [AlgebraicGroup G]
    (sigma : AlgebraicGroup.Morphism G G)
    (hsigma : IsAlgebraicSteinbergEndomorphism sigma)
    (hinj : Function.Injective sigma.onPoints)
    (X : ClosedSubgroup G)
    (hX : sigma.onPoints '' (X : Set (Variety.Point G)) = X) :
    sigma.onPoints '' (X.normalizer : Set (Variety.Point G)) = X.normalizer ∧
      ∃ U : ClosedSubgroup G, IsConnectedUnipotentRadicalOf X.normalizer U ∧
        sigma.onPoints '' (U : Set (Variety.Point G)) = U ∧
        X.normalizer ≤ U.normalizer := by
  have hN := normalizer_invariant_of_bijective sigma ⟨hinj, hsigma.1⟩ X hX
  obtain ⟨U, hU⟩ := exists_connected_radical X.normalizer
  exact ⟨hN, U, hU, connected_radical_invariant sigma hsigma.1 hN hU,
    radical_normalizer_le hU⟩

/-- Semisimple Steinberg maps are point-bijective, so no extra injectivity
input is required in the semisimple case. -/
public theorem invariant_normalizer_radical_of_semisimple
    {G : Variety k} [AlgebraicGroup G]
    (hG : IsSemisimpleAlgebraicGroup G)
    (sigma : AlgebraicGroup.Morphism G G)
    (hsigma : IsAlgebraicSteinbergEndomorphism sigma)
    (X : ClosedSubgroup G)
    (hX : sigma.onPoints '' (X : Set (Variety.Point G)) = X) :
    sigma.onPoints '' (X.normalizer : Set (Variety.Point G)) = X.normalizer ∧
      ∃ U : ClosedSubgroup G, IsConnectedUnipotentRadicalOf X.normalizer U ∧
        sigma.onPoints '' (U : Set (Variety.Point G)) = U ∧
        X.normalizer ≤ U.normalizer := by
  obtain ⟨a, ha, _⟩ :=
    existsUnique_algebraicAutomorphism_realizing_surjective_endomorphism
      sigma hG hsigma.1
  apply invariant_normalizer_radical_of_bijective sigma hsigma _ X hX
  intro x y hxy
  apply a.injective
  exact (ha x).trans (hxy.trans (ha y).symm)

/-- The radical-chain step for the connected reductive group in GLS3, Theorem
3.1.3. The normalizer may be disconnected; its radical is maximal only among
connected normal unipotent subgroups. No point-injectivity is assumed. -/
public theorem invariant_normalizer_radical_of_reductive
    {G : Variety k} [AlgebraicGroup G]
    (hG : IsReductiveAlgebraicGroup G)
    (sigma : AlgebraicGroup.Morphism G G)
    (hsigma : IsAlgebraicSteinbergEndomorphism sigma)
    (X : ClosedSubgroup G)
    (hXU : IsUnipotentAlgebraicGroup X.carrierVariety)
    (hX : sigma.onPoints '' (X : Set (Variety.Point G)) = X) :
    sigma.onPoints '' (X.normalizer : Set (Variety.Point G)) = X.normalizer ∧
      ∃ U : ClosedSubgroup G, IsConnectedUnipotentRadicalOf X.normalizer U ∧
        sigma.onPoints '' (U : Set (Variety.Point G)) = U ∧
        X.normalizer ≤ U.normalizer := by
  have hN := steinbergReductiveEndomorphism_image_normalizer_eq hG sigma hsigma X hXU hX
  obtain ⟨U, hU⟩ := exists_connected_radical X.normalizer
  exact ⟨hN, U, hU, connected_radical_invariant sigma hsigma.1 hN hU,
    radical_normalizer_le hU⟩

/-- Exact invariance of a full preimage. Kernel invariance is stated explicitly;
surjectivity alone would not justify lifting an inverse iterate. -/
public theorem preimage_invariant
    {G Q : Variety k} [AlgebraicGroup G] [AlgebraicGroup Q]
    (q : AlgebraicGroup.Morphism G Q) (hq : Function.Surjective q.onPoints)
    (sigma : AlgebraicGroup.Morphism G G) (tau : AlgebraicGroup.Morphism Q Q)
    (heq : ∀ x, q.onPoints (sigma.onPoints x) = tau.onPoints (q.onPoints x))
    (hker : sigma.onPoints '' (q.kernel : Set (Variety.Point G)) = q.kernel)
    (S : ClosedSubgroup Q)
    (hS : tau.onPoints '' (S : Set (Variety.Point Q)) = S) :
    sigma.onPoints '' (q.closedSubgroupPreimage S : Set (Variety.Point G)) =
      q.closedSubgroupPreimage S := by
  apply Set.Subset.antisymm
  · rintro _ ⟨x, hx, rfl⟩
    apply preimage_stable q sigma tau heq S _ x hx
    intro y hy
    change tau.onPoints y ∈ (S : Set (Variety.Point Q))
    rw [← hS]
    exact ⟨y, hy, rfl⟩
  · intro x hx
    change q.onPoints x ∈ (S : Set (Variety.Point Q)) at hx
    rw [← hS] at hx
    obtain ⟨s, hs, hsx⟩ := hx
    obtain ⟨y, hy⟩ := hq s
    have hk : x * (sigma.onPoints y)⁻¹ ∈ (q.kernel : Set (Variety.Point G)) := by
      change q.onPoints (x * (sigma.onPoints y)⁻¹) = 1
      simp only [map_mul, map_inv, heq, hy, hsx, mul_inv_cancel]
    rw [← hker] at hk
    obtain ⟨z, hz, hzval⟩ := hk
    refine ⟨z * y, ?_, ?_⟩
    · change q.onPoints (z * y) ∈ (S : Set (Variety.Point Q))
      change q.onPoints z = 1 at hz
      simpa only [map_mul, hz, one_mul, hy] using hs
    · rw [map_mul, hzval]
      simp only [mul_assoc, inv_mul_cancel, mul_one]

/-- In an equivariant quotient with connected kernel, exact kernel invariance
follows from surjectivity of the source endomorphism. Thus full preimages of
invariant subgroups are invariant without an additional kernel premise. -/
public theorem preimage_invariant_of_connected_kernel
    {G Q : Variety k} [AlgebraicGroup G] [AlgebraicGroup Q]
    (q : AlgebraicGroup.Morphism G Q) (hq : Function.Surjective q.onPoints)
    (hkerC : _root_.IsConnected (q.kernelClosedSubgroup : Set (Variety.Point G)))
    (sigma : AlgebraicGroup.Morphism G G) (hsigma : Function.Surjective sigma.onPoints)
    (tau : AlgebraicGroup.Morphism Q Q)
    (heq : ∀ x, q.onPoints (sigma.onPoints x) = tau.onPoints (q.onPoints x))
    (S : ClosedSubgroup Q)
    (hS : tau.onPoints '' (S : Set (Variety.Point Q)) = S) :
    sigma.onPoints '' (q.closedSubgroupPreimage S : Set (Variety.Point G)) =
      q.closedSubgroupPreimage S := by
  apply preimage_invariant q hq sigma tau heq _ S hS
  apply connected_stable_is_invariant sigma hsigma q.kernelClosedSubgroup hkerC
  intro x hx
  change q.onPoints (sigma.onPoints x) = 1
  change q.onPoints x = 1 at hx
  rw [heq, hx, map_one]

/-- Borel subgroups lift through surjective morphisms with connected solvable
kernel. This proof uses maximality, not Borel conjugacy. -/
public theorem preimage_borel
    {G Q : Variety k} [AlgebraicGroup G] [AlgebraicGroup Q]
    (q : AlgebraicGroup.Morphism G Q) (hq : Function.Surjective q.onPoints)
    (hkerC : _root_.IsConnected (q.kernelClosedSubgroup : Set (Variety.Point G)))
    (hkerS : Group.IsSolvable q.kernel)
    (B : ClosedSubgroup Q) (hB : IsBorelSubgroup B) :
    IsBorelSubgroup (q.closedSubgroupPreimage B) := by
  let P := q.closedSubgroupPreimage B
  refine ⟨preimage_connected q hq hkerC B hB.connected,
    q.closedSubgroupPreimage_isSolvable_of_kernel B hB.solvable
      (q.preimageRestriction_kernel_isSolvable_of_kernel B hkerS), ?_⟩
  intro S hSC hSS hPS
  let r := q.comp S.inclusion
  let T := r.imageClosedSubgroup
  have hTC := r.imageClosedSubgroup_isConnected (carrier_connected S hSC)
  have hTS := r.imageClosedSubgroup_isSolvable hSS
  have hBT : B ≤ T := by
    intro x hx
    obtain ⟨y, hy⟩ := hq x
    have hyP : y ∈ P := by change q.onPoints y ∈ B; rwa [hy]
    exact ⟨S.pointEquiv.symm ⟨y, hPS hyP⟩, (congrArg q.onPoints
      (congrArg Subtype.val (S.pointEquiv.apply_symm_apply ⟨y, hPS hyP⟩))).trans hy⟩
  have hTB := hB.maximal T hTC hTS hBT
  apply SetLike.coe_injective
  apply Set.Subset.antisymm _ hPS
  intro x hx
  change q.onPoints x ∈ B
  rw [← hTB]
  exact ⟨S.pointEquiv.symm ⟨x, hx⟩, congrArg q.onPoints
    (congrArg Subtype.val (S.pointEquiv.apply_symm_apply ⟨x, hx⟩))⟩

/-- Parabolic subgroups lift through connected solvable kernels, as subgroups
of the source of the quotient morphism. -/
public theorem preimage_parabolic
    {G Q : Variety k} [AlgebraicGroup G] [AlgebraicGroup Q]
    (q : AlgebraicGroup.Morphism G Q) (hq : Function.Surjective q.onPoints)
    (hkerC : _root_.IsConnected (q.kernelClosedSubgroup : Set (Variety.Point G)))
    (hkerS : Group.IsSolvable q.kernel)
    (S : ClosedSubgroup Q) (hS : IsParabolicSubgroup S) :
    IsParabolicSubgroup (q.closedSubgroupPreimage S) := by
  obtain ⟨B, hB, hBS⟩ := hS
  exact ⟨q.closedSubgroupPreimage B, preimage_borel q hq hkerC hkerS B hB,
    fun _ hx => hBS hx⟩

/-- Point-bijectivity descends through an equivariant quotient with invariant
kernel. Thus the bijective normalizer theorem remains usable after quotienting. -/
public theorem quotient_bijective
    {G Q : Variety k} [AlgebraicGroup G] [AlgebraicGroup Q]
    (q : AlgebraicGroup.Morphism G Q) (hq : Function.Surjective q.onPoints)
    (sigma : AlgebraicGroup.Morphism G G) (hsigma : Function.Bijective sigma.onPoints)
    (tau : AlgebraicGroup.Morphism Q Q)
    (heq : ∀ x, q.onPoints (sigma.onPoints x) = tau.onPoints (q.onPoints x))
    (hker : sigma.onPoints '' (q.kernel : Set (Variety.Point G)) = q.kernel) :
    Function.Bijective tau.onPoints := by
  constructor
  · intro a b hab
    obtain ⟨x, rfl⟩ := hq a
    obtain ⟨y, rfl⟩ := hq b
    have hxy : sigma.onPoints (x * y⁻¹) ∈ (q.kernel : Set (Variety.Point G)) := by
      change q.onPoints (sigma.onPoints (x * y⁻¹)) = 1
      rw [heq]
      simp only [map_mul, map_inv, hab, mul_inv_cancel]
    rw [← hker] at hxy
    obtain ⟨z, hz, hzxy⟩ := hxy
    have hzval : z = x * y⁻¹ := hsigma.1 hzxy
    rw [hzval] at hz
    change q.onPoints (x * y⁻¹) = 1 at hz
    simpa only [map_mul, map_inv, mul_inv_eq_one] using hz
  · intro a
    obtain ⟨x, rfl⟩ := hq a
    obtain ⟨y, rfl⟩ := hsigma.2 x
    exact ⟨q.onPoints y, (heq y).symm⟩

/-- The quotient lifting theorem specialized to the unipotent kernel used in
Borel--Tits. Solvability of that kernel is derived, rather than assumed. -/
public theorem preimage_parabolic_of_unipotent_kernel
    {G Q : Variety k} [AlgebraicGroup G] [AlgebraicGroup Q]
    (q : AlgebraicGroup.Morphism G Q) (hq : Function.Surjective q.onPoints)
    (hkerC : _root_.IsConnected (q.kernelClosedSubgroup : Set (Variety.Point G)))
    (hkerU : IsUnipotentAlgebraicGroup q.kernelClosedSubgroup.carrierVariety)
    (S : ClosedSubgroup Q) (hS : IsParabolicSubgroup S) :
    IsParabolicSubgroup (q.closedSubgroupPreimage S) := by
  apply preimage_parabolic q hq hkerC _ S hS
  let : Group.IsSolvable (Variety.Point q.kernelClosedSubgroup.carrierVariety) :=
    isSolvable_of_isUnipotentAlgebraicGroup hkerU
  exact Group.isSolvable_of_surjective
    (f := (Equiv.mulEquiv q.kernelClosedSubgroup.pointEquiv).toMonoidHom)
    q.kernelClosedSubgroup.pointEquiv.surjective

/-- A parabolic in a quotient of a parabolic subgroup lifts to an ambient
parabolic when the quotient kernel is connected and unipotent. For the
Borel--Tits application the kernel is `R_u(P)`; no quotient construction or
finite-generation hypothesis is hidden in this transfer. -/
public theorem preimage_parabolic_ambient
    {G Q : Variety k} [AlgebraicGroup G] [AlgebraicGroup Q]
    (P : ClosedSubgroup G) (hP : IsParabolicSubgroup P)
    (q : AlgebraicGroup.Morphism P.carrierVariety Q)
    (hq : Function.Surjective q.onPoints)
    (hkerC : _root_.IsConnected
      (q.kernelClosedSubgroup : Set (Variety.Point P.carrierVariety)))
    (hkerU : letI := q.kernelClosedSubgroup.carrierAlgebraicGroup
      IsUnipotentAlgebraicGroup q.kernelClosedSubgroup.carrierVariety)
    (S : ClosedSubgroup Q) (hS : IsParabolicSubgroup S) :
    letI := (q.closedSubgroupPreimage S).carrierAlgebraicGroup
    IsParabolicSubgroup
      (P.inclusion.comp (q.closedSubgroupPreimage S).inclusion).imageClosedSubgroup := by
  exact isParabolicSubgroup_trans P hP (q.closedSubgroupPreimage S)
    (preimage_parabolic_of_unipotent_kernel q hq hkerC hkerU S hS)

/-- Inclusion into the ambient group preserves invariance when the two
endomorphisms commute with that inclusion. -/
public theorem inclusion_image_invariant
    {G : Variety k} [AlgebraicGroup G]
    (P : ClosedSubgroup G) (sigma : AlgebraicGroup.Morphism G G)
    (sigmaP : AlgebraicGroup.Morphism P.carrierVariety P.carrierVariety)
    (heq : ∀ x, P.inclusion.onPoints (sigmaP.onPoints x) =
      sigma.onPoints (P.inclusion.onPoints x))
    (S : ClosedSubgroup P.carrierVariety)
    (hS : sigmaP.onPoints '' (S : Set (Variety.Point P.carrierVariety)) = S) :
    letI := S.carrierAlgebraicGroup
    sigma.onPoints ''
        ((P.inclusion.comp S.inclusion).imageClosedSubgroup : Set (Variety.Point G)) =
      (P.inclusion.comp S.inclusion).imageClosedSubgroup := by
  let := S.carrierAlgebraicGroup
  apply Set.Subset.antisymm
  · rintro _ ⟨x, hx, rfl⟩
    obtain ⟨y, hy, rfl⟩ := (P.mem_inclusion_image_iff S x).mp hx
    apply (P.mem_inclusion_image_iff S _).mpr
    refine ⟨sigmaP.onPoints y, ?_, heq y⟩
    change sigmaP.onPoints y ∈ (S : Set (Variety.Point P.carrierVariety))
    rw [← hS]
    exact ⟨y, hy, rfl⟩
  · intro x hx
    obtain ⟨y, hy, rfl⟩ := (P.mem_inclusion_image_iff S x).mp hx
    change y ∈ (S : Set (Variety.Point P.carrierVariety)) at hy
    rw [← hS] at hy
    obtain ⟨z, hz, rfl⟩ := hy
    exact ⟨P.inclusion.onPoints z,
      (P.mem_inclusion_image_iff S _).mpr ⟨z, hz, rfl⟩, (heq z).symm⟩

/-- The invariant ambient parabolic lifting used in the dimension induction
of GLS3, Theorem 3.1.3. The maps are the actual restriction to `P` and induced
quotient endomorphism, with their commuting identities stated explicitly.
Kernel invariance is discharged using its connectedness. -/
public theorem invariant_preimage_parabolic_ambient
    {G Q : Variety k} [AlgebraicGroup G] [AlgebraicGroup Q]
    (P : ClosedSubgroup G) (hP : IsParabolicSubgroup P)
    (q : AlgebraicGroup.Morphism P.carrierVariety Q)
    (hq : Function.Surjective q.onPoints)
    (hkerC : _root_.IsConnected
      (q.kernelClosedSubgroup : Set (Variety.Point P.carrierVariety)))
    (hkerU : letI := q.kernelClosedSubgroup.carrierAlgebraicGroup
      IsUnipotentAlgebraicGroup q.kernelClosedSubgroup.carrierVariety)
    (sigma : AlgebraicGroup.Morphism G G)
    (sigmaP : AlgebraicGroup.Morphism P.carrierVariety P.carrierVariety)
    (hsigmaP : IsAlgebraicSteinbergEndomorphism sigmaP)
    (hrestrict : ∀ x, P.inclusion.onPoints (sigmaP.onPoints x) =
      sigma.onPoints (P.inclusion.onPoints x))
    (tau : AlgebraicGroup.Morphism Q Q)
    (heq : ∀ x, q.onPoints (sigmaP.onPoints x) = tau.onPoints (q.onPoints x))
    (S : ClosedSubgroup Q) (hS : IsParabolicSubgroup S)
    (hSinv : tau.onPoints '' (S : Set (Variety.Point Q)) = S) :
    letI := (q.closedSubgroupPreimage S).carrierAlgebraicGroup
    let R := (P.inclusion.comp (q.closedSubgroupPreimage S).inclusion).imageClosedSubgroup
    IsParabolicSubgroup R ∧ sigma.onPoints '' (R : Set (Variety.Point G)) = R := by
  exact ⟨preimage_parabolic_ambient P hP q hq hkerC hkerU S hS,
    inclusion_image_invariant P sigma sigmaP hrestrict (q.closedSubgroupPreimage S)
      (preimage_invariant_of_connected_kernel q hq hkerC sigmaP hsigmaP.1 tau heq S hSinv)⟩

/-- The first inclusion in the ascending connected-radical chain. -/
public theorem connected_unipotent_le_normalizer_radical
    {G : Variety k} [AlgebraicGroup G] {X U : ClosedSubgroup G}
    (hXC : _root_.IsConnected (X : Set (Variety.Point G)))
    (hXU : IsUnipotentAlgebraicGroup X.carrierVariety)
    (hU : IsConnectedUnipotentRadicalOf X.normalizer U) : X ≤ U := by
  apply hU.2.2.2.2 X X.toSubgroup.le_normalizer hXC hXU
  intro g hg x hx
  exact (Subgroup.mem_normalizer_iff.mp hg x).mp hx

end Theory.AlgebraicGroup.BorelTitsDescent
