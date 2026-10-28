module

public import Theory.AlgebraicGroup.Tori.ProductSubgroup
public import Theory.AlgebraicGroup.Tori.Centralizer

/-!
# The maximal-torus centralizer component and its normalizer

For a maximal torus `T`, put `H = C_G(T)^0`. This module proves
`N_G(H)^0 = H`, the normalizer assertion of Borel §11.7, without assuming
nilpotence or connectedness of the full centralizer.

Two commuting maximal tori coincide because their product is a torus.
Consequently an element normalizing `H` normalizes `T`. Torus rigidity
(§8.10) puts the connected normalizer of `T` in its centralizer; taking
identity components proves the result. This avoids global maximal-torus
conjugacy, element coverage, root generation and Borel self-normalization.

The literal inclusion of `T` in `H` is also realized as a central maximal
torus of `H`, with its ambient image proved equal to `T`. It is the input
needed to apply §11.5(3)(b⇒c); nilpotence is not asserted here.

Source: Borel, *Linear Algebraic Groups*, second edition,
`refs/KGroup/Bor1/Chapter4.tex`, §§11.5 and 11.7;
`refs/KGroup/Bor1/Chapter3.tex`, §8.10.
-/

namespace Theory.AlgebraicGroup.CartanStructure
universe u
variable {k : Type u} [Field k] [IsAlgClosed k]
variable {G : Variety k} [AlgebraicGroup G]

/-- Commuting maximal tori coincide: their product is again a torus. -/
public theorem maximalTorus_eq_of_le_centralizer
    {T S : ClosedSubgroup G} (hT : IsMaximalTorus T) (hS : IsMaximalTorus S)
    (hST : S ≤ T.centralizer) : S = T := by
  let P := T.prod S
  let : AlgebraicGroup P.carrierVariety := P.carrierAlgebraicGroup
  let l : Morphism P.carrierVariety G := (Morphism.fst G G).comp P.inclusion
  let r : Morphism P.carrierVariety G := (Morphism.snd G G).comp P.inclusion
  have hl (x : Variety.Point P.carrierVariety) : l.onPoints x ∈ T :=
    ((T.mem_prod_iff S _).mp (P.pointEquiv x).property).1
  have hr (x : Variety.Point P.carrierVariety) : r.onPoints x ∈ S :=
    ((T.mem_prod_iff S _).mp (P.pointEquiv x).property).2
  have hc (x y : Variety.Point P.carrierVariety) :
      r.onPoints x * l.onPoints y = l.onPoints y * r.onPoints x :=
    (Subgroup.mem_centralizer_iff.mp (hST (hr x)) _ (hl y)).symm
  let m : Morphism P.carrierVariety G :=
    { toVariety := (AlgebraicGroup.mulMorphism G).comp (Morphism.prod l r).toVariety
      map_one := by change l.onPoints 1 * r.onPoints 1 = 1; simp
      map_mul := by
        intro x y
        change l.onPoints (x * y) * r.onPoints (x * y) =
          (l.onPoints x * r.onPoints x) * (l.onPoints y * r.onPoints y)
        simp only [map_mul]
        calc
          (l.onPoints x * l.onPoints y) * (r.onPoints x * r.onPoints y) =
              l.onPoints x * (l.onPoints y * r.onPoints x) * r.onPoints y := by
                simp only [mul_assoc]
          _ = l.onPoints x * (r.onPoints x * l.onPoints y) * r.onPoints y := by
                rw [hc]
          _ = (l.onPoints x * r.onPoints x) * (l.onPoints y * r.onPoints y) := by
                simp only [mul_assoc] }
  have hTI : T ≤ m.imageClosedSubgroup := by
    intro t ht
    let z := (Variety.prodPointEquiv G G).symm (t, 1)
    have hz : z ∈ P := by
      change z ∈ T.prod S
      rw [T.mem_prod_iff S, Equiv.apply_symm_apply]
      exact ⟨ht, S.toSubgroup.one_mem⟩
    refine ⟨P.pointEquiv.symm ⟨z, hz⟩, ?_⟩
    change (Variety.prodPointEquiv G G z).1 * (Variety.prodPointEquiv G G z).2 = t
    simp [z]
  have hSI : S ≤ m.imageClosedSubgroup := by
    intro s hs
    let z := (Variety.prodPointEquiv G G).symm (1, s)
    have hz : z ∈ P := by
      change z ∈ T.prod S
      rw [T.mem_prod_iff S, Equiv.apply_symm_apply]
      exact ⟨T.toSubgroup.one_mem, hs⟩
    refine ⟨P.pointEquiv.symm ⟨z, hz⟩, ?_⟩
    change (Variety.prodPointEquiv G G z).1 * (Variety.prodPointEquiv G G z).2 = s
    simp [z]
  have hIT := hT.2 _ (morphism_image_isTorus m (hT.prod hS).1) hTI
  rw [hIT] at hSI
  exact (hS.2 T hT.1 hSI).symm

omit [IsAlgClosed k] in
private theorem conjugate_isMaximalTorus {T : ClosedSubgroup G}
    (hT : IsMaximalTorus T) (g : Variety.Point G) :
    IsMaximalTorus (T.conjugate g) := by
  have hconj (S : ClosedSubgroup G) (hS : IsSubtorus S) (x : Variety.Point G) :
      IsSubtorus (S.conjugate x) := by
    obtain ⟨n, ⟨e⟩⟩ := hS
    exact ⟨n, ⟨(S.conjugateIso x).comp e⟩⟩
  refine ⟨hconj T hT.1 g, ?_⟩
  intro S hS hTS
  have hback : T ≤ S.conjugate g⁻¹ := by
    intro t ht
    apply (S.mem_conjugate_iff g⁻¹ t).mpr
    apply hTS
    apply (T.mem_conjugate_iff g _).mpr
    change t ∈ T.toSubgroup at ht
    simpa [mul_assoc] using ht
  have heq := hT.2 _ (hconj S hS g⁻¹) hback
  have h := congrArg (fun X : ClosedSubgroup G => X.conjugate g) heq
  simpa only [ClosedSubgroup.conjugate_conjugate, mul_inv_cancel,
    ClosedSubgroup.conjugate_one] using h

omit [IsAlgClosed k] in
private theorem mem_normalizer_of_conjugate_eq {T : ClosedSubgroup G}
    (g : Variety.Point G) (h : T.conjugate g = T) : g ∈ T.normalizer.toSubgroup := by
  apply Subgroup.mem_normalizer_iff.mpr
  intro t
  have heq : g⁻¹ * (g * t * g⁻¹) * g = t := by group
  have hm := T.mem_conjugate_iff g (g * t * g⁻¹)
  rw [h, heq] at hm
  exact hm.symm

/-- Every element normalizing the centralizer component normalizes its
maximal torus. No conjugacy theorem is used. -/
public theorem centralizerComponent_normalizer_le_torus_normalizer
    {T : ClosedSubgroup G} (hT : IsMaximalTorus T) :
    T.centralizer.identityComponentAmbient.normalizer ≤ T.normalizer := by
  let H := T.centralizer.identityComponentAmbient
  have hTH : T ≤ H := maximalTorus_le_identityComponentAmbient_of_le
    T T.centralizer hT (maximalTorus_le_centralizer hT)
  intro g hg
  have hTgH : T.conjugate g ≤ H := by
    intro x hx
    have hxH : x ∈ H.conjugate g :=
      (H.mem_conjugate_iff g x).mpr (hTH ((T.mem_conjugate_iff g x).mp hx))
    rwa [ClosedSubgroup.conjugate_eq_self_of_mem_normalizer g hg] at hxH
  apply mem_normalizer_of_conjugate_eq
  exact maximalTorus_eq_of_le_centralizer hT (conjugate_isMaximalTorus hT g)
    (fun _ hx => T.centralizer.identityComponentAmbient_le (hTgH hx))

omit [IsAlgClosed k] in
private theorem carrier_connected (H : ClosedSubgroup G)
    (hH : _root_.IsConnected (H : Set (Variety.Point G))) :
    Variety.IsConnected H.carrierVariety := by
  let e := Variety.closedSubvarietyPointHomeomorph H.isZariskiClosed
  let : ConnectedSpace {x : Variety.Point G // x ∈ (H : Set (Variety.Point G))} :=
    Subtype.connectedSpace hH
  let : ConnectedSpace (Variety.Point H.carrierVariety) :=
    e.connectedSpace_iff.mpr inferInstance
  exact connectedSpace_iff_univ.mp inferInstance

/-- The literal torus inside `C_G(T)^0` is central and remains maximal.
Its composite inclusion has ambient image exactly `T`. This supplies the
inputs to Borel §11.5(3)(b), before any nilpotence assertion is available. -/
public theorem exists_central_maximalTorus_in_centralizerComponent
    {T : ClosedSubgroup G} (hT : IsMaximalTorus T) :
    let H := T.centralizer.identityComponentAmbient
    ∃ S : ClosedSubgroup H.carrierVariety,
      letI : AlgebraicGroup S.carrierVariety := S.carrierAlgebraicGroup
      IsMaximalTorus S ∧
      S.toSubgroup ≤ Subgroup.center (Variety.Point H.carrierVariety) ∧
      (H.inclusion.comp S.inclusion).imageClosedSubgroup = T := by
  let H := T.centralizer.identityComponentAmbient
  have hTH : T ≤ H := maximalTorus_le_identityComponentAmbient_of_le
    T T.centralizer hT (maximalTorus_le_centralizer hT)
  let j := T.inclusion.codRestrictClosedSubgroup H
    (fun t => hTH (T.pointEquiv t).property)
  let S := j.imageClosedSubgroup
  let : AlgebraicGroup S.carrierVariety := S.carrierAlgebraicGroup
  have hj (t : Variety.Point T.carrierVariety) :
      H.inclusion.onPoints (j.onPoints t) = T.inclusion.onPoints t :=
    Morphism.codRestrictClosedSubgroup_inclusion_apply _ _ _ _
  have hmem (x : Variety.Point H.carrierVariety) :
      x ∈ S ↔ H.inclusion.onPoints x ∈ T := by
    constructor
    · rintro ⟨t, rfl⟩
      rw [hj]
      exact (T.pointEquiv t).property
    · intro hx
      refine ⟨T.pointEquiv.symm ⟨H.inclusion.onPoints x, hx⟩,
        H.inclusion_injective ?_⟩
      rw [hj]
      rfl
  have hmax : IsMaximalTorus S := by
    refine ⟨morphism_image_isTorus j hT.1, ?_⟩
    intro R hR hSR
    let : AlgebraicGroup R.carrierVariety := R.carrierAlgebraicGroup
    let f := H.inclusion.comp R.inclusion
    have hTf : T ≤ f.imageClosedSubgroup := by
      intro t ht
      let tH := H.pointEquiv.symm ⟨t, hTH ht⟩
      have htR : tH ∈ R := hSR ((hmem tH).mpr ht)
      exact ⟨R.pointEquiv.symm ⟨tH, htR⟩, rfl⟩
    have hfT := hT.2 _ (morphism_image_isTorus f hR) hTf
    apply SetLike.coe_injective
    apply Set.Subset.antisymm
    · intro r hr
      apply (hmem r).mpr
      rw [← hfT]
      exact ⟨R.pointEquiv.symm ⟨r, hr⟩, rfl⟩
    · exact hSR
  refine ⟨S, hmax, ?_, ?_⟩
  · intro s hs
    apply Subgroup.mem_center_iff.mpr
    intro x
    apply H.inclusion_injective
    rw [map_mul, map_mul]
    have hx : H.inclusion.onPoints x ∈ T.centralizer :=
      T.centralizer.identityComponentAmbient_le (H.pointEquiv x).property
    exact (Subgroup.mem_centralizer_iff.mp hx _ ((hmem s).mp hs)).symm
  · apply SetLike.coe_injective
    ext t
    constructor
    · rintro ⟨s, rfl⟩
      exact (hmem (S.inclusion.onPoints s)).mp (S.pointEquiv s).property
    · intro ht
      let tH := H.pointEquiv.symm ⟨t, hTH ht⟩
      exact ⟨S.pointEquiv.symm ⟨tH, (hmem tH).mpr ht⟩, rfl⟩

/-- Rigidity of tori puts the connected normalizer inside the centralizer. -/
public theorem torus_normalizer_identityComponent_le_centralizer
    {T : ClosedSubgroup G} (hT : IsMaximalTorus T) :
    T.normalizer.identityComponentAmbient ≤ T.centralizer := by
  let N := T.normalizer.identityComponentAmbient
  have hTN : T ≤ N := maximalTorus_le_identityComponentAmbient_of_le
    T T.normalizer hT Subgroup.le_normalizer
  let j := T.inclusion.codRestrictClosedSubgroup N
    (fun t => hTN (T.pointEquiv t).property)
  let S := j.imageClosedSubgroup
  let : AlgebraicGroup S.carrierVariety := S.carrierAlgebraicGroup
  have hj (t : Variety.Point T.carrierVariety) :
      N.inclusion.onPoints (j.onPoints t) = T.inclusion.onPoints t :=
    Morphism.codRestrictClosedSubgroup_inclusion_apply _ _ _ _
  have hmem (x : Variety.Point N.carrierVariety) :
      x ∈ S ↔ N.inclusion.onPoints x ∈ T := by
    constructor
    · rintro ⟨t, rfl⟩
      rw [hj]
      exact (T.pointEquiv t).property
    · intro hx
      refine ⟨T.pointEquiv.symm ⟨N.inclusion.onPoints x, hx⟩,
        N.inclusion_injective ?_⟩
      rw [hj]
      rfl
  have hSn : S.toSubgroup.Normal := by
    constructor
    intro x hx n
    apply (hmem _).mpr
    have hn : N.inclusion.onPoints n ∈ T.normalizer.toSubgroup :=
      T.normalizer.identityComponentAmbient_le (N.pointEquiv n).property
    change N.inclusion.onPoints (n * x * n⁻¹) ∈ T.toSubgroup
    rw [map_mul, map_mul, map_inv]
    exact (Subgroup.mem_normalizer_iff.mp hn (N.inclusion.onPoints x)).mp
      ((hmem x).mp hx)
  intro g hg
  let n := N.pointEquiv.symm ⟨g, hg⟩
  have hn : N.inclusion.onPoints n = g := rfl
  change g ∈ Subgroup.centralizer (T.toSubgroup : Set (Variety.Point G))
  rw [Subgroup.mem_centralizer_iff]
  intro t ht
  let tT := T.pointEquiv.symm ⟨t, ht⟩
  let s := S.pointEquiv.symm ⟨j.onPoints tT, ⟨tT, rfl⟩⟩
  have hs : S.inclusion.onPoints s = j.onPoints tT := rfl
  have hc := connected_centralizes_normal_subtorus
    (carrier_connected N T.normalizer.identityComponentAmbient_isConnected)
    S (morphism_image_isTorus j hT.1) hSn n s
  have hc' := congrArg N.inclusion.onPoints hc
  rw [map_mul, map_mul, map_inv, hs, hj, hn] at hc'
  change g * t * g⁻¹ = t at hc'
  exact (mul_inv_eq_iff_eq_mul.mp hc').symm

/-- The normalizer identity component of `C_G(T)^0` is itself (Borel §11.7).
Only torus maximality and rigidity enter this part of the source argument. -/
public theorem centralizerComponent_normalizer_identityComponent_eq
    {T : ClosedSubgroup G} (hT : IsMaximalTorus T) :
    T.centralizer.identityComponentAmbient.normalizer.identityComponentAmbient =
      T.centralizer.identityComponentAmbient := by
  let H := T.centralizer.identityComponentAmbient
  have hNT : H.normalizer.identityComponentAmbient ≤
      T.normalizer.identityComponentAmbient :=
    connected_closedSubgroup_le_identityComponentAmbient _ _
      H.normalizer.identityComponentAmbient_isConnected
      (fun _ hx => centralizerComponent_normalizer_le_torus_normalizer hT
        (H.normalizer.identityComponentAmbient_le hx))
  apply SetLike.coe_injective
  apply Set.Subset.antisymm
  · exact connected_closedSubgroup_le_identityComponentAmbient _ _
      H.normalizer.identityComponentAmbient_isConnected
      (fun _ hx => torus_normalizer_identityComponent_le_centralizer hT (hNT hx))
  · exact connected_closedSubgroup_le_identityComponentAmbient _ _
      T.centralizer.identityComponentAmbient_isConnected Subgroup.le_normalizer

end Theory.AlgebraicGroup.CartanStructure
