module

public import Theory.AlgebraicGroup.Borel.Existence
public import Theory.AlgebraicGroup.ClosedSubgroup.Product
public import Theory.AlgebraicGroup.RootSubgroups.Defs
public import Theory.AlgebraicGroup.Tori.Power

universe u

/-! Borel containment for a torus and one of its root subgroups. -/

namespace Theory.AlgebraicGroup

open scoped Pointwise

variable {k : Type u} [Field k] [IsAlgClosed k]

/-- A subtorus and one of its root subgroups lie in a common Borel subgroup. -/
public theorem exists_borelSubgroup_containing_torusRootSubgroup
    {K : Variety k} [AlgebraicGroup K] (T X : ClosedSubgroup K)
    (hT : IsSubtorus T) (hX : IsTorusRootSubgroup T X) :
    ∃ B : ClosedSubgroup K, IsBorelSubgroup B ∧ T ≤ B ∧ X ≤ B := by
  let Ts : Subgroup (Variety.Point K) := T.toClosedSubgroup.toSubgroup
  let Xs : Subgroup (Variety.Point K) := X.toClosedSubgroup.toSubgroup
  have hTcarrier : (T : Set (Variety.Point K)) =
      (Ts : Set (Variety.Point K)) := by
    rfl
  have hXcarrier : (X : Set (Variety.Point K)) =
      (Xs : Set (Variety.Point K)) := by
    rfl
  have hTmem (g : Variety.Point K) : g ∈ T ↔ g ∈ Ts :=
    Set.ext_iff.mp hTcarrier g
  have hXmem (g : Variety.Point K) : g ∈ X ↔ g ∈ Xs :=
    Set.ext_iff.mp hXcarrier g
  have hnorm : Ts ≤ Subgroup.normalizer (Xs : Set (Variety.Point K)) := by
    intro t ht
    have htT : t ∈ T := (hTmem t).mpr ht
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      have hxX : x ∈ X := (hXmem x).mpr hx
      have htinv : t⁻¹ ∈ T := (hTmem t⁻¹).mpr (Ts.inv_mem ht)
      have hr := hX.1 t⁻¹ htinv x hxX
      exact (hXmem (t * x * t⁻¹)).mp (by simpa only [inv_inv] using hr)
    · intro hx
      have hxX : t * x * t⁻¹ ∈ X := (hXmem (t * x * t⁻¹)).mpr hx
      have hr := hX.1 t htT (t * x * t⁻¹) hxX
      exact (hXmem x).mp (by simpa [mul_assoc] using hr)
  obtain ⟨m, hm⟩ :=
    exists_closedSubgroup_productMorphism_range_eq_pointwise_mul X T
  have hsupConstructible : Topology.IsConstructible
      ((Ts ⊔ Xs : Subgroup (Variety.Point K)) : Set (Variety.Point K)) := by
    rw [sup_comm, Subgroup.coe_mul_of_right_le_normalizer_left Xs Ts hnorm,
      ← hm]
    exact m.range_isConstructible
  have hsupClosed : IsClosed
      ((Ts ⊔ Xs : Subgroup (Variety.Point K)) : Set (Variety.Point K)) :=
    constructible_subgroup_isClosed K _ hsupConstructible
  let H : ClosedSubgroup K := ClosedSubgroup.ofSubgroup
    (Ts ⊔ Xs) (Variety.isClosed_iff_isZariskiClosed.mp hsupClosed)
  have hprodConnected : Variety.IsConnected
      (Variety.prod X.carrierVariety T.carrierVariety) := by
    have hI := prodSet_irreducible_of_irreducible
      (connectedAlgebraicGroup_irreducible X.carrierVariety hX.2.isConnected)
      (connectedAlgebraicGroup_irreducible T.carrierVariety hT.isConnected)
    have hprod : Variety.prodSet
        (Set.univ : Set (Variety.Point X.carrierVariety))
        (Set.univ : Set (Variety.Point T.carrierVariety)) =
        (Set.univ : Set (Variety.Point
          (Variety.prod X.carrierVariety T.carrierVariety))) := by
      ext z
      simp [Variety.prodSet]
    rw [hprod] at hI
    exact hI.isConnected
  have hHconnected : _root_.IsConnected
      (H : Set (Variety.Point K)) := by
    change _root_.IsConnected
      ((Ts ⊔ Xs : Subgroup (Variety.Point K)) : Set (Variety.Point K))
    rw [sup_comm, Subgroup.coe_mul_of_right_le_normalizer_left Xs Ts hnorm,
      ← hm, ← Set.image_univ]
    exact hprodConnected.image m.toFun m.continuous.continuousOn
  have hHsolvable : Group.IsSolvable (Variety.Point H.carrierVariety) := by
    have hKPlusSolvable : Group.IsSolvable (Variety.Point (KPlus k)) := by
      apply Group.isSolvable_of_comm
      intro a b
      apply (additiveGroupPointEquiv k).injective
      change Multiplicative.ofAdd
          (Multiplicative.toAdd (additiveGroupPointEquiv k a) +
            Multiplicative.toAdd (additiveGroupPointEquiv k b)) =
        Multiplicative.ofAdd
          (Multiplicative.toAdd (additiveGroupPointEquiv k b) +
            Multiplicative.toAdd (additiveGroupPointEquiv k a))
      rw [add_comm]
    let x : OneParameterParametrization X.carrierVariety := Classical.choice hX.2
    let : Group.IsSolvable (Variety.Point (KPlus k)) := hKPlusSolvable
    let : Group.IsSolvable (Variety.Point X.carrierVariety) :=
      Group.isSolvable_of_surjective (f := x.hom.onPoints) fun y =>
        ⟨x.inv.onPoints y, x.inv_hom_id y⟩
    let : Group.IsSolvable Xs :=
      Group.isSolvable_of_surjective
        (f := (Equiv.mulEquiv X.pointEquiv).toMonoidHom)
        (Equiv.mulEquiv X.pointEquiv).surjective
    have hTPointsSolvable : Group.IsSolvable
        (Variety.Point T.carrierVariety) := by
      apply Group.isSolvable_of_comm
      exact isMulCommutative_iff.mp hT.isMulCommutative
    let : Group.IsSolvable (Variety.Point T.carrierVariety) := hTPointsSolvable
    let : Group.IsSolvable Ts :=
      Group.isSolvable_of_surjective
        (f := (Equiv.mulEquiv T.pointEquiv).toMonoidHom)
        (Equiv.mulEquiv T.pointEquiv).surjective
    let S := Ts ⊔ Xs
    let XS : Subgroup S := Xs.subgroupOf S
    let : XS.Normal :=
      Subgroup.normal_subgroupOf_sup_of_le_normalizer hnorm
    let q := QuotientGroup.mk' XS
    let iT : Ts →* S := Subgroup.inclusion le_sup_left
    let qT : Ts →* S ⧸ XS := q.comp iT
    have hqTsurj : Function.Surjective qT := by
      intro y
      obtain ⟨s, rfl⟩ := QuotientGroup.mk'_surjective XS y
      have hs : s.1 ∈ (Xs : Set (Variety.Point K)) *
          (Ts : Set (Variety.Point K)) := by
        have hsjoin : s.1 ∈ Xs ⊔ Ts := by
          simpa only [S, sup_comm] using s.2
        exact (Set.ext_iff.mp
          (Subgroup.coe_mul_of_right_le_normalizer_left Xs Ts hnorm) s.1).mp
            hsjoin
      rcases hs with ⟨z, hz, t, ht, hzs⟩
      refine ⟨⟨t, ht⟩, ?_⟩
      apply (QuotientGroup.eq_iff_div_mem).2
      change t / s.1 ∈ Xs
      rw [← hzs]
      simpa using Xs.inv_mem hz
    let : Group.IsSolvable (S ⧸ XS) := Group.isSolvable_of_surjective hqTsurj
    have hSsolvable : Group.IsSolvable S := by
      apply Group.isSolvable_of_ker_le_range (Subgroup.inclusion le_sup_right) q
      simp [q, XS, S]
    let : Group.IsSolvable H.toSubgroup := hSsolvable
    exact Group.isSolvable_of_isSolvable_injective
      (f := (Equiv.mulEquiv H.pointEquiv).toMonoidHom)
      (Equiv.mulEquiv H.pointEquiv).injective
  obtain ⟨B, hB, hHB⟩ :=
    exists_borelSubgroup_containing_connected_solvable H hHconnected hHsolvable
  refine ⟨B, hB, ?_, ?_⟩
  · intro t ht
    apply hHB
    change t ∈ Ts ⊔ Xs
    apply (show Ts ≤ Ts ⊔ Xs from le_sup_left)
    exact (hTmem t).mp ht
  · intro x hx
    apply hHB
    change x ∈ Ts ⊔ Xs
    apply (show Xs ≤ Ts ⊔ Xs from le_sup_right)
    exact (hXmem x).mp hx

end Theory.AlgebraicGroup
