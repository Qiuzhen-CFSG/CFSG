module

public import Theory.AlgebraicGroup.Bor1.GeometricCertificates
public import Theory.AlgebraicGroup.ClosedSubgroup.Connected
public import Theory.AlgebraicGroup.RootSubgroups.Defs
public import Theory.AlgebraicGroup.Tori.Power

/-!
The finite-set step in Borel IV, 14.4(2)(a).

A finite set stable under a connected torus is fixed pointwise: each orbit is
the finite image of a connected variety. In a group with trivial torus fixed
subgroup this makes a finite invariant transverse set trivial. Consequently a
factorization of `X` into its identity component and such a set forces `X` to
be connected. Constructing that transverse set remains separate geometry.
-/

universe u

namespace Theory.AlgebraicGroup.BorelIntersectionGeometry

variable {k : Type u} [Field k] [IsAlgClosed k]
variable {G : Variety k} [AlgebraicGroup G]

/-- A connected subtorus fixes every point of a finite invariant set. This
uses inverse conjugation, the convention of `IsClosedSubgroupInvariant`. -/
public theorem finite_torusInvariant_set_fixed
    (T : ClosedSubgroup G) (hT : IsSubtorus T)
    (F : Set (Variety.Point G)) (hF : F.Finite)
    (hTF : ∀ t, t ∈ T → ∀ x, x ∈ F → t⁻¹ * x * t ∈ F)
    {x : Variety.Point G} (hx : x ∈ F) {t : Variety.Point G} (ht : t ∈ T) :
    t⁻¹ * x * t = x := by
  let f : Variety.Morphism T.carrierVariety G :=
    (inverseConjugateMorphism G x).comp T.inclusion.toVariety
  have hf (s : Variety.Point T.carrierVariety) :
      f.toFun s = (T.includePoint s)⁻¹ * x * T.includePoint s := by
    exact inverseConjugateMorphism_apply G x (T.includePoint s)
  have hfinite : (Set.range f.toFun).Finite := by
    apply hF.subset
    rintro y ⟨s, rfl⟩
    rw [hf]
    exact hTF _ (T.pointEquiv s).property x hx
  have hsub := connected_finite_morphism_range_subsingleton f hT.isConnected hfinite
  let s : Variety.Point T.carrierVariety := T.pointEquiv.symm ⟨t, ht⟩
  have hs : T.includePoint s = t :=
    congrArg Subtype.val (T.pointEquiv.apply_symm_apply ⟨t, ht⟩)
  have heq := hsub (Set.mem_range_self s) (Set.mem_range_self 1)
  rw [hf, hf, hs] at heq
  have h1 : T.includePoint (1 : Variety.Point T.carrierVariety) = 1 :=
    T.inclusion.map_one
  simpa only [h1, inv_one, one_mul, mul_one] using heq

/-- With trivial ambient fixed subgroup, every point of a finite invariant
subset of `U` is the identity. -/
public theorem finite_torusInvariant_subset_eq_one
    (T U : ClosedSubgroup G) (hT : IsSubtorus T)
    (hUT : (U.pointwiseCentralizer T).toSubgroup = ⊥)
    (F : Set (Variety.Point G)) (hF : F.Finite) (hFU : F ⊆ U)
    (hTF : ∀ t, t ∈ T → ∀ x, x ∈ F → t⁻¹ * x * t ∈ F)
    {x : Variety.Point G} (hx : x ∈ F) : x = 1 := by
  have hcentral : x ∈ T.centralizer := by
    apply Subgroup.mem_centralizer_iff.mpr
    intro t ht
    have hfix := finite_torusInvariant_set_fixed T hT F hF hTF hx ht
    calc
      t * x = t * (t⁻¹ * x * t) := congrArg (fun z => t * z) hfix.symm
      _ = x * t := by group
  have hxUT : x ∈ (U.pointwiseCentralizer T).toSubgroup := ⟨hFU hx, hcentral⟩
  rw [hUT] at hxUT
  exact Subgroup.mem_bot.mp hxUT

/-- The finite-subgroup case of the invariant-subgroup argument, without any
inference of connectedness from unipotence. -/
public theorem finite_invariant_subgroup_eq_bot_of_fixed_eq_bot
    (T U X : ClosedSubgroup G) (hT : IsSubtorus T)
    (hXU : X ≤ U) (hTX : IsClosedSubgroupInvariant T X)
    (hXfinite : (X : Set (Variety.Point G)).Finite)
    (hUT : (U.pointwiseCentralizer T).toSubgroup = ⊥) : X.toSubgroup = ⊥ := by
  apply le_antisymm
  · intro x hx
    exact Subgroup.mem_bot.mpr
      (finite_torusInvariant_subset_eq_one T U hT hUT X hXfinite hXU hTX hx)
  · exact bot_le

/-- The last paragraph of Borel IV, 14.4(2)(a): a finite invariant transverse
set in a group with no nonidentity torus fixed point forces connectedness.
The point factorization is the geometric input supplied earlier in that proof. -/
public theorem invariant_subgroup_connected_of_finite_transversal
    (T U X : ClosedSubgroup G) (hT : IsSubtorus T)
    (hUT : (U.pointwiseCentralizer T).toSubgroup = ⊥)
    (F : Set (Variety.Point G)) (hF : F.Finite) (hFU : F ⊆ U)
    (hTF : ∀ t, t ∈ T → ∀ x, x ∈ F → t⁻¹ * x * t ∈ F)
    (hfactor : ∀ x, x ∈ X → ∃ y, y ∈ X.identityComponentAmbient ∧
      ∃ f, f ∈ F ∧ x = y * f) :
    _root_.IsConnected (X : Set (Variety.Point G)) := by
  have hXeq : X = X.identityComponentAmbient := by
    apply SetLike.coe_injective
    apply Set.Subset.antisymm
    · intro x hx
      obtain ⟨y, hy, f, hf, rfl⟩ := hfactor x hx
      rw [finite_torusInvariant_subset_eq_one T U hT hUT F hF hFU hTF hf,
        mul_one]
      exact hy
    · exact X.identityComponentAmbient_le
  rw [hXeq]
  exact X.identityComponentAmbient_isConnected

end Theory.AlgebraicGroup.BorelIntersectionGeometry
