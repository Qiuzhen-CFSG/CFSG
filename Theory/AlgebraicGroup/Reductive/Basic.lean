module

public import Theory.AlgebraicGroup.ClosedSubgroup.Centralizer
public import Theory.AlgebraicGroup.Radical.Existence
public import Theory.AlgebraicGroup.Reductive.Defs
public import Theory.AlgebraicGroup.Tori.Centralizer

universe u

/-! Radicals and centers of reductive algebraic groups. -/

namespace Theory.AlgebraicGroup

variable {k : Type u} [Field k] [IsAlgClosed k]

/-- In a reductive group, every radical is the identity component of the
center. -/
public theorem radical_eq_center_identityComponent_of_reductive
    {G : Variety k} [AlgebraicGroup G]
    (hG : IsReductiveAlgebraicGroup G)
    (R : ClosedSubgroup G) (hR : IsRadicalSubgroup R) :
    R = (ClosedSubgroup.top (G := G)).centralizer.identityComponentAmbient := by
  let Z : ClosedSubgroup G := (ClosedSubgroup.top (G := G)).centralizer
  let T : ClosedSubgroup G := Z.identityComponentAmbient
  have hZcarrier : (Z.toSubgroup : Set (Variety.Point G)) =
      Subgroup.center (Variety.Point G) := by
    ext x
    change x ∈ Subgroup.centralizer (Set.univ : Set (Variety.Point G)) ↔
      x ∈ Subgroup.center (Variety.Point G)
    rw [Subgroup.mem_centralizer_iff, Subgroup.mem_center_iff]
    simp only [Set.mem_univ, forall_const]
  have hRcentral : R ≤ Z := by
    intro x hx
    change x ∈ (Z.toSubgroup : Set (Variety.Point G))
    rw [hZcarrier]
    apply Subgroup.mem_center_iff.mpr
    intro g
    let xR : Variety.Point R.carrierVariety := R.pointEquiv.symm ⟨x, hx⟩
    have hconj := connected_centralizes_normal_subtorus
      hG.1 R (hG.2 R hR) hR.normal g xR
    have hxR : R.inclusion.onPoints xR = x := by
      change (R.pointEquiv xR).val = x
      simp [xR]
    rw [hxR] at hconj
    calc
      g * x = (g * x * g⁻¹) * g := by group
      _ = x * g := by rw [hconj]
  have hRT : R ≤ T :=
    connected_closedSubgroup_le_identityComponentAmbient
      R Z hR.connected hRcentral
  have hZnormal : Z.toSubgroup.Normal := by
    let : (ClosedSubgroup.top (G := G)).toSubgroup.Normal := by
      change (⊤ : Subgroup (Variety.Point G)).Normal
      infer_instance
    change (Subgroup.centralizer
      ((ClosedSubgroup.top (G := G)).toSubgroup : Set (Variety.Point G))).Normal
    infer_instance
  have hTnormal : T.toSubgroup.Normal :=
    Z.identityComponentAmbient_normal_of_normal hZnormal
  have hTconnected : _root_.IsConnected (T : Set (Variety.Point G)) :=
    Z.identityComponentAmbient_isConnected
  have hTcentral : T ≤ Z := Z.identityComponentAmbient_le
  have hTcomm : ∀ x y : Variety.Point T.carrierVariety, x * y = y * x := by
    intro x y
    apply T.inclusion_injective
    rw [map_mul, map_mul]
    have hxZ : T.inclusion.onPoints x ∈ Z :=
      hTcentral (T.pointEquiv x).property
    have hxCenter : T.inclusion.onPoints x ∈
        Subgroup.center (Variety.Point G) := by
      change T.inclusion.onPoints x ∈
        (Subgroup.center (Variety.Point G) : Set (Variety.Point G))
      rw [← hZcarrier]
      exact hxZ
    exact (Subgroup.mem_center_iff.mp hxCenter (T.inclusion.onPoints y)).symm
  have hTsolvable : Group.IsSolvable (Variety.Point T.carrierVariety) :=
    Group.isSolvable_of_comm hTcomm
  have hTR : T ≤ R := hR.maximal T hTnormal hTconnected hTsolvable
  apply SetLike.coe_injective
  exact Set.Subset.antisymm hRT hTR

/-- The identity component of the center of a reductive group is a torus. -/
public theorem center_identityComponent_isSubtorus_of_reductive
    {G : Variety k} [AlgebraicGroup G]
    (hG : IsReductiveAlgebraicGroup G) :
    IsSubtorus
      (ClosedSubgroup.top (G := G)).centralizer.identityComponentAmbient := by
  obtain ⟨R, hR⟩ := exists_radical G
  rw [← radical_eq_center_identityComponent_of_reductive hG R hR]
  exact hG.2 R hR

/-- Theorem 1.7.2(c): for a connected group, reductivity is equivalent to
the existence of a toral radical. -/
public theorem isReductive_iff_exists_radical_isSubtorus_of_isConnected
    {G : Variety k} [AlgebraicGroup G]
    (hconnected : Variety.IsConnected G) :
    IsReductiveAlgebraicGroup G ↔
      ∃ R : ClosedSubgroup G, IsRadicalSubgroup R ∧ IsSubtorus R := by
  constructor
  · intro hG
    obtain ⟨R, hR⟩ := exists_radical G
    exact ⟨R, hR, hG.2 R hR⟩
  · rintro ⟨R, hR, hRtorus⟩
    refine ⟨hconnected, ?_⟩
    intro S hS
    rw [hS.eq hR]
    exact hRtorus

public theorem theorem_1_7_2_c
    {G : Variety k} [AlgebraicGroup G] (hG : Variety.IsConnected G) :
    IsReductiveAlgebraicGroup G ↔
      ∃ R : ClosedSubgroup G, IsRadicalSubgroup R ∧ IsSubtorus R := by
  exact isReductive_iff_exists_radical_isSubtorus_of_isConnected hG

end Theory.AlgebraicGroup
