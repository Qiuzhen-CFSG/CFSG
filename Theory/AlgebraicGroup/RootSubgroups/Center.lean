module

public import Theory.AlgebraicGroup.ClosedSubgroup.Centralizer
public import Theory.AlgebraicGroup.RootSubgroups.GeneratedSubgroup

universe u

namespace Theory.AlgebraicGroup

variable {k : Type u} [Field k]

private lemma mem_rootSubgroup_centralizer_iff_rootWeight_pointCharacter_eq_one
    {K : Variety k} [AlgebraicGroup K] (T X : ClosedSubgroup K)
    (χ : TorusWeight T) (hX : IsTorusRootSubgroup T X)
    (hEq : RootWeightEquation T X χ) (z : Variety.Point K) (hz : z ∈ T) :
    z ∈ Subgroup.centralizer (X.toSubgroup : Set (Variety.Point K)) ↔
      χ.pointCharacter (T.pointEquiv.symm ⟨z, hz⟩) = 1 := by
  let s : Variety.Point T.carrierVariety := T.pointEquiv.symm ⟨z, hz⟩
  let x : OneParameterParametrization X.carrierVariety := Classical.choice hX.2
  have hs : T.includePoint s = z :=
    congrArg Subtype.val (T.pointEquiv.apply_symm_apply ⟨z, hz⟩)
  constructor
  · intro hzCentralizer
    have hxmem : X.includePoint (x.value 1) ∈ X :=
      (X.pointEquiv (x.value 1)).2
    have hcomm : X.includePoint (x.value 1) * z =
        z * X.includePoint (x.value 1) := hzCentralizer _ hxmem
    have hconj : z⁻¹ * X.includePoint (x.value 1) * z =
        X.includePoint (x.value 1) := by
      calc
        z⁻¹ * X.includePoint (x.value 1) * z =
            z⁻¹ * (X.includePoint (x.value 1) * z) := by rw [mul_assoc]
        _ = z⁻¹ * (z * X.includePoint (x.value 1)) := by rw [hcomm]
        _ = X.includePoint (x.value 1) := by simp
    have hweight := hEq x 1 s
    rw [hs, hconj, mul_one] at hweight
    have hxval : x.value 1 = x.value (χ.pointCharacter s) := by
      apply X.inclusion_injective
      exact hweight
    have hkplus : kPlusPoint 1 = kPlusPoint (χ.pointCharacter s) := by
      have h := congrArg x.inv.onPoints hxval
      simpa only [OneParameterParametrization.value, x.hom_inv_id] using h
    change χ.pointCharacter s = 1
    exact
      (congrArg (fun q : Variety.Point (KPlus k) => q.val PUnit.unit) hkplus).symm
  · intro hweight
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    let yX : Variety.Point X.carrierVariety := X.pointEquiv.symm ⟨y, hy⟩
    let qy : Variety.Point (KPlus k) := x.inv.onPoints yX
    let a : k := Multiplicative.toAdd (additiveGroupPointEquiv k qy)
    have hqa : kPlusPoint a = qy := by
      apply (additiveGroupPointEquiv k).injective
      exact Multiplicative.ofAdd.apply_symm_apply (additiveGroupPointEquiv k qy)
    have hxa : X.includePoint (x.value a) = y := by
      change (X.pointEquiv (x.hom.onPoints (kPlusPoint a))).val = y
      rw [hqa, x.inv_hom_id]
      exact congrArg Subtype.val (X.pointEquiv.apply_symm_apply ⟨y, hy⟩)
    have hconj := hEq x a s
    change χ.pointCharacter s = 1 at hweight
    rw [hs, hweight, one_mul, hxa] at hconj
    calc
      y * z = z * (z⁻¹ * y * z) := by simp [mul_assoc]
      _ = z * y := congrArg (fun w => z * w) hconj

/-- The center of the ambient group lies in every self-centralizing torus. -/
public theorem center_le_torus_of_centralizer_eq
    {K : Variety k} [AlgebraicGroup K] (T : ClosedSubgroup K)
    (hcentralizer : T.centralizer.toSubgroup = T.toSubgroup) :
    ∀ z, z ∈ Subgroup.center (Variety.Point K) → z ∈ T := by
  intro z hz
  have hzCentralizer : z ∈ T.centralizer.toSubgroup :=
    Subgroup.center_le_centralizer (T.toSubgroup : Set (Variety.Point K)) hz
  rwa [hcentralizer] at hzCentralizer

/-- If a torus is self-centralizing and it together with all root subgroups
generates the ambient group, then the center consists exactly of the torus
elements that centralize the root-generated subgroup.  This is the
group-theoretic reduction behind the center computations in GLS,
Theorem 1.12.6. -/
public theorem center_eq_torus_inf_rootSubgroupGenerated_centralizer
    {K : Variety k} [AlgebraicGroup K] (T : ClosedSubgroup K)
    (D : RootGroupData K T)
    (hcentralizer : T.centralizer.toSubgroup = T.toSubgroup)
    (hgen : RootSubgroupGenerated D Set.univ ⊔ T.toSubgroup = ⊤) :
    Subgroup.center (Variety.Point K) =
      T.toSubgroup ⊓ Subgroup.centralizer
        (RootSubgroupGenerated D Set.univ : Set (Variety.Point K)) := by
  apply le_antisymm
  · intro z hz
    exact ⟨center_le_torus_of_centralizer_eq T hcentralizer z hz,
      Subgroup.center_le_centralizer
        (RootSubgroupGenerated D Set.univ : Set (Variety.Point K)) hz⟩
  · intro z hz
    have hzT : z ∈ T.toSubgroup := hz.1
    have hzRoot : z ∈ Subgroup.centralizer
        (RootSubgroupGenerated D Set.univ : Set (Variety.Point K)) := hz.2
    have hzTcentralizer : z ∈ T.centralizer.toSubgroup := by
      rw [hcentralizer]
      exact hzT
    change z ∈ Subgroup.centralizer
      (T.toSubgroup : Set (Variety.Point K)) at hzTcentralizer
    have hroot : RootSubgroupGenerated D Set.univ ≤
        Subgroup.centralizer ({z} : Set (Variety.Point K)) := by
      intro x hx
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact hzRoot x hx
    have htorus : T.toSubgroup ≤
        Subgroup.centralizer ({z} : Set (Variety.Point K)) := by
      intro x hx
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact hzTcentralizer x hx
    have htop : (⊤ : Subgroup (Variety.Point K)) ≤
        Subgroup.centralizer ({z} : Set (Variety.Point K)) := by
      rw [← hgen]
      exact sup_le hroot htorus
    rw [Subgroup.mem_center_iff]
    intro x
    exact Subgroup.mem_centralizer_singleton_iff.mp (htop (by simp))

/-!
The exact-center step of GLS3 Theorem 1.12.9, isolated from the missing
root-system and upper-series bridges.  The hypotheses are independent facts:
`hUpper` identifies the first upper-central layer with the terminal height
layer, while `hUnique` identifies every root in that layer with the chosen
negative lowest root.  No conclusion-bearing setup structure is used.
-/

public theorem map_center_eq_terminal_rootSubgroup
    {K : Variety k} [AlgebraicGroup K] {T U : ClosedSubgroup K}
    (D : RootGroupData K T) (lowestRoot : D.Root)
    (Uheight : ℕ → ClosedSubgroup K) (c : ℕ)
    (hUheight : ∀ i, 0 < i →
      (Uheight i).toSubgroup =
        RootSubgroupGenerated D {α | (i : ℤ) ≤ D.height α})
    (hcpos : 0 < c)
    (hc : (c : ℤ) = D.height (D.neg lowestRoot))
    (hUnique : ∀ α : D.Root, (c : ℤ) ≤ D.height α →
      α = D.neg lowestRoot)
    (hUpper : Subgroup.map U.toSubgroup.subtype
      (Subgroup.upperCentralSeries U.toSubgroup 1) =
        (Uheight c).toSubgroup) :
    Subgroup.map U.toSubgroup.subtype (Subgroup.center U.toSubgroup) =
      (D.rootSubgroup (D.neg lowestRoot)).toSubgroup := by
  rw [← Subgroup.upperCentralSeries_one]
  rw [hUpper, hUheight c hcpos]
  have hset : {α : D.Root | (c : ℤ) ≤ D.height α} =
      {D.neg lowestRoot} := by
    ext α
    constructor
    · intro hα
      exact hUnique α hα
    · intro hα
      rw [Set.mem_singleton_iff] at hα
      subst α
      exact le_of_eq hc
  rw [hset, RootSubgroupGenerated_singleton]

/-- Under self-centralization and generation by the torus and root subgroups,
a torus element is central exactly when every realized root character
evaluates to one.  This is the character-kernel reduction used in the center
generator calculations of GLS, Theorem 1.12.6. -/
public theorem mem_center_iff_rootWeight_pointCharacter_eq_one
    [IsAlgClosed k] {K : Variety k} [AlgebraicGroup K] (T : ClosedSubgroup K)
    (D : RootGroupData K T) (hD : D.IsRealization)
    (hcentralizer : T.centralizer.toSubgroup = T.toSubgroup)
    (hgen : RootSubgroupGenerated D Set.univ ⊔ T.toSubgroup = ⊤)
    (z : Variety.Point K) (hz : z ∈ T) :
    z ∈ Subgroup.center (Variety.Point K) ↔
      ∀ α, (D.rootWeight α).pointCharacter
        (T.pointEquiv.symm ⟨z, hz⟩) = 1 := by
  constructor
  · intro hzCenter α
    have hzInf : z ∈ T.toSubgroup ⊓ Subgroup.centralizer
        (RootSubgroupGenerated D Set.univ : Set (Variety.Point K)) := by
      rw [← center_eq_torus_inf_rootSubgroupGenerated_centralizer
        T D hcentralizer hgen]
      exact hzCenter
    apply (mem_rootSubgroup_centralizer_iff_rootWeight_pointCharacter_eq_one
      T (D.rootSubgroup α) (D.rootWeight α) (hD.2.2.1 α).1
        (hD.2.2.1 α).2 z hz).mp
    intro x hx
    exact hzInf.2 x
      (rootSubgroup_le_RootSubgroupGenerated D (Set.mem_univ α) hx)
  · intro hroots
    have hzGenerated : z ∈ Subgroup.centralizer
        (RootSubgroupGenerated D Set.univ : Set (Variety.Point K)) := by
      rw [RootSubgroupGenerated, Subgroup.centralizer_closure,
        Subgroup.mem_centralizer_iff]
      intro x hx
      simp only [Set.mem_iUnion] at hx
      obtain ⟨α, -, hx⟩ := hx
      have hzAlpha : z ∈ Subgroup.centralizer
          ((D.rootSubgroup α).toSubgroup : Set (Variety.Point K)) :=
        (mem_rootSubgroup_centralizer_iff_rootWeight_pointCharacter_eq_one
          T (D.rootSubgroup α) (D.rootWeight α) (hD.2.2.1 α).1
            (hD.2.2.1 α).2 z hz).mpr (hroots α)
      exact hzAlpha x hx
    have hzInf : z ∈ T.toSubgroup ⊓ Subgroup.centralizer
        (RootSubgroupGenerated D Set.univ : Set (Variety.Point K)) :=
      ⟨hz, hzGenerated⟩
    rw [center_eq_torus_inf_rootSubgroupGenerated_centralizer
      T D hcentralizer hgen]
    exact hzInf

end Theory.AlgebraicGroup
