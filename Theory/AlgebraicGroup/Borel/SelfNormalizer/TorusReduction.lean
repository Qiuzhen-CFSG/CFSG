module

public import Theory.AlgebraicGroup.Solvable.MaximalTorusConjugacy
public import Theory.AlgebraicGroup.Borel.IntersectionGeometry.Transport

/-!
# Reduction of a Borel normalizer to a torus normalizer

Maximal tori contained in a Borel are conjugate inside that Borel, by the
connected solvable conjugacy theorem. Consequently every point of `N(B)` is
`b * n`, where `b ∈ B` and `n ∈ N(B) ∩ N(T)`. Self-normalization therefore
reduces to the latter intersection. No Bruhat decomposition, ambient torus
conjugacy, or unipotent-radical normalizer theorem is used.

The final definitions specify the actual fixed points on the chosen torus
and the strictly smaller-dimensional induction hypothesis used by the two
geometric branches. They do not assert either branch.

Source: Borel, *Linear Algebraic Groups*, Theorem 11.16, first reduction;
`refs/KGroup/Bor1/Chapter4.tex`, lines 221–229.
-/

universe u

namespace Theory.AlgebraicGroup.BorelSelfNormalizer

variable {k : Type u} [Field k] [IsAlgClosed k]
variable {G : Variety k} [AlgebraicGroup G]

private noncomputable def inside (T B : ClosedSubgroup G) (hTB : T ≤ B) :
    ClosedSubgroup B.carrierVariety :=
  (T.inclusion.codRestrictClosedSubgroup B
    (fun t => hTB (T.pointEquiv t).property)).imageClosedSubgroup

private theorem mem_inside (T B : ClosedSubgroup G) (hTB : T ≤ B)
    (x : Variety.Point B.carrierVariety) :
    x ∈ inside T B hTB ↔ B.inclusion.onPoints x ∈ T := by
  let f := T.inclusion.codRestrictClosedSubgroup B
    (fun t => hTB (T.pointEquiv t).property)
  change (∃ t, f.onPoints t = x) ↔ B.inclusion.onPoints x ∈ T
  constructor
  · rintro ⟨t, rfl⟩
    rw [Morphism.codRestrictClosedSubgroup_inclusion_apply]
    exact (T.pointEquiv t).property
  · intro hx
    let t := T.pointEquiv.symm ⟨B.inclusion.onPoints x, hx⟩
    refine ⟨t, B.inclusion_injective ?_⟩
    rw [Morphism.codRestrictClosedSubgroup_inclusion_apply]
    exact congrArg Subtype.val (T.pointEquiv.apply_symm_apply _)

private theorem inside_isMaximalTorus (T B : ClosedSubgroup G)
    (hTB : T ≤ B) (hT : IsMaximalTorus T) :
    IsMaximalTorus (inside T B hTB) := by
  refine ⟨morphism_image_isTorus _ hT.1, ?_⟩
  intro S hS hTS
  let : AlgebraicGroup S.carrierVariety := S.carrierAlgebraicGroup
  let f := B.inclusion.comp S.inclusion
  have hTf : T ≤ f.imageClosedSubgroup := by
    intro t ht
    let tB := B.pointEquiv.symm ⟨t, hTB ht⟩
    have htB : B.inclusion.onPoints tB = t :=
      congrArg Subtype.val (B.pointEquiv.apply_symm_apply _)
    have htS : tB ∈ S := hTS ((mem_inside T B hTB tB).mpr (htB.symm ▸ ht))
    refine ⟨S.pointEquiv.symm ⟨tB, htS⟩, ?_⟩
    change B.inclusion.onPoints (S.inclusion.onPoints _) = t
    exact (congrArg B.inclusion.onPoints
      (congrArg Subtype.val (S.pointEquiv.apply_symm_apply _))).trans htB
  have hfT := hT.2 _ (morphism_image_isTorus f hS) hTf
  apply SetLike.coe_injective
  apply Set.Subset.antisymm
  · intro s hs
    apply (mem_inside T B hTB s).mpr
    rw [← hfT]
    refine ⟨S.pointEquiv.symm ⟨s, hs⟩, ?_⟩
    change B.inclusion.onPoints (S.inclusion.onPoints _) = B.inclusion.onPoints s
    exact congrArg B.inclusion.onPoints
      (congrArg Subtype.val (S.pointEquiv.apply_symm_apply _))
  · exact hTS

/-- Ambient maximal tori contained in a Borel are conjugate by a point of
that Borel. Only connected solvable conjugacy is needed. -/
public theorem maximalTori_conjugate_inside_borel
    {B T S : ClosedSubgroup G} (hB : IsBorelSubgroup B)
    (hT : IsMaximalTorus T) (hS : IsMaximalTorus S)
    (hTB : T ≤ B) (hSB : S ≤ B) :
    ∃ b : Variety.Point G, b ∈ B.toSubgroup ∧ S = T.conjugate b := by
  have hBc : Variety.IsConnected B.carrierVariety := by
    let e := Variety.closedSubvarietyPointHomeomorph B.isZariskiClosed
    let : ConnectedSpace {x : Variety.Point G // x ∈ (B : Set (Variety.Point G))} :=
      Subtype.connectedSpace hB.connected
    let : ConnectedSpace (Variety.Point B.carrierVariety) :=
      e.connectedSpace_iff.mpr inferInstance
    exact connectedSpace_iff_univ.mp inferInstance
  obtain ⟨b, hb⟩ := maximalTori_conjugate_of_solvable_connected hB.solvable hBc
    (inside_isMaximalTorus T B hTB hT) (inside_isMaximalTorus S B hSB hS)
  let g := B.inclusion.onPoints b
  have hg : g ∈ B.toSubgroup := (B.pointEquiv b).property
  have hconjB : T.conjugate g ≤ B := by
    have h := BorelIntersectionGeometry.conjugate_le hTB g
    rwa [ClosedSubgroup.conjugate_eq_self_of_mem_normalizer g
      (Subgroup.le_normalizer hg)] at h
  have hmem (x : Variety.Point B.carrierVariety) :
      B.inclusion.onPoints x ∈ S ↔ B.inclusion.onPoints x ∈ T.conjugate g := by
    rw [← mem_inside S B hSB x, hb, ClosedSubgroup.mem_conjugate_iff]
    change b⁻¹ * x * b ∈ inside T B hTB ↔ _
    rw [mem_inside T B hTB, ClosedSubgroup.mem_conjugate_iff]
    simp only [map_mul, map_inv, g]
    rfl
  refine ⟨g, hg, SetLike.coe_injective ?_⟩
  apply Set.Subset.antisymm
  · intro x hx
    let xB := B.pointEquiv.symm ⟨x, hSB hx⟩
    have hxB : B.inclusion.onPoints xB = x :=
      congrArg Subtype.val (B.pointEquiv.apply_symm_apply _)
    exact hxB ▸ (hmem xB).mp (hxB.symm ▸ hx)
  · intro x hx
    let xB := B.pointEquiv.symm ⟨x, hconjB hx⟩
    have hxB : B.inclusion.onPoints xB = x :=
      congrArg Subtype.val (B.pointEquiv.apply_symm_apply _)
    exact hxB ▸ (hmem xB).mpr (hxB.symm ▸ hx)

/-- The first reduction in Borel 11.16: a normalizer point is a Borel point
times a point normalizing both the Borel and its chosen maximal torus. -/
public theorem normalizer_factorization
    {B T : ClosedSubgroup G} (hB : IsBorelSubgroup B)
    (hT : IsMaximalTorus T) (hTB : T ≤ B)
    (g : Variety.Point G) (hg : g ∈ B.normalizer.toSubgroup) :
    ∃ b n : Variety.Point G, b ∈ B.toSubgroup ∧
      n ∈ B.normalizer.toSubgroup ∧ n ∈ T.normalizer.toSubgroup ∧ g = b * n := by
  have hTgB : T.conjugate g ≤ B := by
    have h := BorelIntersectionGeometry.conjugate_le hTB g
    rwa [ClosedSubgroup.conjugate_eq_self_of_mem_normalizer g hg] at h
  obtain ⟨b, hb, hTb⟩ := maximalTori_conjugate_inside_borel hB hT
    (BorelIntersectionGeometry.conjugate_isMaximalTorus hT g) hTB hTgB
  have hTn : T.conjugate (b⁻¹ * g) = T := by
    rw [← ClosedSubgroup.conjugate_conjugate, hTb,
      ClosedSubgroup.conjugate_conjugate, inv_mul_cancel, ClosedSubgroup.conjugate_one]
  have hnT : b⁻¹ * g ∈ T.normalizer.toSubgroup := by
    change b⁻¹ * g ∈ Subgroup.normalizer (T.toSubgroup : Set (Variety.Point G))
    rw [Subgroup.mem_normalizer_iff]
    intro t
    have hback : ∀ x : Variety.Point G,
        (b⁻¹ * g)⁻¹ * x * (b⁻¹ * g) ∈ T.toSubgroup ↔ x ∈ T.toSubgroup := by
      intro x
      rw [← T.mem_conjugate_iff, hTn]
      rfl
    have h := hback ((b⁻¹ * g) * t * (b⁻¹ * g)⁻¹)
    have hc : (b⁻¹ * g)⁻¹ * ((b⁻¹ * g) * t * (b⁻¹ * g)⁻¹) * (b⁻¹ * g) = t := by
      group
    rwa [hc] at h
  exact ⟨b, b⁻¹ * g, hb,
    B.normalizer.toSubgroup.mul_mem
      (B.normalizer.toSubgroup.inv_mem (Subgroup.le_normalizer hb)) hg,
    hnT, by simp⟩

/-- Self-normalization reduces to the simultaneous Borel and torus
normalizer. The containment premise is the remaining geometric obligation. -/
public theorem normalizer_eq_of_simultaneous_normalizer_le
    {B T : ClosedSubgroup G} (hB : IsBorelSubgroup B)
    (hT : IsMaximalTorus T) (hTB : T ≤ B)
    (hle : B.normalizer.toSubgroup ⊓ T.normalizer.toSubgroup ≤ B.toSubgroup) :
    B.normalizer = B := by
  apply SetLike.coe_injective
  apply Set.Subset.antisymm
  · intro g hg
    obtain ⟨b, n, hb, hnB, hnT, rfl⟩ := normalizer_factorization hB hT hTB g hg
    exact B.toSubgroup.mul_mem hb (hle ⟨hnB, hnT⟩)
  · exact Subgroup.le_normalizer

/-- The fixed points of conjugation by `n` on the actual torus `T`, viewed
in the ambient point group. This is the source subgroup `S = T ∩ C_G(n)`. -/
@[expose]
public def fixedTorusPoints (T : ClosedSubgroup G) (n : Variety.Point G) :
    Set (Variety.Point G) :=
  {t | t ∈ T.toSubgroup ∧ n * t = t * n}

/-- The induction hypothesis only concerns connected groups of strictly
smaller dimension. Each Borel retains its actual contained maximal torus. -/
@[expose]
public def SmallerDimension (G : Variety k) : Prop :=
  ∀ (H : Variety k) [AlgebraicGroup H],
    Variety.dimension H < Variety.dimension G →
    Variety.IsConnected H →
    ∀ (B T : ClosedSubgroup H), IsBorelSubgroup B → IsMaximalTorus T → T ≤ B →
      B.normalizer = B

end Theory.AlgebraicGroup.BorelSelfNormalizer
