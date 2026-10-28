module

public import Theory.AlgebraicGroup.Parabolic.Defs
public import Theory.AlgebraicGroup.Borel.Conjugation.theorem_1_6_2_b
public import Theory.AlgebraicGroup.Borel.GeometricConjugacy
public import Theory.AlgebraicGroup.Morphism.ClosedImage

/-!
# Ambient transfer of parabolic subgroups

An ambient Borel contained in a closed subgroup restricts to a Borel of that
subgroup. Geometric Borel conjugacy inside a parabolic subgroup `P` then shows
that every Borel of `P` has Borel image in the ambient group. Consequently a
parabolic of `P` has parabolic ambient image.

The restriction proof uses connected solvable images and ambient maximality.
The transfer proof conjugates the restricted ambient Borel inside `P`, and
uses compatibility of the two inclusions with conjugation.

Source: GLS3, Section 1.6 (especially Theorem 1.6.2(b)), and the quotient-lifting
steps in Section 3.1, including the proof of Theorem 3.1.3. The final results
discharge the intermediate conjugacy premise using the complete flag orbit and
solvable fixed-point proof in `Borel.GeometricConjugacy`. The unresolved numbered
conjugacy theorem is not used. Ambient connectedness is unnecessary for this
transfer, so the results also apply to the connected groups of the source.
-/

universe u

namespace Theory.AlgebraicGroup

variable {k : Type u} [Field k] [IsAlgClosed k]

omit [IsAlgClosed k] in
private lemma transitivity_carrier_connected
    {G : Variety k} [AlgebraicGroup G] (B : ClosedSubgroup G)
    (hB : _root_.IsConnected (B : Set (Variety.Point G))) :
    Variety.IsConnected B.carrierVariety := by
  let e := Variety.closedSubvarietyPointHomeomorph B.isZariskiClosed
  let : ConnectedSpace {x : Variety.Point G // x ∈ (B : Set (Variety.Point G))} :=
    Subtype.connectedSpace hB
  let : ConnectedSpace (Variety.Point B.carrierVariety) :=
    e.connectedSpace_iff.mpr inferInstance
  exact connectedSpace_iff_univ.mp inferInstance

/-- Membership in the ambient image of a subgroup of a closed subgroup. -/
public lemma ClosedSubgroup.mem_inclusion_image_iff
    {G : Variety k} [AlgebraicGroup G] (P : ClosedSubgroup G)
    (S : ClosedSubgroup P.carrierVariety) (x : Variety.Point G) :
    letI : AlgebraicGroup S.carrierVariety := S.carrierAlgebraicGroup
    x ∈ (P.inclusion.comp S.inclusion).imageClosedSubgroup ↔
      ∃ y : Variety.Point P.carrierVariety, y ∈ S ∧ P.inclusion.onPoints y = x := by
  let := S.carrierAlgebraicGroup
  constructor
  · rintro ⟨z, rfl⟩
    exact ⟨S.inclusion.onPoints z, (S.pointEquiv z).property, rfl⟩
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨z, rfl⟩ := (show y ∈ Set.range S.inclusion.onPoints by
      rw [S.range_inclusion]
      exact hy)
    exact ⟨z, rfl⟩

/-- The outer inclusion reflects membership in the iterated inclusion image. -/
public lemma ClosedSubgroup.inclusion_mem_inclusion_image_iff
    {G : Variety k} [AlgebraicGroup G] (P : ClosedSubgroup G)
    (S : ClosedSubgroup P.carrierVariety) (x : Variety.Point P.carrierVariety) :
    letI : AlgebraicGroup S.carrierVariety := S.carrierAlgebraicGroup
    P.inclusion.onPoints x ∈ (P.inclusion.comp S.inclusion).imageClosedSubgroup ↔ x ∈ S := by
  let := S.carrierAlgebraicGroup
  rw [P.mem_inclusion_image_iff]
  constructor
  · rintro ⟨y, hy, heq⟩
    exact P.inclusion_injective heq ▸ hy
  · exact fun hx => ⟨x, hx, rfl⟩

/-- Restricting a contained subgroup and then including it recovers that subgroup. -/
public lemma ClosedSubgroup.inclusion_image_preimage_of_le
    {G : Variety k} [AlgebraicGroup G] (P B : ClosedSubgroup G)
    (hBP : B ≤ P) :
    letI : AlgebraicGroup (P.inclusion.closedSubgroupPreimage B).carrierVariety :=
      (P.inclusion.closedSubgroupPreimage B).carrierAlgebraicGroup
    (P.inclusion.comp (P.inclusion.closedSubgroupPreimage B).inclusion).imageClosedSubgroup = B := by
  let := (P.inclusion.closedSubgroupPreimage B).carrierAlgebraicGroup
  apply SetLike.coe_injective
  ext x
  change x ∈ (P.inclusion.comp
    (P.inclusion.closedSubgroupPreimage B).inclusion).imageClosedSubgroup ↔ x ∈ B
  rw [P.mem_inclusion_image_iff]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact hy
  · intro hx
    obtain ⟨y, rfl⟩ := (show x ∈ Set.range P.inclusion.onPoints by
      rw [P.range_inclusion]
      exact hBP hx)
    exact ⟨y, hx, rfl⟩

/-- An ambient Borel contained in a closed subgroup is a Borel of that subgroup. -/
public lemma IsBorelSubgroup.preimage_inclusion_of_le
    {G : Variety k} [AlgebraicGroup G] {B P : ClosedSubgroup G}
    (hB : IsBorelSubgroup B) (hBP : B ≤ P) :
    IsBorelSubgroup (P.inclusion.closedSubgroupPreimage B) := by
  let C := P.inclusion.closedSubgroupPreimage B
  let := C.carrierAlgebraicGroup
  let f := B.inclusion.codRestrictClosedSubgroup P (fun x => hBP (B.pointEquiv x).property)
  have hf (x) : P.inclusion.onPoints (f.onPoints x) = B.inclusion.onPoints x :=
    B.inclusion.codRestrictClosedSubgroup_inclusion_apply P _ x
  have himage : f.imageClosedSubgroup = C := by
    apply SetLike.coe_injective
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      change P.inclusion.onPoints (f.onPoints y) ∈ B
      rw [hf]
      exact (B.pointEquiv y).property
    · intro hx
      change P.inclusion.onPoints x ∈ B at hx
      obtain ⟨y, hy⟩ := (show P.inclusion.onPoints x ∈ Set.range B.inclusion.onPoints by
        rw [B.range_inclusion]
        exact hx)
      exact ⟨y, P.inclusion_injective ((hf y).trans hy)⟩
  have hCconnected : _root_.IsConnected (C : Set (Variety.Point P.carrierVariety)) := by
    rw [← himage]
    exact f.imageClosedSubgroup_isConnected (transitivity_carrier_connected B hB.connected)
  have hCsolvable : Group.IsSolvable (Variety.Point C.carrierVariety) := by
    change @Group.IsSolvable _ C.carrierAlgebraicGroup.toGroup
    rw [← himage]
    exact f.imageClosedSubgroup_isSolvable hB.solvable
  refine ⟨hCconnected, hCsolvable, ?_⟩
  intro D hDconn hDsolv hCD
  let := D.carrierAlgebraicGroup
  have hBD : B ≤ (P.inclusion.comp D.inclusion).imageClosedSubgroup := by
    rw [← P.inclusion_image_preimage_of_le B hBP]
    intro x hx
    obtain ⟨y, hy, rfl⟩ := (P.mem_inclusion_image_iff _ x).mp hx
    exact (P.mem_inclusion_image_iff D _).mpr ⟨y, hCD hy, rfl⟩
  have hDeq := hB.maximal (P.inclusion.comp D.inclusion).imageClosedSubgroup
    ((P.inclusion.comp D.inclusion).imageClosedSubgroup_isConnected
      (transitivity_carrier_connected D hDconn))
    ((P.inclusion.comp D.inclusion).imageClosedSubgroup_isSolvable hDsolv) hBD
  apply SetLike.coe_injective
  ext x
  change x ∈ D ↔ P.inclusion.onPoints x ∈ B
  rw [← hDeq, P.inclusion_mem_inclusion_image_iff]

/-- Conjugation inside a closed subgroup agrees with ambient conjugation of its image. -/
public lemma ClosedSubgroup.inclusion_image_conjugate
    {G : Variety k} [AlgebraicGroup G] (P : ClosedSubgroup G)
    (B : ClosedSubgroup P.carrierVariety) (g : Variety.Point P.carrierVariety) :
    letI := B.carrierAlgebraicGroup
    letI := (B.conjugate g).carrierAlgebraicGroup
    (P.inclusion.comp (B.conjugate g).inclusion).imageClosedSubgroup =
      ((P.inclusion.comp B.inclusion).imageClosedSubgroup).conjugate
        (P.inclusion.onPoints g) := by
  let := B.carrierAlgebraicGroup
  let := (B.conjugate g).carrierAlgebraicGroup
  apply SetLike.coe_injective
  ext x
  change x ∈ (P.inclusion.comp (B.conjugate g).inclusion).imageClosedSubgroup ↔
    x ∈ ((P.inclusion.comp B.inclusion).imageClosedSubgroup).conjugate (P.inclusion.onPoints g)
  rw [P.mem_inclusion_image_iff, ClosedSubgroup.mem_conjugate_iff]
  change (∃ y ∈ B.conjugate g, P.inclusion.onPoints y = x) ↔
    (P.inclusion.onPoints g)⁻¹ * x * P.inclusion.onPoints g ∈
      (P.inclusion.comp B.inclusion).imageClosedSubgroup
  rw [P.mem_inclusion_image_iff]
  constructor
  · rintro ⟨y, hy, rfl⟩
    refine ⟨g⁻¹ * y * g, (B.mem_conjugate_iff g y).mp hy, ?_⟩
    simp only [map_mul, map_inv]
  · rintro ⟨y, hy, heq⟩
    refine ⟨g * y * g⁻¹, ?_, ?_⟩
    · apply (B.mem_conjugate_iff g _).mpr
      change g⁻¹ * (g * y * g⁻¹) * g ∈ B
      simpa only [inv_mul_cancel_left, mul_assoc, inv_mul_cancel, mul_one] using hy
    · simp only [map_mul, map_inv, heq]
      group

/-- Assuming conjugacy of Borels inside a parabolic, each of its Borels has ambient Borel image. -/
public lemma isBorelSubgroup_inclusion_image_of_borel_conjugacy
    {G : Variety k} [AlgebraicGroup G] (P : ClosedSubgroup G)
    (hP : IsParabolicSubgroup P)
    (hconj : ∀ B₁ B₂ : ClosedSubgroup P.carrierVariety,
      IsBorelSubgroup B₁ → IsBorelSubgroup B₂ →
        ∃ g : Variety.Point P.carrierVariety, B₂ = B₁.conjugate g)
    (S : ClosedSubgroup P.carrierVariety) (hS : IsBorelSubgroup S) :
    letI := S.carrierAlgebraicGroup
    IsBorelSubgroup (P.inclusion.comp S.inclusion).imageClosedSubgroup := by
  let := S.carrierAlgebraicGroup
  obtain ⟨B, hB, hBP⟩ := hP
  let := (P.inclusion.closedSubgroupPreimage B).carrierAlgebraicGroup
  obtain ⟨g, hg⟩ := hconj (P.inclusion.closedSubgroupPreimage B) S
    (hB.preimage_inclusion_of_le hBP) hS
  rw [hg, P.inclusion_image_conjugate, P.inclusion_image_preimage_of_le B hBP]
  exact hB.conjugate _

/-- Ambient parabolic transitivity, conditional on Borel conjugacy in the intermediate subgroup. -/
public lemma isParabolicSubgroup_trans_of_borel_conjugacy
    {G : Variety k} [AlgebraicGroup G] (P : ClosedSubgroup G)
    (hP : IsParabolicSubgroup P)
    (hconj : ∀ B₁ B₂ : ClosedSubgroup P.carrierVariety,
      IsBorelSubgroup B₁ → IsBorelSubgroup B₂ →
        ∃ g : Variety.Point P.carrierVariety, B₂ = B₁.conjugate g)
    (S : ClosedSubgroup P.carrierVariety) (hS : IsParabolicSubgroup S) :
    letI := S.carrierAlgebraicGroup
    IsParabolicSubgroup (P.inclusion.comp S.inclusion).imageClosedSubgroup := by
  let := S.carrierAlgebraicGroup
  obtain ⟨B, hB, hBS⟩ := hS
  let := B.carrierAlgebraicGroup
  refine ⟨(P.inclusion.comp B.inclusion).imageClosedSubgroup,
    isBorelSubgroup_inclusion_image_of_borel_conjugacy P hP hconj B hB, ?_⟩
  intro x hx
  obtain ⟨y, hy, rfl⟩ := (P.mem_inclusion_image_iff B x).mp hx
  exact (P.mem_inclusion_image_iff S _).mpr ⟨y, hBS hy, rfl⟩

/-- Every Borel of a parabolic subgroup has Borel image in the ambient group.
This is the ambient Borel transfer used in GLS3, Section 3.1. -/
public theorem isBorelSubgroup_inclusion_image
    {G : Variety k} [AlgebraicGroup G] (P : ClosedSubgroup G)
    (hP : IsParabolicSubgroup P)
    (S : ClosedSubgroup P.carrierVariety) (hS : IsBorelSubgroup S) :
    letI := S.carrierAlgebraicGroup
    IsBorelSubgroup (P.inclusion.comp S.inclusion).imageClosedSubgroup := by
  exact isBorelSubgroup_inclusion_image_of_borel_conjugacy P hP
    (fun _ _ h₁ h₂ => BorelGeometricConjugacy.conjugacy h₁ h₂) S hS

/-- A parabolic subgroup of a parabolic subgroup is parabolic in the ambient
group. Applied after quotient lifting inside `P`, this discharges the ambient
transfer in the proof of GLS3, Theorem 3.1.3. -/
public theorem isParabolicSubgroup_trans
    {G : Variety k} [AlgebraicGroup G] (P : ClosedSubgroup G)
    (hP : IsParabolicSubgroup P)
    (S : ClosedSubgroup P.carrierVariety) (hS : IsParabolicSubgroup S) :
    letI := S.carrierAlgebraicGroup
    IsParabolicSubgroup (P.inclusion.comp S.inclusion).imageClosedSubgroup := by
  exact isParabolicSubgroup_trans_of_borel_conjugacy P hP
    (fun _ _ h₁ h₂ => BorelGeometricConjugacy.conjugacy h₁ h₂) S hS

end Theory.AlgebraicGroup
