module

public import Theory.AlgebraicGroup.Borel.SelfNormalizer.TorusReduction
public import Theory.AlgebraicGroup.Borel.GeometricConjugacy
public import Theory.AlgebraicGroup.Parabolic.Transitivity
public import Theory.AlgebraicGroup.Unipotent.SemisimpleCommutator

set_option backward.isDefEq.respectTransparency false

/-!
# Maximal-torus conjugacy and normalizers in a centralizer

Borel conjugacy and conjugacy of maximal tori inside a connected solvable group
prove conjugacy of ambient maximal tori inside any closed subgroup containing
them. Applied inside the identity component, this reduces connectedness of a
subgroup containing a maximal torus to its torus normalizer. Applied inside a
point centralizer, it proves that ambient conjugacy of two toral points is
realized by the actual torus normalizer, without a connected-centralizer premise.

Sources: Borel, *Linear Algebraic Groups*, §11.3; Steinberg, *Endomorphisms of
Linear Algebraic Groups*, §3. These source reductions feed the actual F4
semisimple centralizer and Ree class-count constructions.
-/

public noncomputable section

namespace Theory.AlgebraicGroup.SemisimpleCentralizerTori
open BorelIntersectionGeometry
universe u
variable {k : Type u} [Field k] [IsAlgClosed k]
variable {G : Variety k} [AlgebraicGroup G]
attribute [local instance] ClosedSubgroup.carrierAlgebraicGroup

private theorem borel_containing {T : ClosedSubgroup G} (hT : IsSubtorus T) :
    ∃ B : ClosedSubgroup G, IsBorelSubgroup B ∧ T ≤ B := by
  have hconn : _root_.IsConnected (T : Set (Variety.Point G)) := by
    let : ConnectedSpace (Variety.Point T.carrierVariety) :=
      connectedSpace_iff_univ.mpr hT.isConnected
    change _root_.IsConnected (T.toSubgroup : Set (Variety.Point G))
    rw [← T.range_inclusion]
    exact isConnected_range T.inclusion.toVariety.continuous
  exact exists_borelSubgroup_containing_connected_solvable T hconn
    (Group.isSolvable_of_comm (isMulCommutative_iff.mp hT.isMulCommutative))

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


theorem maximalTori_conjugate {T S : ClosedSubgroup G}
    (hT : IsMaximalTorus T) (hS : IsMaximalTorus S) :
    ∃ g : Variety.Point G, S = T.conjugate g := by
  obtain ⟨B, hB, hTB⟩ := borel_containing hT.1
  obtain ⟨C, hC, hSC⟩ := borel_containing hS.1
  obtain ⟨g, rfl⟩ := BorelGeometricConjugacy.conjugacy hB hC
  have hSgB : S.conjugate g⁻¹ ≤ B := by
    have h := conjugate_le hSC g⁻¹
    rwa [ClosedSubgroup.conjugate_conjugate, inv_mul_cancel, ClosedSubgroup.conjugate_one] at h
  obtain ⟨b, hb, he⟩ := BorelSelfNormalizer.maximalTori_conjugate_inside_borel hB hT
    (conjugate_isMaximalTorus hS g⁻¹) hTB hSgB
  refine ⟨g * b, ?_⟩
  rw [← ClosedSubgroup.conjugate_conjugate, ← he,
    ClosedSubgroup.conjugate_conjugate, mul_inv_cancel, ClosedSubgroup.conjugate_one]

private theorem image_inside (T H : ClosedSubgroup G) (hTH : T ≤ H) :
    letI := (inside T H hTH).carrierAlgebraicGroup
    (H.inclusion.comp (inside T H hTH).inclusion).imageClosedSubgroup = T := by
  let := (inside T H hTH).carrierAlgebraicGroup
  apply SetLike.coe_injective
  ext x
  change x ∈ (H.inclusion.comp (inside T H hTH).inclusion).imageClosedSubgroup ↔ x ∈ T
  rw [H.mem_inclusion_image_iff]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact (mem_inside T H hTH y).mp hy
  · intro hx
    let y := H.pointEquiv.symm ⟨x, hTH hx⟩
    have hy : H.inclusion.onPoints y = x := congrArg Subtype.val (H.pointEquiv.apply_symm_apply _)
    exact ⟨y, (mem_inside T H hTH y).mpr (hy.symm ▸ hx), hy⟩

theorem maximalTori_conjugate_inside {T S H : ClosedSubgroup G}
    (hT : IsMaximalTorus T) (hS : IsMaximalTorus S) (hTH : T ≤ H) (hSH : S ≤ H) :
    ∃ g : Variety.Point G, g ∈ H ∧ S = T.conjugate g := by
  obtain ⟨g, hg⟩ := maximalTori_conjugate (inside_isMaximalTorus T H hTH hT)
    (inside_isMaximalTorus S H hSH hS)
  have hm := congrArg (fun A : ClosedSubgroup H.carrierVariety =>
    letI := A.carrierAlgebraicGroup
    (H.inclusion.comp A.inclusion).imageClosedSubgroup) hg
  rw [H.inclusion_image_conjugate, image_inside, image_inside] at hm
  exact ⟨H.inclusion.onPoints g, (H.pointEquiv g).property, hm⟩

omit [IsAlgClosed k] in
private theorem normalizer_of_conjugate_eq {T : ClosedSubgroup G}
    {n : Variety.Point G} (hn : T.conjugate n = T) : n ∈ T.normalizer.toSubgroup := by
  apply Subgroup.mem_normalizer_iff.mpr
  intro x
  change x ∈ T ↔ n * x * n⁻¹ ∈ T
  have h := T.mem_conjugate_iff n (n * x * n⁻¹)
  rw [hn] at h
  change (n * x * n⁻¹ ∈ T) ↔ (n⁻¹ * (n * x * n⁻¹) * n ∈ T) at h
  simpa only [inv_mul_cancel_left, mul_assoc, inv_mul_cancel, mul_one] using h.symm

/-- A subgroup containing an ambient maximal torus is connected as soon as
its torus normalizer lies in its identity component. -/
theorem connected_of_normalizer_le_component (H T : ClosedSubgroup G)
    (hT : IsMaximalTorus T) (hTH : T ≤ H)
    (hN : ∀ n : Variety.Point G, n ∈ H → n ∈ T.normalizer.toSubgroup →
      n ∈ H.identityComponentAmbient) :
    _root_.IsConnected (H : Set (Variety.Point G)) := by
  have he : H = H.identityComponentAmbient := by
    apply SetLike.coe_injective
    apply Set.Subset.antisymm _ H.identityComponentAmbient_le
    intro h hh
    have hThH : T.conjugate h ≤ H := by
      intro x hx
      have hxT := (T.mem_conjugate_iff h x).mp hx
      have hc := H.toSubgroup.mul_mem (H.toSubgroup.mul_mem hh (hTH hxT))
        (H.toSubgroup.inv_mem hh)
      change h * (h⁻¹ * x * h) * h⁻¹ ∈ H at hc
      have heq : h * (h⁻¹ * x * h) * h⁻¹ = x := by group
      rwa [heq] at hc
    obtain ⟨b, hb, he⟩ := maximalTori_conjugate_inside hT (conjugate_isMaximalTorus hT h)
      (maximalTorus_le_identityComponentAmbient_of_le T H hT hTH)
      (maximalTorus_le_identityComponentAmbient_of_le (T.conjugate h) H
        (conjugate_isMaximalTorus hT h) hThH)
    have hn : b⁻¹ * h ∈ T.normalizer.toSubgroup := by
      apply normalizer_of_conjugate_eq
      rw [← ClosedSubgroup.conjugate_conjugate, he,
        ClosedSubgroup.conjugate_conjugate, inv_mul_cancel, ClosedSubgroup.conjugate_one]
    have hnH : b⁻¹ * h ∈ H := H.toSubgroup.mul_mem
      (H.toSubgroup.inv_mem (H.identityComponentAmbient_le hb)) hh
    have hnc := hN _ hnH hn
    have hc := H.identityComponentAmbient.toSubgroup.mul_mem hb hnc
    change b * (b⁻¹ * h) ∈ H.identityComponentAmbient at hc
    rwa [mul_inv_cancel_left] at hc
  rw [he]
  exact H.identityComponentAmbient_isConnected


/-- Ambient conjugacy of two points of one maximal torus is realized in its
actual normalizer. No connected-centralizer premise is needed. -/
theorem normalizer_conjugator_of_toral_conjugacy {T : ClosedSubgroup G}
    (hT : IsMaximalTorus T) {x y : Variety.Point G} (hx : x ∈ T) (hy : y ∈ T)
    (hxy : IsConj x y) :
    ∃ n : Variety.Point G, n ∈ T.normalizer.toSubgroup ∧ n * x * n⁻¹ = y := by
  obtain ⟨g, hg⟩ := isConj_iff.mp hxy
  let C := semisimpleCommutatorPointCentralizer y
  have hTC : T ≤ C := by
    intro t ht
    apply Subgroup.mem_centralizer_singleton_iff.mpr
    exact (Subgroup.mem_centralizer_iff.mp (maximalTorus_le_centralizer hT ht) y hy).symm
  have hTgC : T.conjugate g ≤ C := by
    intro t ht
    have hu := (T.mem_conjugate_iff g t).mp ht
    have hc := Subgroup.mem_centralizer_iff.mp (maximalTorus_le_centralizer hT hu) x hx
    apply Subgroup.mem_centralizer_singleton_iff.mpr
    rw [← hg]
    calc
      t * (g * x * g⁻¹) = g * ((g⁻¹ * t * g) * x) * g⁻¹ := by group
      _ = g * (x * (g⁻¹ * t * g)) * g⁻¹ := by rw [hc]
      _ = (g * x * g⁻¹) * t := by group
  obtain ⟨b, hb, he⟩ := maximalTori_conjugate_inside hT (conjugate_isMaximalTorus hT g) hTC hTgC
  have hn : b⁻¹ * g ∈ T.normalizer.toSubgroup := by
    apply normalizer_of_conjugate_eq
    rw [← ClosedSubgroup.conjugate_conjugate, he,
      ClosedSubgroup.conjugate_conjugate, inv_mul_cancel, ClosedSubgroup.conjugate_one]
  have hby : b * y = y * b := Subgroup.mem_centralizer_singleton_iff.mp hb
  refine ⟨b⁻¹ * g, hn, ?_⟩
  calc
    _ = b⁻¹ * (g * x * g⁻¹) * b := by group
    _ = b⁻¹ * y * b := by rw [hg]
    _ = b⁻¹ * (y * b) := by rw [mul_assoc]
    _ = y := by rw [← hby, inv_mul_cancel_left]

end Theory.AlgebraicGroup.SemisimpleCentralizerTori
