module

public import Theory.AlgebraicGroup.Borel.Existence
public import Theory.AlgebraicGroup.ClosedSubgroup.Conjugation
public import Theory.AlgebraicGroup.Tori.Character.Image
/-!
# Reduction of torus conjugacy to Borel and solvable conjugacy

Put each maximal torus in a Borel, conjugate the Borels, and then conjugate the
two tori inside the common connected solvable carrier. The proof checks both
relative maximality and the return to ambient conjugation. Our convention is
`T.conjugate g = g T g⁻¹`, so the two conjugators compose in reverse order.

Both conjugacy inputs remain explicit here. The solvable input is the theorem
`maximalTori_conjugate_of_solvable_connected` in `Solvable.MaximalTorusConjugacy`;
the geometric Borel input is still pending. This reduction uses neither the
unresolved numbered torus theorem nor the unresolved Borel-pair theorem.

Source: GLS3, Theorem 1.4.3(b); Borel, *Linear Algebraic Groups*,
Chapter III, Theorem 10.6(4) and Corollary 11.3(1).
-/

public section

open Theory.AlgebraicGroup
namespace Theory.AlgebraicGroup.F4Chevalley.TorusConjugacy
universe u
variable {k : Type u} [Field k] [IsAlgClosed k]
  {G : Variety k} [AlgebraicGroup G]

private noncomputable def inside (T B : ClosedSubgroup G) (h : T ≤ B) :
    ClosedSubgroup B.carrierVariety :=
  (T.inclusion.codRestrictClosedSubgroup B
    (fun x => h (T.pointEquiv x).property)).imageClosedSubgroup

private theorem mem_inside (T B : ClosedSubgroup G) (h : T ≤ B)
    (x : Variety.Point B.carrierVariety) :
    x ∈ inside T B h ↔ B.inclusion.onPoints x ∈ T := by
  let f := T.inclusion.codRestrictClosedSubgroup B
    (fun y => h (T.pointEquiv y).property)
  have hf (y) : B.inclusion.onPoints (f.onPoints y) = T.inclusion.onPoints y :=
    T.inclusion.codRestrictClosedSubgroup_inclusion_apply B _ y
  change (∃ y, f.onPoints y = x) ↔ B.inclusion.onPoints x ∈ T
  constructor
  · rintro ⟨y, rfl⟩
    rw [hf]
    exact (T.pointEquiv y).property
  · intro hx
    refine ⟨T.pointEquiv.symm ⟨B.inclusion.onPoints x, hx⟩,
      B.inclusion_injective ?_⟩
    rw [hf]
    exact congrArg Subtype.val (T.pointEquiv.apply_symm_apply _)

private theorem inside_maximal (T B : ClosedSubgroup G)
    (hT : IsMaximalTorus T) (h : T ≤ B) : IsMaximalTorus (inside T B h) := by
  refine ⟨morphism_image_isTorus _ hT.1, ?_⟩
  intro S hS hTS
  let _ := S.carrierAlgebraicGroup
  let f := B.inclusion.comp S.inclusion
  have hf : IsSubtorus f.imageClosedSubgroup := morphism_image_isTorus f hS
  have hTf : T ≤ f.imageClosedSubgroup := by
    intro x hx
    let y := B.pointEquiv.symm ⟨x, h hx⟩
    have hy : B.inclusion.onPoints y = x :=
      congrArg Subtype.val (B.pointEquiv.apply_symm_apply _)
    have hyS : y ∈ S := hTS ((mem_inside T B h y).mpr (hy.symm ▸ hx))
    refine ⟨S.pointEquiv.symm ⟨y, hyS⟩, ?_⟩
    change B.inclusion.onPoints ((S.pointEquiv (S.pointEquiv.symm ⟨y, hyS⟩)).val) = x
    rw [S.pointEquiv.apply_symm_apply]
    exact hy
  have heq := hT.2 _ hf hTf
  apply SetLike.coe_injective
  apply Set.Subset.antisymm _ hTS
  intro y hy
  apply (mem_inside T B h y).mpr
  rw [← heq]
  refine ⟨S.pointEquiv.symm ⟨y, hy⟩, ?_⟩
  change B.inclusion.onPoints ((S.pointEquiv (S.pointEquiv.symm ⟨y, hy⟩)).val) = _
  rw [S.pointEquiv.apply_symm_apply]

omit [IsAlgClosed k] in
private theorem conjugate_le (T B : ClosedSubgroup G) (h : T ≤ B)
    (g : Variety.Point G) : T.conjugate g ≤ B.conjugate g := by
  intro x hx
  exact (B.mem_conjugate_iff g x).mpr (h ((T.mem_conjugate_iff g x).mp hx))

omit [IsAlgClosed k] in
private theorem conjugate_maximal (T : ClosedSubgroup G) (hT : IsMaximalTorus T)
    (g : Variety.Point G) : IsMaximalTorus (T.conjugate g) := by
  have torus (S : ClosedSubgroup G) (hS : IsSubtorus S) (x : Variety.Point G) :
      IsSubtorus (S.conjugate x) := by
    obtain ⟨n, ⟨e⟩⟩ := hS
    exact ⟨n, ⟨(S.conjugateIso x).comp e⟩⟩
  refine ⟨torus T hT.1 g, ?_⟩
  intro S hS hTS
  have hback := conjugate_le _ _ hTS g⁻¹
  rw [ClosedSubgroup.conjugate_conjugate, inv_mul_cancel, ClosedSubgroup.conjugate_one] at hback
  have heq := hT.2 _ (torus S hS g⁻¹) hback
  have heq' := congrArg (fun H : ClosedSubgroup G => H.conjugate g) heq
  simpa only [ClosedSubgroup.conjugate_conjugate, mul_inv_cancel,
    ClosedSubgroup.conjugate_one] using heq'

private theorem exists_borel_over_torus (T : ClosedSubgroup G) (hT : IsSubtorus T) :
    ∃ B : ClosedSubgroup G, IsBorelSubgroup B ∧ T ≤ B := by
  have hconn : _root_.IsConnected (T : Set (Variety.Point G)) := by
    let : ConnectedSpace (Variety.Point T.carrierVariety) :=
      connectedSpace_iff_univ.mpr hT.isConnected
    change _root_.IsConnected (T.toSubgroup : Set (Variety.Point G))
    rw [← T.range_inclusion]
    exact isConnected_range T.inclusion.toVariety.continuous
  exact exists_borelSubgroup_containing_connected_solvable T hconn
    (Group.isSolvable_of_comm (isMulCommutative_iff.mp hT.isMulCommutative))

private theorem conjugacy_of_inside_conjugacy
    (B T₁ T₂ : ClosedSubgroup G) (h₁ : T₁ ≤ B) (h₂ : T₂ ≤ B)
    (b : Variety.Point B.carrierVariety)
    (hb : inside T₂ B h₂ = (inside T₁ B h₁).conjugate b) :
    T₂ = T₁.conjugate (B.inclusion.onPoints b) := by
  have hbB : B.inclusion.onPoints b ∈ B.toSubgroup := (B.pointEquiv b).property
  apply SetLike.coe_injective
  ext x
  rw [SetLike.mem_coe, SetLike.mem_coe, T₁.mem_conjugate_iff]
  by_cases hxB : x ∈ B
  · let y := B.pointEquiv.symm ⟨x, hxB⟩
    have hy : B.inclusion.onPoints y = x :=
      congrArg Subtype.val (B.pointEquiv.apply_symm_apply _)
    have he := (mem_inside T₂ B h₂ y).symm
    rw [hb, ClosedSubgroup.mem_conjugate_iff] at he
    change B.inclusion.onPoints y ∈ T₂ ↔ b⁻¹ * y * b ∈ inside T₁ B h₁ at he
    rw [mem_inside] at he
    change x ∈ T₂ ↔ (B.inclusion.onPoints b)⁻¹ * x * B.inclusion.onPoints b ∈ T₁
    simpa only [map_mul, map_inv, hy] using he
  · constructor
    · intro hx
      exact (hxB (h₂ hx)).elim
    · intro hx
      have hz := h₁ hx
      have hx' := B.toSubgroup.mul_mem (B.toSubgroup.mul_mem hbB hz)
        (B.toSubgroup.inv_mem hbB)
      apply False.elim
      apply hxB
      change x ∈ B.toSubgroup
      simpa only [mul_assoc, mul_inv_cancel_left, mul_inv_cancel_right,
        mul_inv_cancel, mul_one] using hx'

/-- Borel conjugacy and conjugacy within each Borel imply ambient torus conjugacy. -/
theorem maximalTori_conjugate_of_borel_and_solvable_conjugacy
    (hBorel : ∀ B C : ClosedSubgroup G, IsBorelSubgroup B → IsBorelSubgroup C →
      ∃ g : Variety.Point G, C = B.conjugate g)
    (hsolv : ∀ B : ClosedSubgroup G, IsBorelSubgroup B →
      ∀ T₁ T₂ : ClosedSubgroup B.carrierVariety,
        IsMaximalTorus T₁ → IsMaximalTorus T₂ →
        ∃ b : Variety.Point B.carrierVariety, T₂ = T₁.conjugate b)
    (T₁ T₂ : ClosedSubgroup G) (hT₁ : IsMaximalTorus T₁) (hT₂ : IsMaximalTorus T₂) :
    ∃ g : Variety.Point G, T₂ = T₁.conjugate g := by
  obtain ⟨B₁, hB₁, h₁⟩ := exists_borel_over_torus T₁ hT₁.1
  obtain ⟨B₂, hB₂, h₂⟩ := exists_borel_over_torus T₂ hT₂.1
  obtain ⟨g, hg⟩ := hBorel B₁ B₂ hB₁ hB₂
  have h₁g : T₁.conjugate g ≤ B₂ := hg.symm ▸ conjugate_le T₁ B₁ h₁ g
  obtain ⟨b, hb⟩ := hsolv B₂ hB₂ (inside (T₁.conjugate g) B₂ h₁g)
    (inside T₂ B₂ h₂) (inside_maximal _ _ (conjugate_maximal T₁ hT₁ g) h₁g)
    (inside_maximal _ _ hT₂ h₂)
  refine ⟨B₂.inclusion.onPoints b * g, ?_⟩
  rw [← ClosedSubgroup.conjugate_conjugate]
  exact conjugacy_of_inside_conjugacy B₂ _ T₂ h₁g h₂ b hb
end Theory.AlgebraicGroup.F4Chevalley.TorusConjugacy
