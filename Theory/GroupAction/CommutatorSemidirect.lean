module

public import Mathlib.GroupTheory.SemidirectProduct
public import Theory.GroupAction.Defs

open scoped Pointwise commutatorElement

namespace Theory.GroupAction

variable {G A : Type*} [Group G] [Group A] [MulDistribMulAction A G]

private theorem semidirect_comm_inl_inv_inr_for_commutatorSubgroup
    (φ : A →* MulAut G) (a : A) (g : G) :
    ⁅((SemidirectProduct.inl (φ := φ) g : G ⋊[φ] A)⁻¹),
      (SemidirectProduct.inr (φ := φ) a : G ⋊[φ] A)⁆ =
        SemidirectProduct.inl (φ := φ) (g⁻¹ * (φ a) g) := by
  let inl : G →* G ⋊[φ] A := SemidirectProduct.inl
  let inr : A →* G ⋊[φ] A := SemidirectProduct.inr
  have hconj :
      (inr a : G ⋊[φ] A) * (inl g : G ⋊[φ] A) * (inr a : G ⋊[φ] A)⁻¹ =
        inl ((φ a) g) := by
    simpa [inl, inr] using (SemidirectProduct.inl_aut (φ := φ) a g).symm
  calc
    ⁅((inl g : G ⋊[φ] A)⁻¹), inr a⁆ =
        (inl g : G ⋊[φ] A)⁻¹ * (inr a : G ⋊[φ] A) *
          ((inl g : G ⋊[φ] A)⁻¹)⁻¹ * (inr a : G ⋊[φ] A)⁻¹ := by
      rw [commutatorElement_def]
    _ = (inl g : G ⋊[φ] A)⁻¹ *
        ((inr a : G ⋊[φ] A) * (inl g : G ⋊[φ] A) * (inr a : G ⋊[φ] A)⁻¹) := by
      simp [mul_assoc]
    _ = (inl g : G ⋊[φ] A)⁻¹ * inl ((φ a) g) := by rw [hconj]
    _ = inl (g⁻¹ * (φ a) g) := by simp [inl]

/-- The subgroup action commutator is monotone in the subgroup being acted on. -/
public theorem commutatorSubgroup_mono {H K : Subgroup G} (hHK : H ≤ K) :
    commutatorSubgroup A G H ≤ commutatorSubgroup A G K := by
  rw [commutatorSubgroup, commutatorSubgroup]
  apply Subgroup.closure_mono
  rintro x ⟨a, g, hg, rfl⟩
  exact ⟨a, g, hHK hg, rfl⟩

/-- Embed an action commutator into the associated semidirect product. -/
public theorem commutatorSubgroup_map_semidirect_inl_eq_commutator
    (B : Subgroup A) (H : Subgroup G) :
    let φ : A →* MulAut G := MulDistribMulAction.toMulAut A G
    let inl : G →* G ⋊[φ] A := SemidirectProduct.inl
    let inr : A →* G ⋊[φ] A := SemidirectProduct.inr
    (commutatorSubgroup B G H).map inl = ⁅H.map inl, B.map inr⁆ := by
  let φ : A →* MulAut G := MulDistribMulAction.toMulAut A G
  let SD := G ⋊[φ] A
  letI : Group SD := by infer_instance
  let inl : G →* SD := SemidirectProduct.inl
  let inr : A →* SD := SemidirectProduct.inr
  let X : Set G :=
    {x : G | ∃ b : B, ∃ g : G, g ∈ H ∧ x = g⁻¹ * (b • g)}
  have hcomm (b : B) (g : G) :
      ⁅((inl g : SD)⁻¹), inr (b : A)⁆ = inl (g⁻¹ * (b • g)) := by
    simpa [SD, inl, inr, φ, Subgroup.smul_def] using
      (semidirect_comm_inl_inv_inr_for_commutatorSubgroup φ (b : A) g)
  have hdef : commutatorSubgroup B G H = Subgroup.closure X := by
    rfl
  change (commutatorSubgroup B G H).map inl = ⁅H.map inl, B.map inr⁆
  rw [hdef, MonoidHom.map_closure]
  refine le_antisymm ?_ ?_
  · refine (Subgroup.closure_le (K := ⁅H.map inl, B.map inr⁆)).2 ?_
    rintro x ⟨y, ⟨b, g, hg, rfl⟩, rfl⟩
    have hgH : inl g ∈ H.map inl := Subgroup.mem_map_of_mem inl hg
    have hginv : (inl g : SD)⁻¹ ∈ H.map inl := (H.map inl).inv_mem hgH
    have hbB : inr (b : A) ∈ B.map inr := Subgroup.mem_map_of_mem inr b.property
    simpa [hcomm] using Subgroup.commutator_mem_commutator hginv hbB
  · refine Subgroup.commutator_le.mpr ?_
    rintro _ ⟨g, hg, rfl⟩ _ ⟨b, hb, rfl⟩
    let b' : B := ⟨b, hb⟩
    have hmem : inl (g * (b • g)⁻¹) ∈ Subgroup.closure (inl '' X) := by
      refine Subgroup.subset_closure ⟨g * (b • g)⁻¹, ?_, rfl⟩
      refine ⟨b', g⁻¹, H.inv_mem hg, ?_⟩
      simp [b', Subgroup.smul_def]
    have hcomm' : ⁅inl g, inr b⁆ = inl (g * (b • g)⁻¹) := by
      simpa [inv_inv, b', Subgroup.smul_def] using hcomm b' g⁻¹
    simpa [hcomm'] using hmem

end Theory.GroupAction
