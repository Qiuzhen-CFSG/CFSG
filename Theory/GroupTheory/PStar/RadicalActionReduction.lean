module

public import Theory.GroupTheory.PStar.ActionProducts
public import Theory.GroupTheory.PStar.ExtensionCentralSylow
public import Theory.GroupTheory.PStar.Radical
public import Mathlib.GroupTheory.SemidirectProduct

/-!
# Two-star radicals and the internal-action reduction

The proved Sylow-centralizer theorem GLS II 5.4 supplies the sole input to
normal-product closure. Hence the two-star radical is itself two-star,
and its normal-subgroup and residual invariance statements are unconditional.
Passing from a normal subgroup to an ambient group with two-group quotient
does not change its embedded two-star radical.

For an actual two-group action, this applies first to G inside G semidirect A.
Inside the centralizer of the embedded actor, the right projection lands in
Z(A) and has kernel exactly the embedded fixed subgroup C_G(A). Applying the
same radical invariance gives both equalities in the opening reduction of
GLS II 5.11. The final equivalence reduces external-action balance to the
literal internal-centralizer assertion, without assuming either assertion.

Source: `refs/KGroup/GLS2/ChapterB.tex`, 5.5--5.8(i),(ii), and the opening
paragraph of 5.11. General extension 5.3 and the Sylow bound 5.9 are not used.
-/

public section
open Subgroup Theory.GroupTheory

namespace Subgroup
variable {G : Type*} [Group G] [Finite G]

/-- The two-star radical is two-star, with GLS 5.4 discharged by the
published Sylow-centralizer theorem. -/
theorem isPStar_twoStarCore : IsPStar 2 (pStarCore 2 G) := by
  apply isPStar_pStarCore_of_normal_sup
  intro N M hN hM hNs hMs
  let : N.Normal := hN
  let : M.Normal := hM
  exact IsPStar.normal_sup_of_centralizerResidual
    (fun Y _ _ hY K _ P => hY.isPStar_pResidual_centralizer K P) N M hNs hMs

/-- Normal-subgroup monotonicity of the two-star radical, with the actual
subtype embedding and no additional radical hypothesis. -/
theorem map_twoStarCore_subtype_le (N : Subgroup G) [N.Normal] :
    (pStarCore 2 N).map N.subtype ≤ pStarCore 2 G :=
  map_pStarCore_subtype_le_of_isPStar N isPStar_twoStarCore

/-- A normal subgroup with two-group quotient has the same embedded
two-star radical as the ambient group. -/
theorem map_twoStarCore_subtype_eq_of_pgroup_quotient
    (N : Subgroup G) [N.Normal] (hquot : IsPGroup 2 (G ⧸ N)) :
    (pStarCore 2 N).map N.subtype = pStarCore 2 G := by
  apply le_antisymm (map_twoStarCore_subtype_le N)
  apply pStarCore_le_map_of_le
  exact pStarCore_le_pResidual.trans (sInf_le ⟨inferInstance, hquot⟩)

/-- GLS 5.8(ii), with both intrinsic radicals embedded in the original group. -/
theorem map_twoStarCore_pResidual_eq :
    (pStarCore 2 (pResidual 2 G)).map (pResidual 2 G).subtype = pStarCore 2 G :=
  map_pStarCore_pResidual_eq_of_isPStar isPStar_twoStarCore

private theorem map_twoStarCore_eq_of_range_eq_ker
    {H B : Type*} [Group H] [Finite H] [Group B]
    (f : G →* H) (hf : Function.Injective f) (q : H →* B)
    (hB : IsPGroup 2 B) (hker : f.range = q.ker) :
    (pStarCore 2 G).map f = pStarCore 2 H := by
  let : f.range.Normal := by rw [hker]; infer_instance
  have hquot : IsPGroup 2 (H ⧸ f.range) := by
    exact ((hB.to_subgroup q.range).of_equiv
      (QuotientGroup.quotientKerEquivRange q).symm).of_equiv
        (QuotientGroup.quotientMulEquivOfEq hker).symm
  let e : G ≃* f.range := MonoidHom.ofInjective hf
  calc
    (pStarCore 2 G).map f = ((pStarCore 2 G).map e.toMonoidHom).map f.range.subtype := by
      rw [map_map]
      rfl
    _ = (pStarCore 2 f.range).map f.range.subtype := by rw [map_pStarCore e]
    _ = pStarCore 2 H := map_twoStarCore_subtype_eq_of_pgroup_quotient f.range hquot

end Subgroup

namespace Theory.GroupTheory.PStarAction
variable {G A : Type*} [Group G] [Group A] [MulDistribMulAction A G]

local notation "SD" => G ⋊[MulDistribMulAction.toMulAut A G] A
local notation "actor" => MonoidHom.range (SemidirectProduct.inr : A →* SD)
local notation "CSD" => centralizer (actor : Set SD)

private theorem inl_mem_actor_centralizer_iff (g : G) :
    (SemidirectProduct.inl g : SD) ∈ CSD ↔ g ∈ fixedPointSubgroup A G := by
  constructor
  · intro hg a
    have he := congrArg SemidirectProduct.left
      (mem_centralizer_iff.mp hg (SemidirectProduct.inr a) ⟨a, rfl⟩)
    simpa only [SemidirectProduct.mul_left, SemidirectProduct.left_inr,
      SemidirectProduct.right_inr, SemidirectProduct.left_inl,
      SemidirectProduct.right_inl, one_mul, map_one, MulAut.one_apply, mul_one,
      MulDistribMulAction.toMulAut_apply, MulDistribMulAction.toMulEquiv_apply] using he
  · intro hg
    apply mem_centralizer_iff.mpr
    rintro _ ⟨a, rfl⟩
    apply SemidirectProduct.ext
    · simpa only [SemidirectProduct.mul_left, SemidirectProduct.left_inr,
        SemidirectProduct.right_inr, SemidirectProduct.left_inl,
        SemidirectProduct.right_inl, one_mul, map_one, MulAut.one_apply, mul_one,
      MulDistribMulAction.toMulAut_apply, MulDistribMulAction.toMulEquiv_apply]
        using hg a
    · simp only [SemidirectProduct.mul_right, SemidirectProduct.right_inr,
        SemidirectProduct.right_inl, mul_one, one_mul]

private def fixedPointInl : fixedPointSubgroup A G →* CSD :=
  ((SemidirectProduct.inl : G →* SD).comp (fixedPointSubgroup A G).subtype).codRestrict _
    (fun x => (inl_mem_actor_centralizer_iff (x : G)).mpr x.property)

private theorem fixedPointInl_injective :
    Function.Injective (fixedPointInl (G := G) (A := A)) := by
  intro x y h
  apply Subtype.ext
  exact SemidirectProduct.inl_injective (congrArg Subtype.val h)

private theorem centralizer_right_mem_center (x : CSD) : (x : SD).right ∈ center A := by
  apply mem_center_iff.mpr
  intro a
  have he := congrArg SemidirectProduct.right
    (mem_centralizer_iff.mp x.property (SemidirectProduct.inr a) ⟨a, rfl⟩)
  simpa only [SemidirectProduct.mul_right, SemidirectProduct.right_inr] using he

private def centralizerRight : CSD →* center A :=
  ((SemidirectProduct.rightHom : SD →* A).comp (CSD).subtype).codRestrict _
    centralizer_right_mem_center

private theorem fixedPointInl_range_eq_ker :
    (fixedPointInl (G := G) (A := A)).range = centralizerRight.ker := by
  ext x
  constructor
  · rintro ⟨g, rfl⟩
    apply Subtype.ext
    rfl
  · intro hx
    have hr : (x : SD).right = 1 := congrArg Subtype.val hx
    have he : (SemidirectProduct.inl (x : SD).left : SD) = x :=
      SemidirectProduct.ext rfl hr.symm
    have hf : (x : SD).left ∈ fixedPointSubgroup A G := by
      apply (inl_mem_actor_centralizer_iff _).mp
      rw [he]
      exact x.property
    exact ⟨⟨(x : SD).left, hf⟩, Subtype.ext he⟩

section Finite
variable [Finite G] [Finite A]
local instance : Finite SD := Finite.of_equiv (G × A) SemidirectProduct.equivProd.symm

/-- The first radical equality in the opening reduction of GLS 5.11:
the literal inclusion in the action semidirect product preserves the core. -/
theorem map_twoStarCore_semidirect_inl (hA : IsPGroup 2 A) :
    (pStarCore 2 G).map (SemidirectProduct.inl : G →* SD) = pStarCore 2 SD :=
  Subgroup.map_twoStarCore_eq_of_range_eq_ker SemidirectProduct.inl
    SemidirectProduct.inl_injective SemidirectProduct.rightHom hA
    SemidirectProduct.range_inl_eq_ker_rightHom

/-- The second radical equality in GLS 5.11's reduction. The actor projection
has values in Z(A) and kernel exactly the embedded C_G(A). -/
theorem map_twoStarCore_fixedPoint_semidirect (hA : IsPGroup 2 A) :
    ((pStarCore 2 (fixedPointSubgroup A G)).map (fixedPointSubgroup A G).subtype).map
        (SemidirectProduct.inl : G →* SD) =
      (pStarCore 2 CSD).map (CSD).subtype := by
  have he := Subgroup.map_twoStarCore_eq_of_range_eq_ker
    (fixedPointInl (G := G) (A := A)) fixedPointInl_injective centralizerRight
    (hA.to_subgroup (center A)) fixedPointInl_range_eq_ker
  have hm := congrArg (Subgroup.map (CSD).subtype) he
  have hcomp : (CSD).subtype.comp (fixedPointInl (G := G) (A := A)) =
      (SemidirectProduct.inl : G →* SD).comp (fixedPointSubgroup A G).subtype := by
    exact MonoidHom.ext (fun _ => rfl)
  rw [Subgroup.map_map, hcomp] at hm
  simpa only [Subgroup.map_map] using hm

/-- The exact external-to-internal balance reduction used in GLS 5.11.
This establishes the equivalence, without assuming either balance assertion. -/
theorem twoStarCore_balance_iff_semidirect (hA : IsPGroup 2 A) :
    (pStarCore 2 (fixedPointSubgroup A G)).map (fixedPointSubgroup A G).subtype ≤
        pStarCore 2 G ↔
      (pStarCore 2 CSD).map (CSD).subtype ≤ pStarCore 2 SD := by
  rw [← map_twoStarCore_fixedPoint_semidirect hA, ← map_twoStarCore_semidirect_inl hA,
    map_le_map_iff_of_injective SemidirectProduct.inl_injective]

end Finite
end Theory.GroupTheory.PStarAction
