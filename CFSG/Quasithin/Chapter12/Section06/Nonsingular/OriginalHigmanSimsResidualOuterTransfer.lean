module

public import Theory.GroupTheory.NormalCentralQuotientAction
public import Theory.GroupTheory.SolvableOuterQuotient
public import Theory.GroupTheory.PCoreSurjective.OddExtension

/-!
# Transporting the actual residual outer action through quotient images

The quotient-to-image equivalence intertwines the original conjugation
actions whenever the restricted kernel is the entire intrinsic two-core.
Consequently innerness on that quotient is equivalent to innerness on the
actual image, with no ambient surjectivity needed. A surjection with a
two-group kernel also preserves innerness on both intrinsic core quotients.

The maps, normal residual, full cores and acting element remain explicit.
These bridges transport the native HS outer witness to the actual star
image without assuming faithfulness or replacing the covering kernel.

Source: the full residual action comparison in the original HS inspection
of Aschbacher--Smith 12.6.12, printed pp.825--826.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section06.OriginalHigmanSimsResidualOuterTransfer

private theorem congr_inner_iff {A B : Type*} [Group A] [Group B]
    (e : A ≃* B) (a : MulAut A) :
    MulAut.congr e a ∈ MulAut.innerSubgroup B ↔ a ∈ MulAut.innerSubgroup A := by
  simpa only [MulAut.innerSubgroup,MonoidHom.mem_range,eq_comm] using
    MulAut.congr_inner_iff e a

/-- The actual image action is inner exactly when the original action on
the full intrinsic two-core quotient is inner. -/
theorem image_action_inner_iff
    {A B : Type*} [Group A] [Group B]
    (f : A →* B) (R : Subgroup A) [R.Normal]
    (hk : (f.comp R.subtype).ker = pCore 2 R) (x : A) :
    let fx : normalizer (R.map f : Set B) := ⟨f x,by
      apply R.le_normalizer_map f
      exact mem_map_of_mem f (by rw [normalizer_eq_top]; exact mem_top x)⟩
    (R.map f).normalizerMonoidHom fx ∈ MulAut.innerSubgroup (R.map f) ↔
      normalQuotientAction R (pCore 2 R) x ∈ MulAut.innerSubgroup (R ⧸ pCore 2 R) := by
  let g := f.comp R.subtype
  have hr : g.range = R.map f := by rw [MonoidHom.range_comp,range_subtype]
  let e : (R ⧸ pCore 2 R) ≃* R.map f :=
    (QuotientGroup.quotientMulEquivOfEq hk.symm).trans
      ((QuotientGroup.quotientKerEquivRange g).trans (MulEquiv.subgroupCongr hr))
  have he (r : R) : e (QuotientGroup.mk' (pCore 2 R) r) = f.subgroupMap R r := by
    apply Subtype.ext
    rfl
  let fx : normalizer (R.map f : Set B) := ⟨f x,by
    apply R.le_normalizer_map f
    exact mem_map_of_mem f (by rw [normalizer_eq_top]; exact mem_top x)⟩
  have hact : MulAut.congr e (normalQuotientAction R (pCore 2 R) x) =
      (R.map f).normalizerMonoidHom fx := by
    apply MulEquiv.ext
    intro y
    obtain ⟨r,rfl⟩ := f.subgroupMap_surjective R y
    change e (normalQuotientAction R (pCore 2 R) x
      (e.symm (f.subgroupMap R r))) = _
    rw [←he r,e.symm_apply_apply,normalQuotientAction_apply_mk,he]
    apply Subtype.ext
    change f (x * (r:A) * x⁻¹) = f x * f (r:A) * (f x)⁻¹
    simp only [map_mul,map_inv]
  change (R.map f).normalizerMonoidHom fx ∈ MulAut.innerSubgroup (R.map f) ↔ _
  rw [←hact]
  exact congr_inner_iff e _

/-- A surjection with two-group kernel preserves innerness of the original
residual action after taking both full intrinsic two-core quotients. -/
theorem quotient_action_inner_iff_of_two_kernel
    {A B : Type*} [Group A] [Finite A] [Group B] [Finite B]
    (q : A →* B) (hq : Function.Surjective q) (hk : IsPGroup 2 q.ker)
    (R : Subgroup A) [R.Normal] (x : A) :
    letI : (R.map q).Normal := (inferInstance : R.Normal).map q hq
    normalQuotientAction (R.map q) (pCore 2 (R.map q)) (q x) ∈
        MulAut.innerSubgroup ((R.map q) ⧸ pCore 2 (R.map q)) ↔
      normalQuotientAction R (pCore 2 R) x ∈ MulAut.innerSubgroup (R ⧸ pCore 2 R) := by
  let : (R.map q).Normal := (inferInstance : R.Normal).map q hq
  have hkR : IsPGroup 2 (q.subgroupMap R).ker := by
    rw [ker_subgroupMap]
    exact hk.comap_subtype
  let e := (q.subgroupMap R).quotientPCoreEquivOfSurjective
    (q.subgroupMap_surjective R) hkR
  have he (r : R) : e (QuotientGroup.mk' (pCore 2 R) r) =
      QuotientGroup.mk' (pCore 2 (R.map q)) (q.subgroupMap R r) :=
    MonoidHom.quotientPCoreEquivOfSurjective_mk _ _ _ r
  have hact : MulAut.congr e (normalQuotientAction R (pCore 2 R) x) =
      normalQuotientAction (R.map q) (pCore 2 (R.map q)) (q x) := by
    apply MulEquiv.ext
    intro y
    obtain ⟨b,rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 (R.map q)) y
    obtain ⟨r,rfl⟩ := q.subgroupMap_surjective R b
    change e (normalQuotientAction R (pCore 2 R) x
      (e.symm (QuotientGroup.mk' (pCore 2 (R.map q)) (q.subgroupMap R r)))) = _
    rw [←he r,e.symm_apply_apply,normalQuotientAction_apply_mk,he,he r,
      normalQuotientAction_apply_mk]
    apply congrArg (QuotientGroup.mk' (pCore 2 (R.map q)))
    apply Subtype.ext
    change q (x * (r:A) * x⁻¹) = q x * q (r:A) * (q x)⁻¹
    simp only [map_mul,map_inv]
  rw [←hact]
  exact congr_inner_iff e _

end CFSG.Quasithin.Chapter12.Section06.OriginalHigmanSimsResidualOuterTransfer
