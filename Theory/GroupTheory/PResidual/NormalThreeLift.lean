module
public import Theory.GroupTheory.PResidual.NormalizedImageLift
public import Theory.GroupTheory.PCoreActionSplitting

/-!
# Exact normal three-subgroup lifts through a two-kernel

For a surjection with two-group kernel, take the two-residual of the full
preimage of a normal three-subgroup. The resulting subgroup is normal and
two-perfect and maps onto the prescribed three-subgroup. Its restricted
quotient map has exactly its intrinsic two-core as kernel, giving the
actual quotient isomorphism.

Source application: the supercritical three-core reduction in
Aschbacher–Smith 14.7.27, printed pp.1054–1055, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup
namespace Subgroup

/-- Lift a normal three-subgroup with its exact image and intrinsic two-core kernel. -/
theorem exists_normal_three_residual_lift {D E : Type*} [Group D] [Finite D]
    [Group E] [Finite E] (q : D →* E) (hq : Function.Surjective q)
    (hk : IsPGroup 2 q.ker) (X : Subgroup E) [X.Normal] (hX : IsPGroup 3 X) :
    ∃ Y : Subgroup D, Y.Normal ∧ IsPPerfect 2 Y ∧ Y ≤ pResidual 2 D ∧
      Y.map q = X ∧ (q.comp Y.subtype).ker = pCore 2 Y ∧
      Nonempty ((Y ⧸ pCore 2 Y) ≃* X) := by
  let I := X.comap q
  let Y := (pResidual 2 I).map I.subtype
  have hp : IsPPerfect 2 X := by
    apply (pResidual_eq_top_iff 2 X).mp
    apply top_unique
    intro x _
    obtain ⟨n,hn⟩ := hX.exists_card_eq
    exact mem_pResidual_of_orderOf_coprime
      (((by decide : Nat.Coprime 2 3).pow_right n).of_dvd_right
        (hn ▸ _root_.orderOf_dvd_natCard x))
  have him : Y.map q = X := by
    rw [map_embedded_pResidual,show I.map q = X from map_comap_eq_self_of_surjective hq X,
      (pResidual_eq_top_iff 2 X).mpr hp,←MonoidHom.range_eq_map,range_subtype]
  let f := q.comp Y.subtype
  have hf : IsPGroup 2 f.ker := hk.comap_of_injective _ Y.subtype_injective
  have hr : f.range = X := by rw [MonoidHom.range_comp,range_subtype,him]
  have h3 : IsPGroup 3 f.range := hr.symm ▸ hX
  have hcore : pCore 2 f.range = ⊥ := by
    exact le_bot_iff.mp ((le_inf le_rfl le_top).trans
      (pCore_isPGroup.disjoint_of_coprime (h3.to_subgroup ⊤)
        (by decide : Nat.Coprime 2 3)).le_bot)
  have he := f.ker_eq_pCore_of_range_core_eq_bot 2 hf hcore
  refine ⟨Y,inferInstance,isPPerfect_embedded_pResidual 2 I,
    map_pResidual_le 2 I.subtype,him,he,?_⟩
  exact ⟨(QuotientGroup.quotientMulEquivOfEq he.symm).trans
    ((QuotientGroup.quotientKerEquivRange f).trans (MulEquiv.subgroupCongr hr))⟩

end Subgroup
