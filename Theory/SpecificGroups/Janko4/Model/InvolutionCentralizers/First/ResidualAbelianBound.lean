module
public import Theory.SpecificGroups.Janko4.Model.InvolutionCentralizers.First.LargeAbelianImage

/-!
# Abelian two-subgroups controlled by the first J₄ centralizer residual

The full perfect residual is the preimage of the native triple M₂₂ cover:
it contains the entire extraspecial two-core and maps onto that cover.
Intersect an abelian two-subgroup normalized by this residual with the
residual. Its normality places it in the extraspecial core, where its
order is at most 128. The residual has index two, giving the bound 256
for the original subgroup. Neither containment in the residual nor
normality in the whole centralizer is assumed.

Source: Aschbacher–Smith, 4.4.3, printed p.623; GLS3 Table 5.3i.
The literal centralizer and quotient certificates retain their ATLAS
attribution through the imported first-centralizer modules.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace Janko4.InvolutionCentralizers.First
open QuotientExtension
attribute [local irreducible] Janko4.modelGroup Janko4.matrixA Janko4.matrixB

/-- The perfect residual is exactly the full native triple-cover preimage. -/
theorem residual_eq_coverPreimage : solvableResidual centralizer = H := by
  apply le_antisymm
  · let : Group.IsSolvable (centralizer ⧸ H) :=
      Group.isSolvable_of_isSolvable_injective
        (f := centralizerQuotientEquivC2.toMonoidHom) centralizerQuotientEquivC2.injective
    exact solvableResidual_le_of_solvable_quotient H
  · intro x hx
    have hmap := map_solvableResidual_eq coverProjection coverProjection_surjective
    rw [solvableResidual_eq_top (G := Sporadic.Mathieu.M22TripleCover)] at hmap
    obtain ⟨r,hr,he⟩ := hmap.symm ▸ mem_top (coverProjection ⟨x,hx⟩)
    have hker : (⟨x,hx⟩ : H) * r⁻¹ ∈ coverProjection.ker := by
      change coverProjection _ = 1
      rw [map_mul,map_inv,he,mul_inv_cancel]
    rw [coverProjection_ker] at hker
    have hc : x * (r : centralizer)⁻¹ ∈ solvableResidual centralizer :=
      twoCore_le_residual hker
    have hr' : (r : centralizer) ∈ solvableResidual centralizer :=
      map_solvableResidual_le H.subtype (mem_map_of_mem H.subtype hr)
    simpa only [inv_mul_cancel_right] using (solvableResidual centralizer).mul_mem hc hr'

/-- Residual normalization bounds every abelian two-subgroup by 256. -/
theorem residual_normalized_abelian_card_le
    (E : Subgroup centralizer) [IsMulCommutative E] (hp : IsPGroup 2 E)
    (hn : solvableResidual centralizer ≤ normalizer (E : Set centralizer)) :
    Nat.card E ≤ 256 := by
  rw [residual_eq_coverPreimage] at hn
  let U := E.subgroupOf H
  let : U.Normal := normal_subgroupOf_of_le_normalizer hn
  have hUcore : U ≤ pCore 2 H := le_sSup ⟨inferInstance,hp.comap_subtype⟩
  have hUQ : U ≤ Q.subgroupOf H := by
    rw [pCore_eq_comap_of_normal] at hUcore
    exact hUcore
  let UQ := U.map H.subtype
  have hUQQ : UQ ≤ Q := by
    rintro _ ⟨u,hu,rfl⟩
    exact hUQ hu
  let W := UQ.subgroupOf Q
  have hUQE : UQ ≤ E := map_comap_le H.subtype E
  let : IsMulCommutative W := ⟨⟨fun x y => Subtype.ext (Subtype.ext
    (setLike_mul_comm (hUQE x.property) (hUQE y.property)))⟩⟩
  let := centralizer_twoCore_extraspecial
  have hW := extraspecial_prime_abelian_card_sq_le_any (p := 2) W
  have hWU : Nat.card W = Nat.card U := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hUQQ).toEquiv]
    exact card_map_of_injective H.subtype_injective
  rw [hWU,centralizer_twoCore_card] at hW
  have hU128 : Nat.card U ≤ 128 := by nlinarith
  let r := (QuotientGroup.mk' H).comp E.subtype
  have hker : Nat.card r.ker = Nat.card U := by
    let er : r.ker ≃* U :=
      { toFun := fun x => ⟨⟨x.val.val,(QuotientGroup.eq_one_iff _).mp x.property⟩,x.val.property⟩
        invFun := fun x => ⟨⟨x.val.val,x.property⟩,(QuotientGroup.eq_one_iff _).mpr x.val.property⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl
        map_mul' := fun _ _ => rfl }
    exact Nat.card_congr er.toEquiv
  have hrange : Nat.card r.range ≤ 2 := by
    have hh := r.range.card_le_card_group
    have hh' : Nat.card (centralizer ⧸ H) = 2 := by
      rw [Nat.card_congr centralizerQuotientEquivC2.toEquiv]
      simp
    exact hh.trans_eq hh'
  have hcount : Nat.card E = Nat.card r.ker * Nat.card r.range := by
    rw [←index_ker]
    exact r.ker.card_mul_index.symm
  rw [hker] at hcount
  nlinarith
end Janko4.InvolutionCentralizers.First
