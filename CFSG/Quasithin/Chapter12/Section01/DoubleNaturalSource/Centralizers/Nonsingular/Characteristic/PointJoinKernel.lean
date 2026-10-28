module
public import CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.Centralizers.Nonsingular.PointAction

/-!
# The exact kernel on the original point-residual join

The action kernel meets the point residual in its two-core. Its remaining
quotient embeds in the two-group quotient supplied by the relative point
Sylow. Thus the full kernel is a two-group. The two-core-free H.9 point
stabilizer identifies it with the intrinsic two-core of the join.

This uses only the Sylow in the local point centralizer. JankoAction uses
the equality to descend the full point action through the central-cover
action on an ordinary component.
Source: Aschbacher--Smith 12.1.1 and H.9.1(4), printed pp.788 and390.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter12.Section01.DoubleNaturalSource
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- The literal point-residual join acts with exactly its intrinsic two-core as kernel. -/
theorem doubleNatural_adapted_pointJoin_action_kernel
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    {n : ℕ} (B : DoubledBranch T L V n) :
    letI := D.doubledOrbit_elementary h
    ∀ (S : B.SourceModel) w, B.AdaptedPoint S w →
      let J := B.pointResidual w ⊔ B.pointSylow w
      ∀ hJM : J ≤ B.localPointCentralizer w,
        ((S.localPointAction w).comp (inclusion hJM)).ker = pCore 2 J := by
  let := D.doubledOrbit_elementary h
  intro S w hw J hJM
  let R := B.pointResidual w
  let A := R.subgroupOf J
  let P := (B.pointSylow w).subgroupOf J
  let f := (S.localPointAction w).comp (inclusion hJM)
  have hPN : B.pointSylow w ≤ normalizer (R : Set G) :=
    (le_inf (inf_le_left.trans D.sylow_normalizes_component) inf_le_right).trans
      (B.localPointCentralizer_normalizes_residual w)
  let : A.Normal := normal_subgroupOf_of_le_normalizer (sup_le R.le_normalizer hPN)
  have hgen : A ⊔ P = ⊤ := by
    apply map_injective J.subtype_injective
    rw [Subgroup.map_sup,map_subgroupOf_eq_of_le le_sup_left,
      map_subgroupOf_eq_of_le le_sup_right,←MonoidHom.range_eq_map,range_subtype]
  have hquot : IsPGroup 2 (J ⧸ A) := isPGroup_quotient_of_sup_eq_top A P
    ((T.isPGroup'.to_le inf_le_left).comap_subtype) hgen
  let q := (QuotientGroup.mk' A).comp f.ker.subtype
  have hkq : IsPGroup 2 q.ker := by
    let r : q.ker →* R :=
      (J.subtype.comp (f.ker.subtype.comp q.ker.subtype)).codRestrict R (by
        intro x
        exact (QuotientGroup.eq_one_iff (N := A) x.val.val).mp x.property)
    have hr (x : q.ker) : r x ∈ pCore 2 R := by
      rw [←(S.nonsingular_residual_kernel_and_quotient w hw.nonsingular).1]
      exact congrArg Subtype.val x.val.property
    let r' := r.codRestrict (pCore 2 R) hr
    apply pCore_isPGroup.of_injective r'
    intro x y hxy
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : pCore 2 R => (z.val : G)) hxy
  have hk : IsPGroup 2 f.ker := by
    have hh := (hquot.to_subgroup ⊤).comap_of_ker_isPGroup q hkq
    rw [comap_top] at hh
    exact hh.of_equiv topEquiv
  have hf : Function.Surjective f := S.adapted_pointJoin_action_surjective w hw
    (le_inf (inf_le_left.trans D.sylow_normalizes_component) inf_le_right)
  change f.ker = pCore 2 J
  have hkle : f.ker ≤ pCore 2 J := le_sSup ⟨inferInstance,hk⟩
  apply le_antisymm hkle
  have hi : (pCore 2 J).map f ≤ pCore 2 (S.setup.stabilizer (Additive.ofMul w)) :=
    le_sSup ⟨(inferInstance : (pCore 2 J).Normal).map f hf,pCore_isPGroup.map f⟩
  rw [S.nonsingular_stabilizer_twoCore w hw.nonsingular] at hi
  exact (Subgroup.map_eq_bot_iff _).mp (bot_unique hi)
end CFSG.Quasithin.Chapter12.Section02.ChosenModule
