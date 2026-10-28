module
public import Theory.Representation.BinaryPermutation.FourBlockThompson
public import Theory.SpecificGroups.SymmetricEight.FourBlockSylowResidual
public import Theory.GroupTheory.PResidual.Quotient
public import Theory.GroupTheory.PCoreImage
public import Theory.GroupTheory.PGroup.NormalChain
public import Theory.GroupTheory.PGroup.SubnormalCore

/-!
# The literal weight-four centralizer and its block residual

The full seven-dimensional core word supported on the first four letters
has a stabilizer between A₄ × A₄ and the unordered four-block stabilizer.
Every such intermediate group has two-residual A₄ × A₄: the latter is
two-perfect and has two-power index. The intermediate group is subnormal
in the full block stabilizer, so its two-core is the same V₄ × V₄.

The word, action, embedded residual and embedded core remain literal.
The original Section 12.6 application uses these to identify O²(C_L(v₄))
and the full preimage of its two-core under the original LT action.

Source: Aschbacher--Smith, combined manuscript of 1 March 2004,
12.6.1(4) and the proof of 12.6.19, printed pp.823 and 828.
-/

public section
open Subgroup
namespace BinaryPermutation.TerminalOrthogonal.FourBlockPoint
open FourBlockResidual

/-- A subgroup between the two alternating block factors and the full block
stabilizer has exactly those factors as its embedded two-residual. -/
theorem intermediate_residual (J : Subgroup S8) (hRJ : R ≤ J) (hJH : J ≤ H) :
    (pResidual 2 J).map J.subtype = R := by
  have hperf : pResidual 2 R = ⊤ := by
    have hh := map_pResidual 2 productEquiv
    rw [product_pResidual, map_top_of_surjective _ productEquiv.surjective] at hh
    exact hh.symm
  have hrJ : pResidual 2 (R.subgroupOf J) = ⊤ := by
    have hh := map_pResidual 2 (subgroupOfEquivOfLe hRJ).symm
    rw [hperf,map_top_of_surjective _ (subgroupOfEquivOfLe hRJ).symm.surjective] at hh
    exact hh.symm
  have hi : R.relIndex H = 8 := by
    have hc := (R.subgroupOf H).card_mul_index
    rw [Nat.card_congr (subgroupOfEquivOfLe R_le_H).toEquiv,
      R_card,Theory.SpecificGroups.SymmetricEight.FourBlockSylowResidual.fourStabilizer_card] at hc
    change 144 * R.relIndex H = 1152 at hc
    omega
  let : (R.subgroupOf J).Normal :=
    normal_subgroupOf_of_le_normalizer (hJH.trans H_normalizes_R)
  have hp : IsPGroup 2 (J ⧸ R.subgroupOf J) := by
    apply (isPGroup_iff_card_dvd_pow).mpr
    refine ⟨3,?_⟩
    rw [←index_eq_card]
    have hd := relIndex_dvd_index_of_le (show R.subgroupOf H ≤ J.subgroupOf H from comap_mono hRJ)
    rw [relIndex_subgroupOf hJH] at hd
    change R.relIndex J ∣ R.relIndex H at hd
    rw [hi] at hd
    exact hd
  apply le_antisymm
  · have hh := map_mono (f := J.subtype)
      ((pResidual_le_iff_isPGroup_quotient 2 (R.subgroupOf J)).mpr hp)
    rwa [map_subgroupOf_eq_of_le hRJ] at hh
  · have hh := map_mono (f := J.subtype)
      (show R.subgroupOf J ≤ pResidual 2 J from by
        have hm := map_pResidual_le 2 (R.subgroupOf J).subtype
        rwa [hrJ,←MonoidHom.range_eq_map,range_subtype] at hm)
    rwa [map_subgroupOf_eq_of_le hRJ] at hh

/-- Every intermediate block group has the same literal two-core. -/
theorem intermediate_core (J : Subgroup S8) (hRJ : R ≤ J) (hJH : J ≤ H) :
    J.pCoreIn 2 = Theory.SpecificGroups.SymmetricEight.FourBlockCoreAction.kleinGroup := by
  have hr : pResidual 2 H ≤ J.subgroupOf H := by
    intro x hx
    exact hRJ ((intermediate_residual H R_le_H le_rfl).le (mem_map_of_mem H.subtype hx))
  let q := QuotientGroup.mk' (pResidual 2 H)
  have hn : (J.subgroupOf H).IsSubnormal := by
    have hh := ((isPGroup_quotient_pResidual 2 (G := H)).subgroup_isSubnormal
      ((J.subgroupOf H).map q)).comap q
    rwa [comap_map_eq_self (by simpa only [q,QuotientGroup.ker_mk'] using hr)] at hh
  have hcore := Theory.SpecificGroups.SymmetricEight.FourBlockCoreAction.fourStabilizer_pCoreIn
  apply le_antisymm
  · exact (pCoreAmbient_mono_of_isSubnormalIn J H 2 hJH hn).trans_eq hcore
  · rw [←hcore]
    exact le_pCoreIn_of_normalizes (isPGroup_pCoreIn 2 H)
      (hcore ▸ (kleinGroup_le_R.trans hRJ))
      (hJH.trans (H.le_normalizer.trans
        (normalizer_le_normalizer_characteristic_image H (pCore 2 H))))

/-- The two-core of the literal alternating block product is the block Klein group. -/
theorem residual_core : R.pCoreIn 2 = Theory.SpecificGroups.SymmetricEight.FourBlockCoreAction.kleinGroup :=
  intermediate_core R le_rfl R_le_H

/-- The specified weight-four representative in the full seven-dimensional core. -/
@[expose] def point : core (Fin 8) :=
  ⟨fun i => if i.val < 4 then 1 else 0, by rw [mem_core]; decide⟩

/-- Its actual permutation stabilizer, retaining the full core action. -/
@[expose] def stabilizer : Subgroup S8 where
  carrier := {g | coreRepresentation (Fin 8) g point = point}
  one_mem' := by simp
  mul_mem' := by
    intro a b ha hb
    change coreRepresentation (Fin 8) a point = point at ha
    change coreRepresentation (Fin 8) b point = point at hb
    change coreRepresentation (Fin 8) (a*b) point = point
    rw [map_mul,Module.End.mul_apply,hb,ha]
  inv_mem' := by
    intro a ha
    have hh := congrArg (coreRepresentation (Fin 8) a⁻¹) ha
    rw [←Module.End.mul_apply,←map_mul,inv_mul_cancel,map_one,Module.End.one_apply] at hh
    exact hh.symm

private theorem point_eq_iff (i j : Fin 8) :
    point.val i = point.val j ↔ i.val / 4 = j.val / 4 := by
  revert i j
  decide

theorem stabilizer_le : stabilizer ≤ H := by
  intro g hg i j
  have he (k : Fin 8) : point.val (g k) = point.val k := by
    have hh := congrArg (fun v : core (Fin 8) => v.val (g k)) hg
    change point.val (g⁻¹ (g k)) = point.val (g k) at hh
    simpa using hh.symm
  rw [←point_eq_iff,←point_eq_iff,he,he]

theorem residual_le_stabilizer : R ≤ stabilizer := by
  intro g hg
  rw [←blockHom_range] at hg
  obtain ⟨a,rfl⟩ := hg
  apply Subtype.ext
  apply funext
  intro i
  obtain ⟨i,rfl⟩ := (@finSumFinEquiv 4 4).surjective i
  change point.val ((blockHom a)⁻¹ (finSumFinEquiv i)) = point.val (finSumFinEquiv i)
  rw [←map_inv]
  rcases i with i | i
  · simp only [blockHom, Theory.SpecificGroups.SymmetricEight.FourBlockResidual.blockAlternatingHom,
      MonoidHom.comp_apply, Subgroup.coe_subtype, MonoidHom.coe_mk, OneHom.coe_mk,
      Equiv.permCongr_apply, Equiv.symm_apply_apply, Equiv.sumCongr_apply, Sum.map_inl]
    change (if (a.1.val⁻¹ i).val < 4 then (1 : ZMod 2) else 0) =
      (if i.val < 4 then 1 else 0)
    simp
  · simp only [blockHom, Theory.SpecificGroups.SymmetricEight.FourBlockResidual.blockAlternatingHom,
      MonoidHom.comp_apply, Subgroup.coe_subtype, MonoidHom.coe_mk, OneHom.coe_mk,
      Equiv.permCongr_apply, Equiv.symm_apply_apply, Equiv.sumCongr_apply, Sum.map_inr]
    change (if 4 + (a.2.val⁻¹ i).val < 4 then (1 : ZMod 2) else 0) =
      (if 4 + i.val < 4 then 1 else 0)
    simp

theorem even_stabilizer_residual :
    (pResidual 2 (alternatingGroup (Fin 8) ⊓ stabilizer : Subgroup S8)).map
      (alternatingGroup (Fin 8) ⊓ stabilizer).subtype = R :=
  intermediate_residual _ (le_inf (R_le_P.trans inf_le_left) residual_le_stabilizer)
    (inf_le_right.trans stabilizer_le)

end BinaryPermutation.TerminalOrthogonal.FourBlockPoint
