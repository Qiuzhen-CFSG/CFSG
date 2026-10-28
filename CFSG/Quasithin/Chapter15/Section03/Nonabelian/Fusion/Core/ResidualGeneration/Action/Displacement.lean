module

public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Core.ResidualGeneration.Action.Actors
public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Core.ResidualGeneration.Inputs
public import Theory.Representation.PSL3Two.SingerDisplacement
public import Theory.GroupTheory.PGroup.RankTwoExtraspecialThirtyTwo

/-!
# Singer displacement in the literal U/Z

A Singer element displaces the entire natural and contragredient modules.
The equivariant coordinates of 15.3.58 transport this to a surjective
commutator map on the actual U/Z. Lifting that Singer actor to O²(H) puts
all these commutators in U ∩ O²(H). Since Z is the Frattini subgroup of
extraspecial U, generation modulo Z gives U ≤ O²(H).

Source: Aschbacher–Smith, combined manuscript (1 March 2004),
15.3.55, 15.3.58(2–3), and the proof of 15.3.59, printed pp.1147–1150.
-/

public section

namespace CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Core.ResidualGeneration
open Subgroup
open CFSG.Quasithin.Chapter15.Section03.Nonabelian
open Matrix.PSL3Two.OuterInvolutionSinger
open Representation.BinaryOffender
open scoped commutatorElement

variable {G : Type*} [Group G] {T Z ZS V : Subgroup G} {t : G}
variable [(Z.subgroupOf (closureU Z ZS)).Normal]

/-- The ambient commutator, retained as an element of the H-invariant U. -/
@[expose] def closureCommutator (h : centralizerH Z) (u : closureU Z ZS) : closureU Z ZS :=
  ⟨⁅(h : G), (u : G)⁆,
    (le_normalizer_iff_commutator_le_right.mp (H_normalizes_closureU Z ZS))
      (commutator_mem_commutator h.property u.property)⟩

/-- Quotient projection turns the actual commutator into action displacement. -/
theorem quotient_closureCommutator (h : centralizerH Z) (u : closureU Z ZS) :
    QuotientGroup.mk' (Z.subgroupOf (closureU Z ZS)) (closureCommutator h u) =
      quotientAction Z ZS h (QuotientGroup.mk' _ u) * (QuotientGroup.mk' _ u)⁻¹ := by
  rw [quotientAction_mk, ← map_inv, ← map_mul]
  rfl

private theorem singer_displacement_natural :
    Function.Surjective (BinaryLinearThree.W singer - LinearMap.id :
      Module.End (ZMod 2) BinaryLinearThree.Vector) := by
  apply LinearMap.range_eq_top.mp
  apply Submodule.eq_top_of_finrank_eq
  rw [← fixedCodim_zpowers_eq_displacement_rank,
    BinaryLinearThree.SingerDisplacement.fixedCodim_singer_natural]
  simp [BinaryLinearThree.Vector, Matrix.PSL3Two.Fano.Vector]

private theorem singer_displacement_dual :
    Function.Surjective (BinaryLinearThree.W.dual singer - LinearMap.id :
      Module.End (ZMod 2) (Module.Dual (ZMod 2) BinaryLinearThree.Vector)) := by
  apply LinearMap.range_eq_top.mp
  apply Submodule.eq_top_of_finrank_eq
  rw [← fixedCodim_zpowers_eq_displacement_rank,
    BinaryLinearThree.SingerDisplacement.fixedCodim_singer_dual]
  simp [BinaryLinearThree.Vector, Matrix.PSL3Two.Fano.Vector]

/-- The specified Singer actor displaces every element of the actual U/Z. -/
theorem quotient_singer_displacement_surjective
    (d : RecognizedAction T Z ZS V t) (h : centralizerH Z)
    (hh : d.actorEquiv (actorProjection Z h) = MulAut.conj singer) :
    Function.Surjective (fun w : VectorQuotient Z ZS => quotientAction Z ZS h w * w⁻¹) := by
  intro w
  obtain ⟨v, hv⟩ := singer_displacement_natural (d.coordinates w).toAdd.1
  obtain ⟨f, hf⟩ := singer_displacement_dual (d.coordinates w).toAdd.2
  refine ⟨d.coordinates.symm (Multiplicative.ofAdd (v, f)), d.coordinates.injective ?_⟩
  rw [map_mul, map_inv]
  apply Multiplicative.toAdd.injective
  simp only [toAdd_mul, toAdd_inv, ← sub_eq_add_neg]
  rw [d.equivariant h singer hh, d.coordinates.apply_symm_apply]
  exact Prod.ext hv hf

variable [Finite G]

/-- The extraspecial subgroup U lies in the actual two-residual of H. -/
theorem closure_le_residual (d : RecognizedAction T Z ZS V t)
    [IsExtraspecial 2 (closureU Z ZS)]
    (hUH : closureU Z ZS ≤ centralizerH Z)
    (hcenter : (center (closureU Z ZS)).map (closureU Z ZS).subtype = Z) :
    closureU Z ZS ≤ residualK Z := by
  let U := closureU Z ZS
  let N := (residualK Z).subgroupOf U
  let q := QuotientGroup.mk' (Z.subgroupOf U)
  obtain ⟨k, hk⟩ := exists_residual_lift_inner Z d.actorEquiv singer
  let h := inclusion (residual_le_H Z) k
  have hsurj := quotient_singer_displacement_surjective d h hk
  have hnorm : centralizerH Z ≤ normalizer (residualK Z : Set G) :=
    (normal_subgroupOf_iff_le_normalizer (residual_le_H Z)).mp (residual_normal_in_H Z)
  have hmap : N.map q = ⊤ := by
    apply eq_top_iff.mpr
    intro w _
    obtain ⟨w₀, hw₀⟩ := hsurj w
    obtain ⟨u, rfl⟩ := QuotientGroup.mk'_surjective (Z.subgroupOf U) w₀
    refine ⟨closureCommutator h u, ?_, ?_⟩
    · exact (le_normalizer_iff_commutator_le_left.mp (hUH.trans hnorm))
        (commutator_mem_commutator k.property u.property)
    · exact (quotient_closureCommutator h u).trans hw₀
  have hZ : Z ≤ U := hcenter.symm.le.trans (map_subtype_le _)
  have hz : Z.subgroupOf U ≤ frattini U := by
    rw [IsExtraspecial.frattini_eq_center_two]
    apply (map_le_map_iff_of_injective U.subtype_injective).mp
    rw [map_subgroupOf_eq_of_le hZ, hcenter]
  have hsup : N ⊔ frattini U = ⊤ := by
    have hh := congrArg (comap q) hmap
    rw [comap_map_eq, comap_top, QuotientGroup.ker_mk'] at hh
    exact top_unique (hh.symm.le.trans (sup_le_sup_left hz N))
  have hN : N = ⊤ := frattini_nongenerating hsup
  intro u hu
  have hn : (⟨u, hu⟩ : U) ∈ N := hN.symm ▸ mem_top _
  exact hn

end CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Core.ResidualGeneration
