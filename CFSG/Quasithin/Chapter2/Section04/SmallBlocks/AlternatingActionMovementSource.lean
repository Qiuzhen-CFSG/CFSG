module
public import CFSG.Quasithin.Chapter2.Section04.SmallBlocks.AlternatingRelativeIndicesSource
public import Theory.GroupTheory.ConjugateJoinImageMovement
/-!
# The original conjugator moves the square-action image

The C.5.6 factorization writes the selected Thompson subgroup as the join
of the natural module, its actual source conjugate, and the block centralizer.
The two relative indices imply that any action with the intrinsic Sylow kernel
has noncommuting images inside the original Sylow subgroup T. This preserves
the common two-subgroup required for the order-72 orthogonal action argument.

Source: Aschbacher--Smith 2.4.29, printed p.545.
-/
public section
open Subgroup Stellmacher
namespace CFSG.Quasithin.Chapter2
open ChapterC ChapterC.Section05.ConjugateSource
variable {G W : Type*} [Group G] [Finite G] [Group W] {M : Subgroup G}

theorem MinimalBlockSetup.single_alternating_action_movement
    (d : MinimalBlockSetup M) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hM : IsMaximalTwoLocal M) (hTM : (T : Subgroup G) ≤ M)
    (hu : ∀ N : Subgroup G, IsMaximalTwoLocal N → (T : Subgroup G) ≤ N → N = M)
    (hST : (d.S : Subgroup d.H).map d.H.subtype < (T : Subgroup G))
    (hsingle : d.L0 = d.block)
    (hA : IsAlternatingBlock (d.block.map d.H.subtype) 5)
    (f : T →* W)
    (hker : (f.comp (inclusion hST.le)).ker =
      (( ( (pResidual 2 (M ⊓ d.block.map d.H.subtype : Subgroup G)).map
          (M ⊓ d.block.map d.H.subtype).subtype).pCoreIn 2) ⊔
        ((T : Subgroup G) ⊓ centralizer (d.block.map d.H.subtype : Set G))).subgroupOf
          ((d.S : Subgroup d.H).map d.H.subtype)) :
    ∃ x u : T, f x * f u ≠ f u * f x := by
  let R := (d.S : Subgroup d.H).map d.H.subtype
  let U := sourceModule (d.block.map d.H.subtype)
  let D := (T : Subgroup G) ⊓ centralizer (d.block.map d.H.subtype : Set G)
  let P := ((pResidual 2 (M ⊓ d.block.map d.H.subtype : Subgroup G)).map
    (M ⊓ d.block.map d.H.subtype).subtype).pCoreIn 2
  let E := P ⊔ D
  let J := elementaryAbelianMaxJ R
  have hi := (d.single_alternating_sylow_index_source hG T hM hTM hu hST hsingle hA).1
  obtain ⟨c,h,x,hx,hnc⟩ := d.single_alternating_configuration hG T hST.le hsingle hA
    (T : Subgroup G) hST.le le_rfl hi
  have hRK := c.R_le_H.trans c.normalizes_residual
  have hH : d.H = d.block.map d.H.subtype ⊔ R := c.residual_sup_sylow.symm
  have hno (A : Subgroup G) (hAR : A ≤ R) (hHA : d.H ≤ normalizer (A : Set G))
      (hTA : (T : Subgroup G) ≤ normalizer (A : Set G)) : A = ⊥ :=
    c.no_common_normal A hAR ((normal_subgroupOf_iff_le_normalizer
      (hAR.trans (c.R_le_M.trans le_sup_left))).mpr (sup_le hTA hHA))
  have hfull := ChapterC.Section06.original_core_eq_module_centralizer c h.block.2.1
  have hp := h.source_C56_single_block_7 hRK d.H (T : Subgroup G) R c.T_le c.R_normal hRK hH hno
    (hfull.trans (congrArg (fun A : Subgroup G => A.pCoreIn 2) hH)) x hx hi hnc
  have hfamily : J=(U⊔U.map (MulAut.conj x⁻¹).toMonoidHom)⊔D := by
    have hh := hp.2.2.2.2.2.2.1
    rw [hp.2.2.2.1,hp.2.2.2.2.2.2.2.1,
      ←d.single_block_sylow_centralizer T hST.le hsingle] at hh
    exact hh
  have hUR : U ≤ R := h.module_le.trans inf_le_left
  have hDR : D ≤ R := by
    rw [show D=R⊓centralizer (d.block.map d.H.subtype : Set G) from
      d.single_block_sylow_centralizer T hST.le hsingle]
    exact inf_le_left
  have hJR : J ≤ R := sSup_le fun A hA=>hA.1
  obtain ⟨hiU,hiJ⟩ := d.single_alternating_core_relative_indices hG T hM hTM hu hST hsingle hA
  have hrestrict (A : Subgroup G) (hAR : A ≤ R) :
      (A.subgroupOf R).map (inclusion hST.le) = A.subgroupOf (T : Subgroup G) := by
    apply map_injective (f:=(T : Subgroup G).subtype) (T : Subgroup G).subtype_injective
    rw [map_map,map_subgroupOf_eq_of_le (hAR.trans hST.le)]
    change (A.subgroupOf R).map R.subtype=A
    exact map_subgroupOf_eq_of_le hAR
  have hcard (A : Subgroup G) (hAR : A ≤ R) :
      Nat.card ((A.subgroupOf (T : Subgroup G)).map f) = E.relIndex A := by
    rw [←hrestrict A hAR,map_map,←relIndex_ker,hker,relIndex_subgroupOf hAR]
  have hDk : D.subgroupOf (T : Subgroup G) ≤ f.ker := by
    intro z hz
    let zr : R := ⟨z,hDR hz⟩
    have hh : zr ∈ (f.comp (inclusion hST.le)).ker := by
      rw [hker]
      exact mem_sup_right hz
    exact hh
  obtain ⟨u,hu⟩ := exists_noncommuting_restricted_image_of_conjugate_join
    (T : Subgroup G) U D J f ⟨x,hx⟩ (hUR.trans hST.le) inf_le_left hfamily hDk
    ((hcard U hUR).trans hiU) ((hcard J hJR).trans hiJ)
  exact ⟨⟨x,hx⟩,u,hu⟩
end CFSG.Quasithin.Chapter2
