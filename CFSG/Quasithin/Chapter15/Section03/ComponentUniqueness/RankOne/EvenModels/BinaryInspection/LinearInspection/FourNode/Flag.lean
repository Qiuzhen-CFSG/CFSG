module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankOne.EvenModels.BinaryInspection.LinearInspection.FourNode.Selection
public import CFSG.Quasithin.Chapter2.Section01To03.ComponentRefinement.LieType.Binary.ParabolicPairs.SylowCoordinates
public import Theory.SpecificGroups.BinaryLinear.FourCentralizerOvergroups


/-!
# The degree-four flag from the source involution

Choose the actual binary linear component model. The inner representative of
the source involution is nonidentity, since otherwise the component lies in M.
It centralizes the component Sylow, so it is a rank-one transvection. Its
centralizer lies in M and equals the common stabilizer of its image line and
fixed hyperplane. Full-flag reconstruction identifies these as the first and
last cuts of the actual Sylow flag. The intrinsic transvection-overgroup cover
then gives both bounds required for node selection.

Source: Aschbacher--Smith, 1.1.5(3)(a), printed p.501, and 15.3.43,
the n = 1 paragraph on printed p.1140; the transvection geometry is the
independently proved calculation used in 2.3.9(7), pp.525--526.
-/

@[expose] public section

open Subgroup
open BinaryLinear BinaryLinear.OuterCyclic BinaryLinear.InvariantNodeActions
namespace CFSG.Quasithin.Chapter15.Section03.RankOne.EvenModels.BinaryInspection.LinearInspection
variable {G : Type*} [Group G] [Finite G]
variable {Yplus S M I L V₁ V₂ : Subgroup G}
variable (c : ReducedConfiguration Yplus S M I L V₁ V₂)

private theorem cut_of_rank (b : Basis 3) (W : Submodule (ZMod 2) (Space 4))
    (i : Fin 3) (hr : Module.finrank (ZMod 2) W = i.val + 1)
    (hB : cutStabilizer b Set.univ ≤ parabolic W) : W = cutSpace b i := by
  have h0 : W ≠ ⊥ := by intro he; rw [he, finrank_bot] at hr; omega
  have ht : W ≠ ⊤ := by
    intro he
    rw [he, finrank_top, Module.finrank_fin_fun] at hr
    have := i.isLt
    omega
  obtain ⟨j, hj⟩ := fullFlag_invariant_subspace b W h0 ht hB
  have he : j = i := by
    have hr' := congrArg (fun U : Submodule (ZMod 2) (Space 4) => Module.finrank (ZMod 2) U) hj
    rw [cutSpace_finrank, hr] at hr'
    exact Fin.ext (by omega)
  rwa [he] at hj

/-- The source inner involution constructs the actual centralizer flag. -/
theorem fourFlagData_of_source {z : G} (hz : SourceInvolution S M z)
    (hs : IsSimpleGroup L) (iso : ClassicalGroup.IsPSL L 4 2) (hi : ActsInner L z) :
    Nonempty (FourFlagData c) := by
  obtain ⟨e⟩ := exists_component_linearEquiv c hs (by decide : 0 < 4) iso
  have hinj : Function.Injective c.toComponentAction.componentMap := by
    apply (MonoidHom.ker_eq_bot_iff _).mp
    rw [c.toComponentAction.componentMap_ker, component_center_eq_bot c hs]
  let u := MulEquiv.ofBijective c.toComponentAction.componentMap
    ⟨hinj, c.toComponentAction.componentMap_surjective⟩
  let v := u.trans e
  let ep := v.trans (CFSG.Quasithin.Chapter2.ComponentRefinement.LieType.Binary.pslEquivLinear 4).symm
  have hv : CFSG.Quasithin.Chapter2.ComponentRefinement.LieType.Binary.linearModel ep = v := by
    apply MulEquiv.ext
    intro x
    exact (CFSG.Quasithin.Chapter2.ComponentRefinement.LieType.Binary.pslEquivLinear 4).apply_symm_apply (v x)
  have hu : u.toMonoidHom = c.toComponentAction.componentMap := rfl
  have hS : (S.subgroupOf L).map u.toMonoidHom =
      (c.toComponentAction.image S).subgroupOf (c.toComponentAction.image L) := by
    rw [hu, ← ParabolicInspection.componentMap_preimage_sylow c,
      map_comap_eq_self_of_surjective c.toComponentAction.componentMap_surjective]
  have hM : (M.subgroupOf L).map u.toMonoidHom =
      (c.toComponentAction.image (M ⊓ L)).subgroupOf (c.toComponentAction.image L) := by
    rw [quotient_intersection_eq c, inf_subgroupOf_right, hu,
      ← ParabolicInspection.componentMap_preimage_local c,
      map_comap_eq_self_of_surjective c.toComponentAction.componentMap_surjective]
  obtain ⟨T, hT⟩ := component_sylow c
  have hT' : (T : Subgroup L) = S.subgroupOf L := by
    apply map_injective L.subtype_injective
    rw [hT, subgroupOf_map_subtype]
  obtain ⟨t, ht⟩ := hi
  have ht1 : t ≠ 1 := by
    intro he
    apply c.component_outside
    intro x hx
    apply hz.centralizer_le
    rw [mem_centralizer_singleton_iff]
    have hh := ht ⟨x, hx⟩
    rw [he] at hh
    simp only [OneMemClass.coe_one, one_mul, inv_one, mul_one] at hh
    exact ((mul_inv_eq_iff_eq_mul).mp hh).symm
  have hTC : ∀ x : L, x ∈ T → x * t = t * x := by
    intro x hx
    have hxS : (x : G) ∈ S := by change x ∈ S.subgroupOf L; rwa [← hT']
    have hh := ht x
    have hzX : z * (x : G) * z⁻¹ = x := by rw [← hz.central x hxS, mul_inv_cancel_right]
    rw [hzX] at hh
    apply Subtype.ext
    exact ((mul_inv_eq_iff_eq_mul).mp hh.symm).symm
  have hCM : centralizer ({t} : Set L) ≤ M.subgroupOf L := by
    intro x hx
    have hcx : (x : G) * (t : G) = (t : G) * (x : G) :=
      congrArg Subtype.val (mem_centralizer_singleton_iff.mp hx)
    have hzX : z * (x : G) * z⁻¹ = x := by
      rw [ht x, ← hcx, mul_inv_cancel_right]
    exact hz.centralizer_le (mem_centralizer_singleton_iff.mpr
      ((mul_inv_eq_iff_eq_mul).mp hzX).symm)
  obtain ⟨coords⟩ := CFSG.Quasithin.Chapter2.ComponentRefinement.LieType.Binary.exists_transvectionCoordinates_of_centralizes_sylow
    (by decide : 2 ≤ 4) ep T ht1 hTC
  have hC : (centralizer ({t} : Set L)).map v.toMonoidHom =
      parabolic coords.line ⊓ parabolic coords.hyperplane := by
    rw [coords.centralizer_eq]
    change ((parabolic coords.line).comap (CFSG.Quasithin.Chapter2.ComponentRefinement.LieType.Binary.linearModel ep).toMonoidHom ⊓
      (parabolic coords.hyperplane).comap (CFSG.Quasithin.Chapter2.ComponentRefinement.LieType.Binary.linearModel ep).toMonoidHom).map
      v.toMonoidHom = _
    rw [hv, ← comap_inf, map_comap_eq_self_of_surjective v.surjective]
  let U := T.mapSurjective (f := v.toMonoidHom) v.surjective
  obtain ⟨b, hb⟩ := sylow_eq_cutStabilizer U
  have hUC : cutStabilizer b Set.univ ≤ parabolic coords.line ⊓ parabolic coords.hyperplane := by
    rw [← hC, ← hb]
    exact map_mono (fun x hx => mem_centralizer_singleton_iff.mpr (hTC x hx))
  have hl : coords.line = cutSpace b 0 :=
    cut_of_rank b coords.line 0 coords.line_finrank (hUC.trans inf_le_left)
  have hh : coords.hyperplane = cutSpace b 2 := by
    apply cut_of_rank b coords.hyperplane 2 _ (hUC.trans inf_le_right)
    change Module.finrank (ZMod 2) coords.hyperplane = 3
    have hd : Module.finrank (ZMod 2) coords.hyperplane + 1 = 4 := coords.hyperplane_finrank
    omega
  have he : (M.subgroupOf L).map v.toMonoidHom =
      ((c.toComponentAction.image (M ⊓ L)).subgroupOf
        (c.toComponentAction.image L)).map e.toMonoidHom := by
    change (M.subgroupOf L).map (e.toMonoidHom.comp u.toMonoidHom) = _
    rw [← map_map, hM]
  have hCP : parabolic coords.line ⊓ parabolic coords.hyperplane ≤
      (M.subgroupOf L).map v.toMonoidHom := by
    rw [← hC]
    exact map_mono hCM
  have hproper : (M.subgroupOf L).map v.toMonoidHom ≠ ⊤ := by
    intro htop
    apply c.component_outside
    apply subgroupOf_eq_top.mp
    apply top_unique
    intro x _
    have hx : v x ∈ (M.subgroupOf L).map v.toMonoidHom := htop ▸ mem_top _
    obtain ⟨y, hy, he⟩ := hx
    exact v.injective he ▸ hy
  have hcover := FourCentralizerOvergroups.flag_overgroup_cover coords.vector coords.functional
    coords.incident ((M.subgroupOf L).map v.toMonoidHom) hCP hproper
  change (M.subgroupOf L).map v.toMonoidHom ≤ parabolic coords.line ∨
    (M.subgroupOf L).map v.toMonoidHom ≤ parabolic coords.hyperplane at hcover
  refine ⟨⟨e, b, ?_, ?_, ?_⟩⟩
  · rw [← hS, map_map]
    change (S.subgroupOf L).map v.toMonoidHom = _
    rw [← hT']
    exact hb
  · have hmid : minimalParabolic b 1 = parabolic (cutSpace b 0) ⊓ parabolic (cutSpace b 2) := by
      ext g
      simp only [minimalParabolic, mem_cutStabilizer, mem_inf]
      change (∀ i : Fin 3, i ≠ 1 → g ∈ parabolic (cutSpace b i)) ↔ _
      constructor
      · exact fun h => ⟨h 0 (by decide), h 2 (by decide)⟩
      · intro h i hi
        fin_cases i <;> simp_all
    rw [hmid, ← hl, ← hh, ← he]
    exact hCP
  · rwa [hl, hh, he] at hcover

end CFSG.Quasithin.Chapter15.Section03.RankOne.EvenModels.BinaryInspection.LinearInspection
