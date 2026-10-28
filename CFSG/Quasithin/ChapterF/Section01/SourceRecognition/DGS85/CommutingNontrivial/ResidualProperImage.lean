module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingTrivial.WholeSpan
public import GorensteinWalter.SL2ProjectiveCover
public import Theory.GroupTheory.PResidual.PerfectImage

/-!
# Proper intersection images in a natural residual section

If the intersection filled the residual section, its commutator with the
opposite full-index actor would control the whole neighborhood. The source
commutator bound then gives a cubic order bound. The natural square quotient
forces its residual fixed denominator to be exactly the beta center, which
already lies in the proper intersection: a contradiction.

The main statement retains the fixed-denominator commutator explicitly.
For a field larger than two, perfectness supplies it from the residual/core cover.
Neither denominator containment nor a cubic order is assumed.
Source: DGS, *Groups and Graphs* (1985), 8.5, printed p.139.
-/

@[expose] public noncomputable section
open Subgroup Representation
open scoped MatrixGroups IsMulCommutative
open Subgroup.CosetGeometry.RankTwo Theory.GroupTheory.AmalgamGraph
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingNontrivial
open CommutingTrivial
variable {G : Type*} [Group G] {P : Fin 2 → Subgroup G} {B : Subgroup G}

private theorem residual_fixed_local_commutator
    (h : LocallyRankOneTriple P B) (beta : Vertex (family P))
    (hcore : ⁅Q (family P) beta,V (family P) beta 1⁆ ≤ Z (family P) beta)
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (hlarge : 3 < Nat.card F)
    (e : (graphLocalGroup (family P) beta ⧸ pCore 2 (graphLocalGroup (family P) beta)) ≃* SL(2,F)) :
    let L := graphLocalGroup (family P) beta
    let E := (pResidual 2 L).map L.subtype
    ⁅V (family P) beta 1 ⊓ centralizer (E : Set G),L⁆ ≤ Z (family P) beta := by
  let := finite_endpoints h
  let L := graphLocalGroup (family P) beta
  let E := (pResidual 2 L).map L.subtype
  let C := V (family P) beta 1 ⊓ centralizer (E : Set G)
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))
  let : Finite L := Finite.of_injective (inclusion (sylowGenerated_le _)) (inclusion_injective _)
  let : Group.IsPerfect SL(2,F) := GorensteinWalter.sl2_isPerfect_of_card_gt_three F hlarge
  have hmap : (pResidual 2 L).map q = ⊤ := by
    rw [map_pResidual_of_surjective 2 q (e.surjective.comp (QuotientGroup.mk'_surjective _)),
      pResidual_eq_top_of_isPerfect]
  have hker : q.ker = pCore 2 L := by
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective,QuotientGroup.ker_mk']
  have hsup : pResidual 2 L ⊔ pCore 2 L = ⊤ := by
    have hh := congrArg (Subgroup.comap q) hmap
    rwa [comap_map_eq,hker,comap_top] at hh
  have hcover : E ⊔ Q (family P) beta = L := by
    have hh := congrArg (Subgroup.map L.subtype) hsup
    have hc : (pCore 2 L).map L.subtype = Q (family P) beta := graphLocalGroup_core h beta
    rwa [Subgroup.map_sup,hc,←MonoidHom.range_eq_map,range_subtype] at hh
  change ⁅C,L⁆ ≤ Z (family P) beta
  rw [commutator_comm]
  rw [←hcover]
  apply commutator_sup_le_of_relative_normal L E (Q (family P) beta) C (Z (family P) beta)
    ((sylowGenerated_le _).trans (stabilizer_normalizes_Z (family P) beta))
    (map_subtype_le _) (core_le_graphLocalGroup h beta)
  · rw [commutator_comm]
    exact (commutator_eq_bot_iff_le_centralizer.mpr (show C ≤ centralizer (E : Set G) from inf_le_right)).le.trans bot_le
  · exact (commutator_mono le_rfl inf_le_left).trans hcore

/-- The source commutator bound makes the intersection image proper. -/
theorem source_residual_image_proper_of_fixed_commutator
    (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (hS : ∀ i, ∃ T : Sylow 2 (P i), (T : Subgroup (P i)).map (P i).subtype ≤ B)
    {beta mid : Vertex (family P)} (hm : (graph (family P)).Adj beta mid)
    (hz : Z (family P) beta = omegaCenterIn (graphLocalGroup (family P) beta))
    (hcore : ⁅Q (family P) beta,V (family P) beta 1⁆ ≤ Z (family P) beta)
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (e : (graphLocalGroup (family P) beta ⧸ pCore 2 (graphLocalGroup (family P) beta)) ≃* SL(2,F))
    (hfixed :
      let L := graphLocalGroup (family P) beta
      let E := (pResidual 2 L).map L.subtype
      ⁅V (family P) beta 1 ⊓ centralizer (E : Set G),L⁆ ≤ Z (family P) beta)
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    (σ : Representation (ZMod 2) SL(2,F) W)
    (c : BinaryConjugationSection (graphLocalGroup (family P) beta) (V (family P) beta 1)
      (V (family P) beta 1 ⊓ centralizer ((pResidual 2 (graphLocalGroup (family P) beta)).map
        (graphLocalGroup (family P) beta).subtype : Set G))
      (σ.comp (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 (graphLocalGroup (family P) beta))))))
    (hcW : Nat.card W = Nat.card F ^ 2)
    (A U : Subgroup G) (hAV : A ≤ V (family P) beta 1)
    (hZA : Z (family P) beta ≤ A) (hprop : ¬ V (family P) beta 1 ≤ A)
    (hVm : V (family P) beta 1 ≤ stabilizer (family P) mid)
    (hUL : U ≤ graphLocalGroup (family P) beta) (hpU : IsPGroup 2 U)
    (hi : (Q (family P) beta).relIndex U = Nat.card F)
    (hUm : U ≤ stabilizer (family P) mid)
    (hcomm : ⁅A,U⁆ ≤ Z (family P) mid)
    (hcm : Nat.card (Z (family P) mid) = Nat.card F ^ 2)
    (hcb : Nat.card (Z (family P) beta) = Nat.card F)
    [Finite (V (family P) beta 1)] [IsMulCommutative (V (family P) beta 1)] :
    c.imageSpace A ≠ ⊤ := by
  let := finite_endpoints h
  let L := graphLocalGroup (family P) beta
  let E := (pResidual 2 L).map L.subtype
  let C := V (family P) beta 1 ⊓ centralizer (E : Set G)
  intro him
  have hgen : V (family P) beta 1 = A ⊔ C :=
    le_antisymm (c.le_sup_kernel_of_image_top A him) (sup_le hAV inf_le_left)
  have hCC : ⁅C,U⁆ ≤ Z (family P) beta :=
    (commutator_mono le_rfl hUL).trans hfixed
  have hZbm : Z (family P) beta ≤ Z (family P) mid :=
    hz ▸ intrinsic_local_omega_le_neighbor_Z h hB hS hm
  have hR : ⁅V (family P) beta 1,U⁆ ≤ Z (family P) mid := by
    rw [hgen]
    exact commutator_sup_le_of_relative_normal (V (family P) beta 1) A C U (Z (family P) mid)
      (hVm.trans (stabilizer_normalizes_Z (family P) mid)) hAV inf_le_left hcomm (hCC.trans hZbm)
  have hcV := linear_neighborhood_card_bound_of_commutator h hB hS hm hz hcore e
    U hUL hpU hi hUm hR hcm hcb
  have hiC : C.relIndex (V (family P) beta 1) = Nat.card F ^ 2 := by
    have ht : c.imageSpace (V (family P) beta 1) = ⊤ :=
      top_unique (him ▸ c.imageSpace_mono hAV)
    have hv := c.imageSpace_card_eq_relIndex (V (family P) beta 1) le_rfl
    rw [ht,Nat.card_congr (Submodule.topEquiv : (⊤ : Submodule (ZMod 2) W) ≃ₗ[ZMod 2] W).toEquiv,hcW] at hv
    exact hv.symm
  have hZC : Z (family P) beta ≤ C := by
    refine le_inf (hZA.trans hAV) ?_
    intro x hx y hy
    have hx' := (mem_omegaCenterIn_iff _ _).mp (hz ▸ hx)
    exact hx'.2.1 y (map_subtype_le _ hy)
  let : Finite C := Finite.of_injective (inclusion (show C ≤ V (family P) beta 1 from inf_le_left))
    (inclusion_injective _)
  have hcC : Nat.card C ≤ Nat.card F := by
    have hh := relIndex_mul_card_of_le (show C ≤ V (family P) beta 1 from inf_le_left)
    rw [hiC] at hh
    have hp : 0 < Nat.card F := Nat.card_pos
    nlinarith [hcV]
  have he : Z (family P) beta = C := eq_of_le_of_card_ge hZC (by rwa [hcb])
  exact hprop (hgen.le.trans (sup_le le_rfl (he ▸ hZA)))

/-- Perfectness supplies the fixed-denominator commutator for a nonbinary field. -/
theorem source_natural_residual_image_proper
    (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (hS : ∀ i, ∃ T : Sylow 2 (P i), (T : Subgroup (P i)).map (P i).subtype ≤ B)
    {beta mid : Vertex (family P)} (hm : (graph (family P)).Adj beta mid)
    (hz : Z (family P) beta = omegaCenterIn (graphLocalGroup (family P) beta))
    (hcore : ⁅Q (family P) beta,V (family P) beta 1⁆ ≤ Z (family P) beta)
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (hlarge : 3 < Nat.card F)
    (e : (graphLocalGroup (family P) beta ⧸ pCore 2 (graphLocalGroup (family P) beta)) ≃* SL(2,F))
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    (σ : Representation (ZMod 2) SL(2,F) W)
    (c : BinaryConjugationSection (graphLocalGroup (family P) beta) (V (family P) beta 1)
      (V (family P) beta 1 ⊓ centralizer ((pResidual 2 (graphLocalGroup (family P) beta)).map
        (graphLocalGroup (family P) beta).subtype : Set G))
      (σ.comp (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 (graphLocalGroup (family P) beta))))))
    (hcW : Nat.card W = Nat.card F ^ 2)
    (A U : Subgroup G) (hAV : A ≤ V (family P) beta 1)
    (hZA : Z (family P) beta ≤ A) (hprop : ¬ V (family P) beta 1 ≤ A)
    (hVm : V (family P) beta 1 ≤ stabilizer (family P) mid)
    (hUL : U ≤ graphLocalGroup (family P) beta) (hpU : IsPGroup 2 U)
    (hi : (Q (family P) beta).relIndex U = Nat.card F)
    (hUm : U ≤ stabilizer (family P) mid)
    (hcomm : ⁅A,U⁆ ≤ Z (family P) mid)
    (hcm : Nat.card (Z (family P) mid) = Nat.card F ^ 2)
    (hcb : Nat.card (Z (family P) beta) = Nat.card F)
    [Finite (V (family P) beta 1)] [IsMulCommutative (V (family P) beta 1)] :
    c.imageSpace A ≠ ⊤ := by
  exact source_residual_image_proper_of_fixed_commutator h hB hS hm hz hcore e
    (residual_fixed_local_commutator h beta hcore hlarge e) σ c hcW A U hAV hZA hprop
    hVm hUL hpU hi hUm hcomm hcm hcb

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingNontrivial
