module

public import Stellmacher.SectionNine.NineFiveSupportData
public import Stellmacher.SectionFiveToSeven.Result7_6

namespace Stellmacher.SectionNine

open Later SectionsFiveToSeven CosetGraphContext SevenSix

universe u

public theorem nine_five_penultimate_adjacent
    {G : Type u} [Group G] [Finite G] {T A B : Subgroup G}
    (ctx : SectionNineLocalContext G T A B) :
    ctx.Γ.adjacent
      (ctx.criticalPath.path ⟨ctx.criticalPath.length - 1,
        Nat.lt_succ_of_le (Nat.sub_le _ _)⟩) ctx.criticalPath.a' := by
  have hpositive := ctx.criticalPath.length_pos
  have hedge := ctx.criticalPath.path_adj ⟨ctx.criticalPath.length - 1, by omega⟩
  convert hedge using 1
  · apply congrArg ctx.criticalPath.path
    apply Fin.ext
    rfl
  · rw [← ctx.criticalPath.path_end]
    apply congrArg ctx.criticalPath.path
    apply Fin.ext
    simp
    omega

public theorem nine_five_penultimate_core_le_terminal
    {G : Type u} [Group G] [Finite G] {T A B : Subgroup G}
    (ctx : SectionNineLocalContext G T A B) :
    twoCoreIn (EAt ctx.Γ
      (ctx.criticalPath.path ⟨ctx.criticalPath.length - 1,
        Nat.lt_succ_of_le (Nat.sub_le _ _)⟩)) ≤ GAt ctx.Γ ctx.criticalPath.a' := by
  let penultimate := ctx.criticalPath.path ⟨ctx.criticalPath.length - 1,
    Nat.lt_succ_of_le (Nat.sub_le _ _)⟩
  have hcore : twoCoreIn (EAt ctx.Γ penultimate) ≤ QAt ctx.Γ penultimate := by
    change twoCoreIn (e ctx.Γ penultimate) ≤ q ctx.Γ penultimate
    rw [CosetGraphContext.e, ctx.Γ.twoResidualAt_def, q, ctx.Γ.twoCoreAt_def,
      residual_core_eq_inter_core]
    exact inf_le_right
  exact hcore.trans
    (((lemma_seven_three ctx.sectionSeven ctx.Γ).sylow_and_core penultimate
      ctx.criticalPath.a' ((mem_neighborhood_iff_adjacent ctx.Γ).mpr
        (nine_five_penultimate_adjacent ctx)) (default : Sylow 2
          (stabilizer ctx.Γ penultimate ⊓ stabilizer ctx.Γ ctx.criticalPath.a' : Subgroup G))).2.2)

public theorem nine_five_neighbor_module_le_of_residual_normalizes
    {G : Type u} [Group G] [Finite G] {T A B : Subgroup G}
    (ctx : SectionNineLocalContext G T A B)
    (neighbor terminal : ctx.Γ.Vertex) (hadj : ctx.Γ.adjacent neighbor terminal)
    (container : Subgroup G) (hcenter : ZAt ctx.Γ neighbor ≤ container)
    (hnormal : EAt ctx.Γ terminal ≤ Subgroup.normalizer (container : Set G)) :
    VAt ctx.Γ terminal ≤ container := by
  let localGroup := GAt ctx.Γ terminal
  let edge := GAt ctx.Γ neighbor ⊓ localGroup
  let sylow : Sylow 2 edge := default
  let sylowImage := sylowTwoAmbient edge sylow
  let residual := EAt ctx.Γ terminal
  have hneighbor : neighbor ∈ neighborhood ctx.Γ terminal :=
    (mem_neighborhood_iff_adjacent ctx.Γ).mpr (ctx.Γ.adjacent_symm hadj)
  have hsylow : IsSylowTwoIn sylowImage localGroup :=
    ((lemma_seven_three ctx.sectionSeven ctx.Γ).sylow_and_core neighbor terminal
      ((mem_neighborhood_iff_adjacent ctx.Γ).mpr hadj) sylow).2.1
  have hresidual : residual = twoResidualIn localGroup := by
    change e ctx.Γ terminal = twoResidualIn (stabilizer ctx.Γ terminal)
    rw [CosetGraphContext.e, ctx.Γ.twoResidualAt_def]
    rfl
  have hresidual_le : residual ≤ localGroup := hresidual ▸ twoResidualIn_le _
  have hgenerate : residual ⊔ sylowImage = localGroup := by
    rw [hresidual]
    exact twoResidualIn_sup_sylow hsylow
  let _ : (residual.subgroupOf localGroup).Normal := by
    rw [hresidual]
    exact twoResidualIn_normal _
  have hnative : sylowImage.subgroupOf localGroup ⊔ residual.subgroupOf localGroup = ⊤ := by
    rw [← Subgroup.subgroupOf_sup hsylow.1 hresidual_le, sup_comm, hgenerate,
      Subgroup.subgroupOf_self]
  rw [VAt, v, ctx.Γ.vAt_def]
  apply sSup_le
  rintro center ⟨vertex, hvertex, rfl⟩
  obtain ⟨actor, hactor⟩ := (lemma_seven_one ctx.sectionSeven ctx.Γ).local_transitivity
    terminal hneighbor hvertex
  have hactor_native : actor ∈ sylowImage.subgroupOf localGroup ⊔
      residual.subgroupOf localGroup := by rw [hnative]; trivial
  obtain ⟨wheel, hwheel, mover, hmover, hfactor⟩ :=
    Subgroup.mem_sup_of_normal_right.mp hactor_native
  have hwheel_edge : (wheel : G) ∈ edge :=
    (Subgroup.map_subtype_le (sylow : Subgroup edge)) hwheel
  have hwheel_fixed : ctx.Γ.act (wheel : G) neighbor = neighbor :=
    (Set.ext_iff.mp (ctx.Γ.stabilizer_def neighbor) (wheel : G)).mp hwheel_edge.1
  have hmove : ctx.Γ.act (mover : G) neighbor = vertex := by
    rw [← hwheel_fixed, ← ctx.Γ.act_mul]
    exact (congrArg (fun element : localGroup => ctx.Γ.act (element : G) neighbor)
      hfactor).trans hactor
  change z ctx.Γ vertex ≤ container
  rw [← hmove, z_act]
  exact (Subgroup.map_mono hcenter).trans_eq
    (Subgroup.mem_normalizer_iff_map_conj_eq.mp
      ((Subgroup.normalizer (container : Set G)).inv_mem (hnormal hmover)))

public theorem nine_five_two_support_span_of_neighbor_center
    {G : Type u} [Group G] [Finite G] {T A B : Subgroup G}
    (ctx : SectionNineLocalContext G T A B)
    (neighbor terminal : ctx.Γ.Vertex) (hadj : ctx.Γ.adjacent neighbor terminal)
    (support : Subgroup G) (conjugator : G)
    (hsupport : support ≤ VAt ctx.Γ terminal)
    (hnormal : EAt ctx.Γ terminal ≤ Subgroup.normalizer (support : Set G))
    (hconjugator : conjugator ∈ GAt ctx.Γ terminal)
    (hcenter : ZAt ctx.Γ neighbor ≤
      support ⊔ support.map (MulAut.conj conjugator⁻¹).toMonoidHom) :
    VAt ctx.Γ terminal = support ⊔ support.map (MulAut.conj conjugator⁻¹).toMonoidHom := by
  let conjugation := MulAut.conj conjugator⁻¹
  have hresidual : EAt ctx.Γ terminal = twoResidualIn (GAt ctx.Γ terminal) := by
    change e ctx.Γ terminal = twoResidualIn (stabilizer ctx.Γ terminal)
    rw [CosetGraphContext.e, ctx.Γ.twoResidualAt_def]
    rfl
  have hlocal_normal : GAt ctx.Γ terminal ≤
      Subgroup.normalizer (EAt ctx.Γ terminal : Set G) := by
    rw [hresidual]
    exact (Subgroup.normal_subgroupOf_iff_le_normalizer (twoResidualIn_le _)).mp
      (twoResidualIn_normal _)
  have hresidual_map : (EAt ctx.Γ terminal).map conjugation.toMonoidHom =
      EAt ctx.Γ terminal := Subgroup.mem_normalizer_iff_map_conj_eq.mp
        ((Subgroup.normalizer (EAt ctx.Γ terminal : Set G)).inv_mem
          (hlocal_normal hconjugator))
  have hother_normal : EAt ctx.Γ terminal ≤
      Subgroup.normalizer (support.map conjugation.toMonoidHom : Set G) := by
    rw [← hresidual_map]
    exact (Subgroup.map_mono hnormal).trans (Subgroup.le_normalizer_map _)
  apply le_antisymm
  · exact nine_five_neighbor_module_le_of_residual_normalizes ctx neighbor terminal hadj
      _ hcenter ((le_inf hnormal hother_normal).trans
        (Subgroup.normalizer_inf_normalizer_le_normalizer_sup _ _))
  · apply sup_le hsupport
    exact (Subgroup.map_mono hsupport).trans_eq
      (Subgroup.mem_normalizer_iff_map_conj_eq.mp
        ((Subgroup.normalizer (VAt ctx.Γ terminal : Set G)).inv_mem
          (stabilizer_le_normalizer_v ctx.Γ terminal hconjugator)))

end Stellmacher.SectionNine
