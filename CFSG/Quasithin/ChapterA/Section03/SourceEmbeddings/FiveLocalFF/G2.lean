module
public import Theory.AtlasPort.LinearGroups.G2.HigherFieldResiduals
public import Theory.AtlasPort.LinearGroups.G2.Simplicity
public import Theory.AtlasPort.LinearGroups.G2.DerivedEvenOrder
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.FiveLocalFF.RankOneCovers
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.Quotients
public import Theory.GroupTheory.CComponent.QuotientLifting
public import Theory.GroupTheory.PCoreFrattiniTransport

/-!
# Local alternating-five sections in the characteristic-two G₂ model

Conjugate the given full Sylow subgroup to the six positive root groups.
Proper Sylow-overgroup geometry puts its join with the local C-component
in a standard parabolic. Perfectness places the component in the parabolic
residual, which also contains the standard Sylow. The residual has a
rank-one quotient with two-group kernel, so the rank-one cover theorem
identifies the original component with that literal residual.

The quotient by its actual two-core has SL₂ order. An alternating-five
marking forces field cardinality four. The derived binary carrier is
excluded directly by its order 6048. None of these statements assume
quasisimplicity of the smaller local C-component or discard its two-core.

Source: Aschbacher–Smith A.3.12, F.1.12 and the constrained FF-action
argument in 10.2.9, printed pp.47–48, 262–264 and 751–752
(1 March 2004 manuscript).
-/

public section
noncomputable section
open Subgroup Theory.GroupTheory Atlas.G2 Atlas.G2.LieParabolicSetup
open scoped MatrixGroups Pointwise
namespace CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.FiveLocalFF.G2
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

private theorem local_perfect {G : Type*} [Group G] (S : Subgroup G)
    {B : Subgroup G} (hB : B ∈ localCComponents S) : Group.IsPerfect B := by
  let := hB.perfect
  exact Group.IsPerfect.ofSurjective
    (f := (subgroupOfEquivOfLe (show B ≤ B ⊔ S from le_sup_left)).toMonoidHom)
    (subgroupOfEquivOfLe le_sup_left).surjective

/-- A proper full-Sylow local C-component is a conjugate of one literal
G₂ parabolic residual. -/
theorem local_placement (hq : 2 < Nat.card F)
    (S : Sylow 2 (Model F)) (B : Subgroup (Model F))
    (hB : B ∈ localCComponents S) (hproper : B ≠ ⊤) :
    ∃ g : Model F, B.map (MulAut.conj g).toMonoidHom = local₁ ∨
      B.map (MulAut.conj g).toMonoidHom = local₂ := by
  let : IsSimpleGroup (Model F) := Atlas.G2.isSimple hq
  have hjoin : B ⊔ (S : Subgroup (Model F)) ≠ ⊤ := by
    intro ht
    have hc : B.IsCComponent := by
      have hm := hB
      change (B.subgroupOf (B ⊔ (S : Subgroup (Model F)))).IsCComponent at hm
      rw [ht] at hm
      simpa only [map_subgroupOf_eq_of_le le_top] using hm.map_subtype (.top)
    exact (hc.subnormal.eq_bot_or_top_of_isSimpleGroup inferInstance).elim hc.ne_bot hproper
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (Model F) S (sylow (F := F))
  have hSU : (S : Subgroup (Model F)).map (MulAut.conj g).toMonoidHom = unipotent := by
    rw [← sylow_coe, ← hg, Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def]
    rfl
  let a := MulAut.conj g
  let S' := S.mapSurjective (f := a.toMonoidHom) a.surjective
  let : Group.IsSolvable a.toMonoidHom.ker := by
    rw [a.toMonoidHom.ker_eq_bot_iff.mpr a.injective]
    infer_instance
  have hl : B.map a.toMonoidHom ∈ localCComponents (S' : Subgroup (Model F)) :=
    Chapter1.Section02.localCComponents_map_of_solvable_ker hB a.toMonoidHom
  have hp := ProperSylowOvergroups.le_parabolic
    ((B ⊔ (S : Subgroup (Model F))).map a.toMonoidHom)
    (hSU ▸ map_mono (show (S : Subgroup (Model F)) ≤ B ⊔ (S : Subgroup (Model F)) from le_sup_right))
    (lt_top_iff_ne_top.mpr (by
      intro ht
      apply hjoin
      apply Subgroup.map_injective (f := a.toMonoidHom) a.injective
      rw [map_top_of_surjective a.toMonoidHom a.surjective]
      exact ht))
  rw [Subgroup.map_sup] at hp
  refine ⟨g, ?_⟩
  let := local_perfect (S' : Subgroup (Model F)) hl
  rcases hp with hp | hp
  · left
    let := local₁_isPerfect hq
    apply local_eq_of_sl2_core_quotient local₁ hq
      (local₁CoreQuotientEquivPSL.trans longSLEquivPSL.symm) S' (B.map a.toMonoidHom) hl
    · rw [← HigherFieldResiduals.parabolic₁_residual hq]
      exact le_map_solvableResidual_of_isPerfect _ parabolic₁ (le_sup_left.trans hp)
    · change (S : Subgroup (Model F)).map a.toMonoidHom ≤ local₁
      rw [hSU]
      exact unipotent_le_local₁
  · right
    let := local₂_isPerfect hq
    apply local_eq_of_sl2_core_quotient local₂ hq
      (local₂CoreQuotientEquivPSL.trans longSLEquivPSL.symm) S' (B.map a.toMonoidHom) hl
    · rw [← HigherFieldResiduals.parabolic₂_residual hq]
      exact le_map_solvableResidual_of_isPerfect _ parabolic₂ (le_sup_left.trans hp)
    · change (S : Subgroup (Model F)).map a.toMonoidHom ≤ local₂
      rw [hSU]
      exact unipotent_le_local₂

/-- The actual A₅ two-core section forces field size four and literal
short- or long-parabolic residual placement. -/
theorem five_section_placement (hq : 2 < Nat.card F)
    (S : Sylow 2 (Model F)) (B : Subgroup (Model F))
    (hB : B ∈ localCComponents S) (hproper : B ≠ ⊤)
    (e : (B ⧸ pCore 2 B) ≃* alternatingGroup (Fin 5)) :
    Nat.card F = 4 ∧ ∃ g : Model F,
      B.map (MulAut.conj g).toMonoidHom = local₁ ∨
      B.map (MulAut.conj g).toMonoidHom = local₂ := by
  obtain ⟨g, hg⟩ := local_placement hq S B hB hproper
  refine ⟨?_, g, hg⟩
  let a := (MulAut.conj g).subgroupMap B
  let aq := QuotientGroup.congr _ _ a (pCore_map_iso 2 a)
  rcases hg with hp | hp
  · have ep : ((B.map (MulAut.conj g).toMonoidHom) ⧸
        pCore 2 (B.map (MulAut.conj g).toMonoidHom)) ≃* SL(2, F) := by
      rw [hp]
      exact (QuotientGroup.quotientMulEquivOfEq local₁_intrinsic_pCore).trans
        local₁RadicalQuotientEquivSL
    exact field_four_of_sl2_five_section e (aq.trans ep)
  · have ep : ((B.map (MulAut.conj g).toMonoidHom) ⧸
        pCore 2 (B.map (MulAut.conj g).toMonoidHom)) ≃* SL(2, F) := by
      rw [hp]
      exact (QuotientGroup.quotientMulEquivOfEq local₂_pCore).trans
        local₂RadicalQuotientEquivSL
    exact field_four_of_sl2_five_section e (aq.trans ep)

omit [CharP F 2] in
/-- The derived binary carrier has no alternating-five two-core section. -/
theorem binary_derived_excluded (hF : Nat.card F = 2)
    (B : Subgroup (commutator (Model F)))
    (e : (B ⧸ pCore 2 B) ≃* alternatingGroup (Fin 5)) : False := by
  have hd := card_quotient_dvd_card (pCore 2 B)
  rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup] at hd
  norm_num at hd
  have h := (by decide : 5 ∣ 60).trans (hd.trans B.card_subgroup_dvd_card)
  rw [DerivedEvenOrder.card_derived_binary hF] at h
  norm_num at h

end CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.FiveLocalFF.G2
