module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.StarQuotient
public import Theory.Representation.BinaryConjugationSection.CentralDisplacement

/-!
# The source star quotient at positive distance

The star is contained in the two-core and its component displacement lies in
the elementary moving layer, which centralizes that core. Hence squares in
the star centralize the component. The quotient by the entire component
centralizer is elementary even without elementary structure on the whole star.
Core displacement descends the literal conjugation action through the original
vertex quotient, and perfectness rules out new component-fixed vectors.

This extends the quotient construction to distance two while retaining all
fixed attachments. Source: MS93 (3.4), printed p.869.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative commutatorElement

open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
open CFSG.Quasithin.ChapterC.RankTwo.Sp4Four
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic.DistanceTwoRecognition
variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)
variable (d : CharacteristicReduction K R)
include h

/-- The star modulo its full component centralizer is an elementary module
at every positive critical distance, even when the whole star is nonabelian. -/
theorem replacement_sourceStarQuotient_over
    (geometry : Geometry d.radical) (hb : 0 < geometry.b d.radical)
    (Y : Subgroup d.radical) (P : Sylow 2 (Ltilde d.radical (alpha d.radical)))
    (hY : Y.map (embedS d.radical) = componentSylowSeed d.radical (alpha d.radical) P)
    (hn : Q d.radical (beta d.radical) ≤
      normalizer (Y.map (embedS d.radical) : Set (FreeAmalgam d.radical)))
    {J : Type*} [Group J] (κ : stabilizer d.radical (alpha d.radical) →* J)
    (hκ : Function.Surjective κ)
    (hκQ : κ.ker.map (stabilizer d.radical (alpha d.radical)).subtype =
      Q d.radical (alpha d.radical)) :
    ∃ s : SourceStarQuotient d.radical Y J, s.quotient = κ := by
  let S := stabilizer d.radical (alpha d.radical)
  let A := sourceStarAlpha d.radical Y
  let L₀ := Ltilde d.radical (alpha d.radical)
  let U₀ := U d.radical (alpha d.radical)
  let C₀ := A ⊓ centralizer (L₀ : Set (FreeAmalgam d.radical))
  have hAS : A ≤ S := sourceStarAlpha_le_stabilizer _ _
  have hAQ := h.replacement_sourceStarAlpha_le_own_core d geometry hb Y P hY hn
  have hLS : L₀ ≤ S := Ltilde_le_stabilizer _
  have hSL : S ≤ normalizer (L₀ : Set (FreeAmalgam d.radical)) := by
    have ht := le_normalizer_map (H := pResidual 2 S) S.subtype
    rw [normalizer_eq_top,←MonoidHom.range_eq_map,range_subtype] at ht
    exact ht
  have hNC : normalizer (L₀ : Set (FreeAmalgam d.radical)) ≤
      normalizer (centralizer (L₀ : Set (FreeAmalgam d.radical)) : Set _) :=
    (normal_subgroupOf_iff_le_normalizer (Subgroup.centralizer_le_normalizer _)).mp inferInstance
  have hSN : S ≤ normalizer (C₀ : Set (FreeAmalgam d.radical)) :=
    (le_inf (sourceStarAlpha_normalized _ _)
      (hSL.trans hNC)).trans
      inf_normalizer_le_normalizer_inf
  have hAL : A ≤ normalizer (L₀ : Set (FreeAmalgam d.radical)) :=
    hAS.trans hSL
  have hC : C₀ = A ⊓ fixedCore d.radical (alpha d.radical) := by
    ext x
    exact ⟨fun hx => ⟨hx.1,hAQ hx.1,hx.2⟩,fun hx => ⟨hx.1,hx.2.2⟩⟩
  let : (C₀.subgroupOf A).Normal :=
    normal_subgroupOf_of_le_normalizer (hAS.trans hSN)
  have hN : C₀.subgroupOf A = (centralizer (L₀ : Set (FreeAmalgam d.radical))).subgroupOf A := by
    ext a
    exact ⟨fun ha => ha.2,fun ha => ⟨a.property,ha⟩⟩
  let : ((centralizer (L₀ : Set (FreeAmalgam d.radical))).subgroupOf A).Normal :=
    hN ▸ inferInstance
  let : IsElementaryAbelian 2 U₀ := h.replacement_vertex_moving_elementary d rfl
  let : IsElementaryAbelian 2 (A ⧸ (centralizer (L₀ : Set (FreeAmalgam d.radical))).subgroupOf A) :=
    Subgroup.central_displacement_quotient_elementary A L₀ U₀
      (h.replacement_sourceStarAlpha_commutator_le_U d geometry hb Y P hY hn)
      (commutator_eq_bot_iff_le_centralizer.mp
        ((commutator_mono (U_le_Z _) hAQ).trans_eq (Z_centralizes_Q _ _ rfl) |>.antisymm bot_le))
  let : IsElementaryAbelian 2 (A ⧸ C₀.subgroupOf A) :=
    IsElementaryAbelian.of_surjective (QuotientGroup.quotientMulEquivOfEq hN).symm.toMonoidHom
      (QuotientGroup.quotientMulEquivOfEq hN).symm.surjective
  obtain ⟨z,path,hfirst⟩ := exists_replacement_critical_path_through_beta d geometry hb
  have hbound := h.replacement_sourceStarAlpha_core_displacement d geometry hb
    path hfirst Y P hY hn
  obtain ⟨σ,c,hc⟩ := BinaryConjugationSection.exists_descended_actor S A C₀ hAS inf_le_left
    (sourceStarAlpha_normalized _ _) hSN κ hκ (by
      intro a ha x hx
      have haQ : (a : FreeAmalgam d.radical) ∈ Q d.radical (alpha d.radical) :=
        hκQ ▸ mem_map_of_mem S.subtype ha
      have hm : ⁅(a : FreeAmalgam d.radical),x⁆ ∈ ⁅A,Q d.radical (alpha d.radical)⁆ := by
        rw [commutator_comm]
        exact commutator_mem_commutator haQ hx
      refine ⟨?_,(hbound hm).2⟩
      rw [commutatorElement_def]
      exact A.mul_mem ((mem_normalizer_iff.mp
        (sourceStarAlpha_normalized d.radical Y a.property) x).mp hx) (A.inv_mem hx))
  let : Group.IsPerfect (K.subgroupOf d.overgroup) := (h.replacement_component d).perfect
  let : Group.IsPerfect (Ltilde d.radical (alpha d.radical)) := by
    rw [Ltilde_alpha,h.replacement_residual d]
    exact Group.IsPerfect.map _
  have hfixed := BinaryConjugationSection.fixed_section_eq_bot S A L₀ hLS hAL κ σ c
  let : Finite S := finite_stabilizer _ _
  let : Finite A := Finite.of_injective (inclusion hAS) (inclusion_injective _)
  refine ⟨{
    Carrier := Additive (A ⧸ C₀.subgroupOf A)
    quotient := κ
    quotient_surjective := hκ
    quotient_kernel := hκQ
    action := σ
    sectionData := ?_
    fixed_eq_bot := hfixed },rfl⟩
  rw [←hC]
  exact c

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic.DistanceTwoRecognition
