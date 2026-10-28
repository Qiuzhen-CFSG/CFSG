module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.Noncommuting.LocalSections
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.LocalStructure.Centers
public import Theory.Representation.BinaryConjugationSection.Descent
public import Theory.Representation.BinaryConjugationSection.CentralKernel
public import Theory.Representation.BinaryConjugationSection.ActionKernel
public import Theory.ElementaryAbelian.Quotient

/-!
# Constructing the actual endpoint center sections

The central omega of the local actor lies in every local Sylow center and
hence in the original vertex center span. Conjugation therefore constructs
the literal Z/Ω₁(Z(L)) module through L/Q, with its original quotient
coordinates. The same Sylow seed proves corrected fixed-space generation.
We also construct the unquotiented Z action; the critical centralizer
intersection proves that every actual Sylow image acts faithfully on it.

Source: DGS, *Groups and Graphs* (1985), (3.8), (6.2), (7.1),
printed pp.82–83,119,126–127, with the correction to (5.12).
`EndpointKernel` passes the Sylow faithfulness to the central quotient.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryConjugationSection
open Representation.BinaryOffender Representation.RankOne.QuadraticRecognition
open Theory.GroupTheory.AmalgamGraph Subgroup.CosetGeometry.RankTwo
open scoped commutatorElement IsMulCommutative
namespace CFSG.Quasithin.ChapterF.Source.DGS85.Noncommuting
universe u
variable {G : Type u} [Group G]

/-- Relative centrality places the denominator in the original Sylow-center span. -/
theorem local_omega_le_center_span (P E : Subgroup G) (c : LocalRankOneData P E)
    (hodd : ¬ 2 ∣ c.Pstar.relIndex P) :
    Stellmacher.omegaOneCenterAmbient c.Pstar ≤ sylowCenterSpan P := by
  rw [local_center_span P E c hodd]
  let O := Stellmacher.omegaOneCenterAmbient c.Pstar
  let : IsElementaryAbelian 2 O := Stellmacher.omegaOneCenterAmbient_elementaryAbelian _
  let T := (c.sylow : Subgroup c.Pstar).map c.Pstar.subtype
  have hOL : O ≤ c.Pstar := fun x hx =>
    (Stellmacher.mem_omegaOneCenterAmbient_iff _ _).mp hx |>.1
  have hOC : O ≤ centralizer (T : Set G) := by
    intro x hx t ht
    exact (Stellmacher.mem_omegaOneCenterAmbient_iff _ _).mp hx |>.2.2 t (map_subtype_le _ ht)
  have hOT : O ≤ T := le_sylow_image_of_normalizes c.Pstar c.sylow rfl
    (IsElementaryAbelian.isPGroup 2 O) hOL (hOC.trans (Subgroup.centralizer_le_normalizer _))
  apply le_trans _ (le_iSup (fun S : Sylow 2 c.Pstar =>
    omegaCenterIn ((S : Subgroup c.Pstar).map c.Pstar.subtype)) c.sylow)
  intro x hx
  exact (Stellmacher.mem_omegaOneCenterAmbient_iff T x).mpr
    ⟨hOT hx,(Stellmacher.mem_omegaOneCenterAmbient_iff _ _).mp hx |>.2.1,hOC hx⟩

/-- Construct the source section and its fixed-space generation using the same quotient map. -/
theorem graph_endpoint_section_exists
    {P : Fin 2 → Subgroup G} {B : Subgroup G}
    (h : LocallyRankOneTriple P B) (v : Vertex (family P))
    (E : Subgroup G) (c : LocalRankOneData (stabilizer (family P) v) E)
    (hodd : ¬ 2 ∣ c.Pstar.relIndex (stabilizer (family P) v))
    [((Q (family P) v).subgroupOf c.Pstar).Normal] :
    let A := Z (family P) v
    let C := Stellmacher.omegaOneCenterAmbient c.Pstar
    letI := graph_Z_elementary h v
    ∃ (σ : Representation (ZMod 2) (c.Pstar ⧸ (Q (family P) v).subgroupOf c.Pstar)
      (Additive (A ⧸ C.subgroupOf A)))
      (s : BinaryConjugationSection c.Pstar A C
        (σ.comp (QuotientGroup.mk' ((Q (family P) v).subgroupOf c.Pstar)))),
      (∀ z : A, (s.coordinates z).toAdd =
        Additive.ofMul (QuotientGroup.mk' (C.subgroupOf A) z)) ∧
      ∀ T : Sylow 2 c.Pstar, GeneratedByFixedSpace σ
        ((T : Subgroup c.Pstar).map (QuotientGroup.mk' ((Q (family P) v).subgroupOf c.Pstar))) := by
  let := finite_endpoints h
  let := graph_Z_elementary h v
  have hZL : Z (family P) v ≤ c.Pstar := by
    change sylowCenterSpan (stabilizer (family P) v) ≤ c.Pstar
    rw [local_center_span _ _ c hodd]
    exact sylowCenterSpan_le _
  have hnZ : c.Pstar ≤ normalizer (Z (family P) v : Set G) :=
    c.Pstar_le.trans ((normal_subgroupOf_iff_le_normalizer (Z_le_stabilizer _ _)).mp (Z_normal _ _))
  obtain ⟨σ,s,hs⟩ := exists_descended_actor c.Pstar (Z (family P) v)
    (Stellmacher.omegaOneCenterAmbient c.Pstar) hZL (local_omega_le_center_span _ _ c hodd)
    hnZ (c.Pstar.le_normalizer.trans (normalizer_le_normalizer_omegaCenterIn _))
    (QuotientGroup.mk' ((Q (family P) v).subgroupOf c.Pstar))
    (QuotientGroup.mk'_surjective _) (by
      intro a ha z hz
      have haQ : (a : G) ∈ Q (family P) v := (QuotientGroup.eq_one_iff a).mp ha
      have hc := graph_Q_centralizes_Z h v haQ z hz
      rw [commutatorElement_eq_one_iff_mul_comm.mpr hc.symm]
      exact one_mem _)
  exact ⟨σ,s,hs,fun T => local_section_generated _ _ c hodd σ _ s T⟩

/-- Construct the unquotiented endpoint action, retaining identity coordinates. -/
theorem graph_endpoint_full_action_exists
    {P : Fin 2 → Subgroup G} {B : Subgroup G}
    (h : LocallyRankOneTriple P B) (v : Vertex (family P))
    (E : Subgroup G) (c : LocalRankOneData (stabilizer (family P) v) E)
    (hodd : ¬ 2 ∣ c.Pstar.relIndex (stabilizer (family P) v))
    [((Q (family P) v).subgroupOf c.Pstar).Normal] :
    letI := graph_Z_elementary h v
    ∃ (σ : Representation (ZMod 2) (c.Pstar ⧸ (Q (family P) v).subgroupOf c.Pstar)
      (Additive (Z (family P) v)))
      (s : BinaryConjugationSection c.Pstar (Z (family P) v) ⊥
        (σ.comp (QuotientGroup.mk' ((Q (family P) v).subgroupOf c.Pstar)))),
      ∀ z : Z (family P) v, (s.coordinates z).toAdd = Additive.ofMul z := by
  let := finite_endpoints h
  let := graph_Z_elementary h v
  have hZL : Z (family P) v ≤ c.Pstar := by
    change sylowCenterSpan (stabilizer (family P) v) ≤ c.Pstar
    rw [local_center_span _ _ c hodd]
    exact sylowCenterSpan_le _
  apply exists_of_central_kernel c.Pstar _ hZL
    (c.Pstar_le.trans ((normal_subgroupOf_iff_le_normalizer (Z_le_stabilizer _ _)).mp (Z_normal _ _)))
    (QuotientGroup.mk' ((Q (family P) v).subgroupOf c.Pstar)) (QuotientGroup.mk'_surjective _)
  intro a ha
  exact graph_Q_centralizes_Z h v ((QuotientGroup.eq_one_iff a).mp ha)

/-- The critical centralizer theorem detects the entire two-part of the original action kernel. -/
theorem graph_critical_full_action_sylow_kernel
    {P : Fin 2 → Subgroup G} {B : Subgroup G}
    (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (hS : ∀ i, ∃ T : Sylow 2 (P i), (T : Subgroup (P i)).map (P i).subtype ≤ B)
    {v w : Vertex (family P)} (hc : IsCriticalPair (family P) v w)
    {H : Subgroup G} (hH : H ≤ stabilizer (family P) v)
    [((Q (family P) v).subgroupOf H).Normal]
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    (σ : Representation (ZMod 2) (H ⧸ (Q (family P) v).subgroupOf H) W)
    (s : BinaryConjugationSection H (Z (family P) v) ⊥
      (σ.comp (QuotientGroup.mk' ((Q (family P) v).subgroupOf H)))) (T : Sylow 2 H) :
    Disjoint σ.ker ((T : Subgroup H).map (QuotientGroup.mk' ((Q (family P) v).subgroupOf H))) := by
  let A := (T : Subgroup H).map H.subtype
  have hi := source_critical_inf_centralizer h hB hS hc A (T.isPGroup'.map _) ((map_subtype_le _).trans hH)
  apply disjoint_iff.mpr
  apply bot_unique
  rintro _ ⟨hk,t,ht,rfl⟩
  apply (QuotientGroup.eq_one_iff t).mpr
  have hct : (t : G) ∈ centralizer (Z (family P) v : Set G) := by
    intro z hz
    have hh := (s.action_mem_ker_iff t).mp hk z hz
    exact (commutatorElement_eq_one_iff_mul_comm.mp (mem_bot.mp hh)).symm
  exact (hi.le ⟨mem_map_of_mem H.subtype ht,hct⟩).2

end CFSG.Quasithin.ChapterF.Source.DGS85.Noncommuting
