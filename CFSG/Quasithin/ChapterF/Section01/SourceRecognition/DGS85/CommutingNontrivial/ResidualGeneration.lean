module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingNontrivial.ResidualDescent
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingNontrivial.ResidualComparisonApplication
public import Theory.Representation.BinaryConjugationSection.ConjugateSpan
public import Theory.Representation.BinaryConjugationSection.SylowGeneration

/-!
# Corrected fixed-space generation on the Chapter 8 residual join

The normal subgroup D = O²(L_alpha') Q_lambda meets the full edge Sylow
in an actual Sylow S of D. In the counterexample branch of 8.3 that
intersection is the quotient omega preimage. Its displacement on the
neighboring center lies in the original residual denominator. The image
of Z_lambda is therefore fixed by S and generates the full residual
section under D. This proves the published fixed-space-generation
correction to 5.12 on the descended D/O₂(D) action.

Two-perfectness of O²(L_alpha') also preserves zero residual fixed space
under this restriction and descent. The reduced F1.11 application builds
the section and all these premises on its unchanged original vectors.
The natural-case exclusion and paired square inequalities remain to be
proved; no model recognition or Chapter 8 conclusion is assumed here.

Source: DGS, Groups and Graphs (1985), proof of 8.3, pp.135–136,
and Stroth's fixed-space-generation correction to 5.12.
-/

@[expose] public noncomputable section
open Subgroup Representation Representation.BinaryOffender
open Representation.RankOne.QuadraticRecognition
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingNontrivial
open Subgroup.CosetGeometry.RankTwo Theory.GroupTheory.AmalgamGraph
universe u
variable {G : Type u} [Group G] {P : Fin 2 → Subgroup G} {B : Subgroup G}

/-- The normal residual join has the literal full-edge intersection as a
Sylow subgroup. Normality is relative to the original local group. -/
theorem source_residual_join_sylow (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (d : EarlierLocalTheorems (family P))
    {v w : Vertex (family P)} (hvw : (graph (family P)).Adj v w)
    (R : Sylow 2 (d.localGroup w))
    (hR : (R : Subgroup (d.localGroup w)).map (d.localGroup w).subtype =
      (stabilizer (family P) w ⊓ stabilizer (family P) v).pCoreIn 2) :
    let F := family P
    let E := (pResidual 2 (d.localGroup v)).map (d.localGroup v).subtype
    let D := E ⊔ Q F w
    D ≤ d.localGroup v ∧ d.localGroup v ≤ normalizer (D : Set G) ∧
    ∃ S : Sylow 2 D,
      (S : Subgroup D).map D.subtype =
        ((R : Subgroup (d.localGroup w)).map (d.localGroup w).subtype) ⊓ D := by
  let := finite_endpoints h
  let F := family P
  let L := d.localGroup v
  let E := (pResidual 2 L).map L.subtype
  let D := E ⊔ Q F w
  let X := D.subgroupOf L
  let : Finite L := Finite.of_injective (inclusion (d.local_le v)) (inclusion_injective _)
  obtain ⟨T,hT⟩ := source_edge_core_local_sylow h hB d hvw
  have hTR : (T : Subgroup L).map L.subtype =
      (R : Subgroup (d.localGroup w)).map (d.localGroup w).subtype := by
    rw [hT,hR,inf_comm (stabilizer F v)]
  have hQT : Q F w ≤ (T : Subgroup L).map L.subtype := by
    rw [hT]
    simpa only [inf_comm] using Noncommuting.graph_Q_le_edgeCore h hvw.symm
  have hQL : Q F w ≤ L := hQT.trans (map_subtype_le _)
  have hDL : D ≤ L := sup_le (map_subtype_le _) hQL
  have hTw : (T : Subgroup L).map L.subtype ≤ stabilizer F w := by
    rw [hT]
    exact (pCoreIn_le 2 _).trans inf_le_right
  have hnQ : (T : Subgroup L) ≤ normalizer (Q F w |>.subgroupOf L : Set L) := by
    apply le_normalizer_iff.mpr
    intro t ht x hx
    exact le_normalizer_iff.mp (hTw.trans (stabilizer_normalizes_Q F w)) t
      (mem_map_of_mem L.subtype ht) x hx
  have hX : X = pResidual 2 L ⊔ (Q F w).subgroupOf L := by
    dsimp only [X,D,E]
    rw [subgroupOf_sup (map_subtype_le _) hQL,subgroupOf,
      comap_map_eq_self_of_injective L.subtype_injective]
  let : X.Normal := hX ▸ pResidual_sup_normal_of_sylow_normalizes T _ hnQ
  obtain ⟨S,hS⟩ := T.exists_sylow_map_eq_inf_of_normal X
  let e : X ≃* D := subgroupOfEquivOfLe hDL
  let S' := S.mapSurjective (f := e.toMonoidHom) e.surjective
  refine ⟨hDL,(normal_subgroupOf_iff_le_normalizer hDL).mp inferInstance,S',?_⟩
  change ((S : Subgroup X).map e.toMonoidHom).map D.subtype = _
  have hf : D.subtype.comp e.toMonoidHom = L.subtype.comp X.subtype := rfl
  rw [map_map,hf,←map_map,hS,Subgroup.map_inf _ _ _ L.subtype_injective,
    map_subgroupOf_eq_of_le hDL,hTR]

private theorem residual_join_neighbor_span (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (d : EarlierLocalTheorems (family P))
    {v w : Vertex (family P)} (hvw : (graph (family P)).Adj v w)
    (hz : Z (family P) v = omegaCenterIn (d.localGroup v)) :
    conjugateSpanBy (Z (family P) w)
      ((pResidual 2 (d.localGroup v)).map (d.localGroup v).subtype ⊔ Q (family P) w) =
        V (family P) v 1 := by
  let := finite_endpoints h
  let F := family P
  let L := d.localGroup v
  let E := (pResidual 2 L).map L.subtype
  let : Finite L := Finite.of_injective (inclusion (d.local_le v)) (inclusion_injective _)
  obtain ⟨T,hT⟩ := source_edge_core_local_sylow h hB d hvw
  have hTw : (T : Subgroup L).map L.subtype ≤ stabilizer F w := by
    rw [hT]
    exact (pCoreIn_le 2 _).trans inf_le_right
  have hnE : L ≤ normalizer (E : Set G) := by
    simpa only [normalizer_eq_top,←MonoidHom.range_eq_map,range_subtype]
      using (pResidual 2 L).le_normalizer_map L.subtype
  have hQT : Q F w ≤ (T : Subgroup L).map L.subtype := by
    rw [hT]
    simpa only [inf_comm] using Noncommuting.graph_Q_le_edgeCore h hvw.symm
  have hQL : Q F w ≤ L := hQT.trans (map_subtype_le _)
  have hsupp : E ⊔ (T : Subgroup L).map L.subtype = L := by
    have hh := congrArg (map L.subtype) (pResidual_sup_sylow_eq_top T)
    simpa only [Subgroup.map_sup,←MonoidHom.range_eq_map,range_subtype] using hh
  have hspan := CommutingThreeProfile.V_eq_center_sup_neighbor_conjugates F L (d.local_le v) hvw
    (fun z hz => d.transitive v ⟨w,hvw⟩ ⟨z,hz⟩)
  have hzle : Z F v ≤ Z F w := hz.symm ▸ local_omega_le_neighbor_Z h d hvw
  rw [sup_eq_right.mpr (hzle.trans (le_conjugateSpanBy _ _))] at hspan
  have hspanE : conjugateSpanBy (Z F w) L = conjugateSpanBy (Z F w) E := by
    rw [←hsupp]
    exact conjugateSpanBy_sup_of_normalizes_seed _ _ _
      (hTw.trans (stabilizer_normalizes_Z F w)) ((map_subtype_le _).trans hnE)
  rw [conjugateSpanBy_sup_of_normalizes_seed _ _ _
    ((Q_le_stabilizer F w).trans (stabilizer_normalizes_Z F w)) (hQL.trans hnE),
    ←hspanE,←hspan]

private theorem residual_fixed_restriction (L D : Subgroup G) [Finite L]
    (hDL : D ≤ L) (hED : (pResidual 2 L).map L.subtype ≤ D)
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    (ρ : Representation (ZMod 2) L W)
    (σ : Representation (ZMod 2) (D ⧸ pCore 2 D) W)
    (hσ : ∀ g : D, σ (QuotientGroup.mk' (pCore 2 D) g) = ρ (inclusion hDL g))
    (hr : fixedSpace ρ (pResidual 2 L) = ⊥) :
    fixedSpace σ (pResidual 2 (D ⧸ pCore 2 D)) = ⊥ := by
  let q := QuotientGroup.mk' (pCore 2 D)
  let f : pResidual 2 L →* D :=
    (L.subtype.comp (pResidual 2 L).subtype).codRestrict D
      (fun r => hED (mem_map_of_mem L.subtype r.property))
  have hf := map_pResidual_le 2 f
  rw [(pResidual_eq_top_iff 2 (pResidual 2 L)).mpr (isPPerfect_pResidual 2)] at hf
  apply bot_unique
  intro z hz
  apply hr.le
  intro r
  have hrD : f r ∈ pResidual 2 D := hf (mem_map_of_mem f (mem_top r))
  have hq : q (f r) ∈ pResidual 2 (D ⧸ pCore 2 D) :=
    map_pResidual_le 2 q (mem_map_of_mem q hrD)
  have hh := hz ⟨q (f r),hq⟩
  change σ (q (f r)) z = z at hh
  rw [hσ] at hh
  exact hh

/-- The residual-join quotient satisfies the corrected Sylow-fixed generation
condition on the whole original residual section. The Sylow is constructed
as the literal intersection with the full edge Sylow. -/
theorem source_counterexample_residual_prepared (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (d : EarlierLocalTheorems (family P))
    {a beta a' : Vertex (family P)} (hc : IsCriticalPair (family P) a a')
    (hab : (graph (family P)).Adj a beta)
    (hd : (graph (family P)).dist beta a' + 1 = b (family P))
    (hb : 1 < b (family P)) (hcomm : ⁅Z (family P) a,Z (family P) a'⁆ = ⊥)
    (models : ∀ v : Vertex (family P), IsRankOneModel (d.localGroup v ⧸ pCore 2 (d.localGroup v)))
    (w : (graph (family P)).neighborSet a')
    (hm : ⁅V (family P) beta 1 ⊓ Q (family P) a',Z (family P) w.val⁆ ≠ ⊥)
    (hescape : ¬ Q (family P) w.val ≤ Q (family P) a')
    (R : Sylow 2 (d.localGroup w.val))
    (hR : (R : Subgroup (d.localGroup w.val)).map (d.localGroup w.val).subtype =
      (stabilizer (family P) w.val ⊓ stabilizer (family P) a').pCoreIn 2)
    (hbad : ¬ ⁅quotientSylowOmegaPreimage (d.localGroup w.val) R,Z (family P) w.val⁆ ≤
      ⁅V (family P) beta 1 ⊓ Q (family P) a',V (family P) a' 1⁆)
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    (ρ : Representation (ZMod 2) (d.localGroup a') W)
    (c : BinaryConjugationSection (d.localGroup a') (V (family P) a' 1)
      (V (family P) a' 1 ⊓ centralizer
        ((pResidual 2 (d.localGroup a')).map (d.localGroup a').subtype : Set G)) ρ)
    (hr : fixedSpace ρ (pResidual 2 (d.localGroup a')) = ⊥) :
    let F := family P
    let L := d.localGroup a'
    let E := (pResidual 2 L).map L.subtype
    let D := E ⊔ Q F w.val
    ∃ (hDL : D ≤ L) (σ : Representation (ZMod 2) (D ⧸ pCore 2 D) W) (S : Sylow 2 D),
      (∀ g : D, σ (QuotientGroup.mk' (pCore 2 D) g) = ρ (inclusion hDL g)) ∧
      (S : Subgroup D).map D.subtype = quotientSylowOmegaPreimage (d.localGroup w.val) R ∧
      GeneratedByFixedSpace σ ((S : Subgroup D).map (QuotientGroup.mk' (pCore 2 D))) ∧
      fixedSpace σ (pResidual 2 (D ⧸ pCore 2 D)) = ⊥ ∧
      ∃ cD : BinaryConjugationSection D (V F a' 1)
        (V F a' 1 ⊓ centralizer (E : Set G))
        (σ.comp (QuotientGroup.mk' (pCore 2 D))), cD.coordinates = c.coordinates := by
  let := finite_endpoints h
  let F := family P
  let L := d.localGroup a'
  let E := (pResidual 2 L).map L.subtype
  let D := E ⊔ Q F w.val
  let q := QuotientGroup.mk' (pCore 2 D)
  let : Finite L := Finite.of_injective (inclusion (d.local_le a')) (inclusion_injective _)
  obtain ⟨hDL,σ,hσ,cD,hcD⟩ := source_counterexample_residual_quotient_action h hB d hc hab hd hb
    hcomm models w hm hescape R hR hbad ρ c
  obtain ⟨_,_,S,hS⟩ := source_residual_join_sylow h hB d w.property R hR
  have hY := source_counterexample_residual_edge_eq_omega h hB d hc hab hd hb hcomm
    models w hm hescape R hR hbad
  have hSY : (S : Subgroup D).map D.subtype = quotientSylowOmegaPreimage (d.localGroup w.val) R :=
    hS.trans hY
  have hmove := source_omega_displacement_residual_fixed h hB d hc hab hd hb hcomm models w hm hescape R hR
  have hmove' : ⁅(S : Subgroup D).map D.subtype,Z F w.val⁆ ≤
      V F a' 1 ⊓ centralizer (E : Set G) := by
    rw [hSY]
    exact hmove.trans (inf_le_inf_right _ (Z_neighbor_le_V F w.property))
  have hz := critical_end_center_of_commuting F h.generate
    (fun v => (source_Z_Q_U h v).1) (fun v => (source_Z_Q_U h v).2) hc hcomm
    L (d.sylow_or_center a')
  have hspan := residual_join_neighbor_span h hB d w.property hz
  let U := BinaryConjugationSection.fixedConjugateSpan σ ((S : Subgroup D).map q)
  let U' : Subrepresentation (σ.comp q) :=
    ⟨U.toSubmodule,fun g _ hv => U.apply_mem_toSubmodule (q g) hv⟩
  have hgen : GeneratedByFixedSpace σ ((S : Subgroup D).map q) := by
    apply cD.generated_image_le (Z F w.val) hspan.symm U'
    intro z hz
    apply BinaryConjugationSection.fixedSpace_le_fixedConjugateSpan σ ((S : Subgroup D).map q)
    intro s
    obtain ⟨g,hg,he⟩ := s.property
    change σ s.val z = z
    rw [←he]
    exact cD.fixed_on_imageSpace_of_commutator_le _ _ hmove' g (mem_map_of_mem D.subtype hg) z hz
  exact ⟨hDL,σ,S,hσ,hSY,hgen,
    residual_fixed_restriction L D hDL le_sup_left ρ σ hσ hr,cD,hcD⟩

open Representation.NormalElementaryQuotient CommutingTrivial
variable {J : Fin 2 → Subgroup G} {S₀ : Subgroup G}

/-- Corrected fixed-space generation for the actual full reduced residual
section, with its original coordinate map and the literal intersection Sylow.
Both the section and its vanishing residual fixed space are constructed from
the source configuration, so neither is an extra assembly premise. -/
theorem reduced_counterexample_residual_prepared
    (h : HypothesisF11 J S₀)
    (hob : ∀ v w : Vertex (Reduction.reducedFamily J S₀),
      (graph (Reduction.reducedFamily J S₀)).Adj v w →
      ¬ stabilizer (Reduction.reducedFamily J S₀) v ≤ normalizer
        ((Q (Reduction.reducedFamily J S₀) w ⊓ Q (Reduction.reducedFamily J S₀) v :
          Subgroup (Reduction.G₀ J S₀)) : Set (Reduction.G₀ J S₀)))
    (models : ∀ v : Vertex (Reduction.reducedFamily J S₀),
      IsRankOneModel (graphLocalGroup (Reduction.reducedFamily J S₀) v ⧸
        pCore 2 (graphLocalGroup (Reduction.reducedFamily J S₀) v)))
    {a beta a' : Vertex (Reduction.reducedFamily J S₀)}
    (hc : IsCriticalPair (Reduction.reducedFamily J S₀) a a')
    (hab : (graph (Reduction.reducedFamily J S₀)).Adj a beta)
    (hd : (graph (Reduction.reducedFamily J S₀)).dist beta a' + 1 = b (Reduction.reducedFamily J S₀))
    (hb : 1 < b (Reduction.reducedFamily J S₀))
    (hcomm : ⁅Z (Reduction.reducedFamily J S₀) a,Z (Reduction.reducedFamily J S₀) a'⁆ = ⊥)
    (w : (graph (Reduction.reducedFamily J S₀)).neighborSet a')
    (hm : ⁅V (Reduction.reducedFamily J S₀) beta 1 ⊓ Q (Reduction.reducedFamily J S₀) a',
      Z (Reduction.reducedFamily J S₀) w.val⁆ ≠ ⊥)
    (R : Sylow 2 (graphLocalGroup (Reduction.reducedFamily J S₀) w.val))
    (hR : (R : Subgroup (graphLocalGroup (Reduction.reducedFamily J S₀) w.val)).map
      (graphLocalGroup (Reduction.reducedFamily J S₀) w.val).subtype =
        (stabilizer (Reduction.reducedFamily J S₀) w.val ⊓ stabilizer (Reduction.reducedFamily J S₀) a').pCoreIn 2)
    (hbad : ¬ ⁅quotientSylowOmegaPreimage (graphLocalGroup (Reduction.reducedFamily J S₀) w.val) R,
      Z (Reduction.reducedFamily J S₀) w.val⁆ ≤
        ⁅V (Reduction.reducedFamily J S₀) beta 1 ⊓ Q (Reduction.reducedFamily J S₀) a',
          V (Reduction.reducedFamily J S₀) a' 1⁆) :
    let F := Reduction.reducedFamily J S₀
    let L := graphLocalGroup F a'
    let U := (V F a' 1).subgroupOf L
    let E := (pResidual 2 L).map L.subtype
    let D := E ⊔ Q F w.val
    letI : ∀ i, Finite (F i) := finite_endpoints (Reduction.reduced_triple h)
    letI := neighborhoodIn_normal F a' L (sylowGenerated_le _)
    ∃ hb2 : 2 < b F,
      letI := neighborhoodIn_elementary F (Reduction.reduced_triple h).generate
        (fun v => (source_Z_Q_U (Reduction.reduced_triple h) v).1)
        (Reduction.reduced_kernel_sylow h) a' hb2 L
      Nontrivial (FixedQuotient U (pResidual 2 L)) ∧
      ∃ (hDL : D ≤ L)
        (σ : Representation (ZMod 2) (D ⧸ pCore 2 D) (FixedQuotient U (pResidual 2 L)))
        (S : Sylow 2 D),
        (∀ g : D, σ (QuotientGroup.mk' (pCore 2 D) g) =
          fixedQuotientAction U (pResidual 2 L) (inclusion hDL g)) ∧
        (S : Subgroup D).map D.subtype = quotientSylowOmegaPreimage (graphLocalGroup F w.val) R ∧
        GeneratedByFixedSpace σ ((S : Subgroup D).map (QuotientGroup.mk' (pCore 2 D))) ∧
        fixedSpace σ (pResidual 2 (D ⧸ pCore 2 D)) = ⊥ ∧
        Nonempty (BinaryConjugationSection D (V F a' 1)
          (V F a' 1 ⊓ centralizer (E : Set (Reduction.G₀ J S₀)))
          (σ.comp (QuotientGroup.mk' (pCore 2 D)))) := by
  let ht := Reduction.reduced_triple h
  let F := Reduction.reducedFamily J S₀
  let L := graphLocalGroup F a'
  let U := (V F a' 1).subgroupOf L
  let d := Reduction.reducedEarlierLocalTheorems h hob
  let : ∀ i, Finite (F i) := finite_endpoints ht
  let : U.Normal := neighborhoodIn_normal F a' L (sylowGenerated_le _)
  obtain ⟨hb2,hn,⟨c⟩,hr,_,_,_⟩ := reduced_ending_residual_actor h hob models hc hab hd hb hcomm w
  refine ⟨hb2,hn,?_⟩
  let : IsElementaryAbelian 2 U := neighborhoodIn_elementary F ht.generate
    (fun v => (source_Z_Q_U ht v).1) (Reduction.reduced_kernel_sylow h) a' hb2 L
  have hescape := core_escape_of_intersection_obstruction F (hob w.val a' w.property.symm)
  obtain ⟨hDL,σ,S,hσ,hS,hgen,hres,cD,_⟩ := source_counterexample_residual_prepared ht
    (Reduction.reduced_borel_core_sylow h) d hc hab hd hb hcomm models w hm hescape R hR hbad
    (fixedQuotientAction U (pResidual 2 L)) c hr
  exact ⟨hDL,σ,S,hσ,hS,hgen,hres,⟨cD⟩⟩

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingNontrivial
