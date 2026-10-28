module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingNontrivial.ResidualRoot
public import Theory.GroupTheory.PResidual.SylowJoin
public import Theory.GroupTheory.SylowNormalRestriction

/-!
# The residual intersection equals the quotient omega preimage

Let E = O²(L_alpha') and T be the full moving-edge Sylow. If
T ∩ E Q_lambda lay in Q_lambda, normality of E Q_lambda in L_alpha'
would make Q_lambda Sylow in its local conjugate span. The original 6.5
obstruction rules this out. In the counterexample branch of 8.3 the
already proved upper inclusion puts its nonzero quotient image in the
omega-center. Fusion under the actual Sylow normalizer makes that image
the entire omega-center. Kernel containment then gives equality before
passing to the quotient.

Source: DGS, Groups and Graphs (1985), proof of 8.3, pp.135–136.
This supplies the quotient identity used in `ResidualDescent`; the
naturality exclusion and paired square estimates remain separate steps.
-/

@[expose] public noncomputable section
open Subgroup Representation
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingNontrivial
open Subgroup.CosetGeometry.RankTwo Theory.GroupTheory.AmalgamGraph
universe u
variable {G : Type u} [Group G]

private theorem sylow_in_span_of_residual_intersection
    (L A : Subgroup G) [Finite L] (R : Sylow 2 L)
    (hA : A ≤ (R : Subgroup L).map L.subtype)
    (hn : (R : Subgroup L).map L.subtype ≤ normalizer (A : Set G))
    (hi : ((R : Subgroup L).map L.subtype) ⊓
      ((pResidual 2 L).map L.subtype ⊔ A) ≤ A) :
    ∃ S : Sylow 2 (conjugateSpanBy A L),
      (S : Subgroup (conjugateSpanBy A L)).map (conjugateSpanBy A L).subtype = A := by
  let W := conjugateSpanBy A L
  let X := W.subgroupOf L
  let D := pResidual 2 L ⊔ A.subgroupOf L
  have hAL : A ≤ L := hA.trans (map_subtype_le _)
  have hWL : W ≤ L := conjugateSpanBy_le hAL L.le_normalizer
  have hnA : (R : Subgroup L) ≤ normalizer (A.subgroupOf L : Set L) := by
    apply le_normalizer_iff.mpr
    intro r hr a ha
    exact le_normalizer_iff.mp hn r (mem_map_of_mem L.subtype hr) a ha
  let : D.Normal := pResidual_sup_normal_of_sylow_normalizes R (A.subgroupOf L) hnA
  have hDmap : D.map L.subtype = (pResidual 2 L).map L.subtype ⊔ A := by
    rw [Subgroup.map_sup,map_subgroupOf_eq_of_le hAL]
  have hWD : W ≤ D.map L.subtype := conjugateSpanBy_le
    (hDmap.symm ▸ (show A ≤ (pResidual 2 L).map L.subtype ⊔ A from le_sup_right))
    (by simpa only [normalizer_eq_top,←MonoidHom.range_eq_map, range_subtype] using D.le_normalizer_map L.subtype)
  let : X.Normal := normal_subgroupOf_of_le_normalizer (le_normalizer_conjugateSpanBy A L)
  obtain ⟨S,hS⟩ := R.exists_sylow_map_eq_inf_of_normal X
  let e : X ≃* W := subgroupOfEquivOfLe hWL
  let S' := S.mapSurjective (f := e.toMonoidHom) e.surjective
  refine ⟨S',?_⟩
  have hf : W.subtype.comp e.toMonoidHom = L.subtype.comp X.subtype := rfl
  change ((S : Subgroup X).map e.toMonoidHom).map W.subtype = A
  rw [map_map,hf,←map_map,hS,Subgroup.map_inf _ _ _ L.subtype_injective,map_subgroupOf_eq_of_le hWL]
  exact le_antisymm ((inf_le_inf_left _ hWD).trans (by simpa only [hDmap] using hi))
    (le_inf hA (le_conjugateSpanBy A L))

variable {P : Fin 2 → Subgroup G} {B : Subgroup G}

/-- The original 6.5 obstruction makes the residual intersection larger than
its moving-vertex core. -/
theorem source_residual_edge_not_le_core (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (d : EarlierLocalTheorems (family P))
    {v w : Vertex (family P)} (hvw : (graph (family P)).Adj v w)
    (R : Sylow 2 (d.localGroup w))
    (hR : (R : Subgroup (d.localGroup w)).map (d.localGroup w).subtype =
      (stabilizer (family P) w ⊓ stabilizer (family P) v).pCoreIn 2) :
    ¬ ((R : Subgroup (d.localGroup w)).map (d.localGroup w).subtype) ⊓
      ((pResidual 2 (d.localGroup v)).map (d.localGroup v).subtype ⊔ Q (family P) w) ≤
        Q (family P) w := by
  let := finite_endpoints h
  let F := family P
  let L := d.localGroup v
  let : Finite L := Finite.of_injective (inclusion (d.local_le v)) (inclusion_injective _)
  obtain ⟨S,hS⟩ := source_edge_core_local_sylow h hB d hvw
  have hST : (S : Subgroup L).map L.subtype = (R : Subgroup (d.localGroup w)).map (d.localGroup w).subtype := by
    rw [hS,hR,inf_comm (stabilizer F v)]
  intro hi
  apply d.core_span_obstruction v w hvw
  apply sylow_in_span_of_residual_intersection L (Q F w) S
  · rw [hS]
    simpa only [inf_comm] using Noncommuting.graph_Q_le_edgeCore h hvw.symm
  · rw [hS]
    exact ((pCoreIn_le 2 (stabilizer F v ⊓ stabilizer F w)).trans inf_le_right).trans
      (stabilizer_normalizes_Q F w)
  · rwa [hST]

/-- In the counterexample branch of 8.3, the residual intersection is
exactly the preimage of the moving Sylow omega-center. The lower inclusion
uses the original adjacent-core Sylow obstruction and normalizer fusion. -/
theorem source_counterexample_residual_edge_eq_omega (h : LocallyRankOneTriple P B)
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
      ⁅V (family P) beta 1 ⊓ Q (family P) a',V (family P) a' 1⁆) :
    ((R : Subgroup (d.localGroup w.val)).map (d.localGroup w.val).subtype) ⊓
      ((pResidual 2 (d.localGroup a')).map (d.localGroup a').subtype ⊔ Q (family P) w.val) =
      quotientSylowOmegaPreimage (d.localGroup w.val) R := by
  let := finite_endpoints h
  let F := family P
  let L := d.localGroup w.val
  let T := (R : Subgroup L).map L.subtype
  let E := (pResidual 2 (d.localGroup a')).map (d.localGroup a').subtype
  let D := E ⊔ Q F w.val
  let T₀ := T ⊓ D
  let N := (normalizer (R : Set L)).map L.subtype
  let X := T₀.subgroupOf L
  let q := QuotientGroup.mk' (pCore 2 L)
  let : Finite L := Finite.of_injective (inclusion (d.local_le w.val)) (inclusion_injective _)
  let S := R.mapSurjective (f := q) (QuotientGroup.mk'_surjective _)
  let A := X.map q
  have hNend : N ≤ stabilizer F a' := by
    have he := (source_edge_local_normalizer h d w.property.symm (models w.val) R hR).2
    rintro _ ⟨l,hl,rfl⟩
    have hl' : l ∈ (stabilizer F a').subgroupOf L := he.symm ▸ hl
    exact hl'
  have hNL : N ≤ normalizer (d.localGroup a' : Set G) := by
    intro g hg
    apply mem_normalizer_iff_map_conj_eq.mpr
    exact (d.conjugate g a').symm.trans (congrArg d.localGroup (hNend hg))
  have hNE : N ≤ normalizer (E : Set G) :=
    hNL.trans (normalizer_le_normalizer_characteristic_image (d.localGroup a') (pResidual 2 (d.localGroup a')))
  have hNQ : N ≤ normalizer (Q F w.val : Set G) := by
    intro g hg
    apply mem_normalizer_iff_map_conj_eq.mpr
    exact (Q_translate F g w.val).symm.trans
      (congrArg (Q F) (((map_subtype_le _).trans (d.local_le w.val)) hg))
  have hNT : N ≤ normalizer (T : Set G) := (R : Subgroup L).le_normalizer_map L.subtype
  have hNX : N ≤ normalizer (T₀ : Set G) :=
    (le_inf hNT ((le_inf hNE hNQ).trans (normalizer_inf_normalizer_le_normalizer_sup E (Q F w.val)))).trans
      inf_normalizer_le_normalizer_inf
  have hXS : X ≤ R := by
    intro x hx
    obtain ⟨y,hy,he⟩ := hx.1
    exact (Subtype.ext he : y=x) ▸ hy
  have hnX : normalizer (R : Set L) ≤ normalizer (X : Set L) := by
    apply le_normalizer_iff.mpr
    intro g hg x hx
    exact le_normalizer_iff.mp hNX g (mem_map_of_mem L.subtype hg) x hx
  have hnA : normalizer (S : Set (L ⧸ pCore 2 L)) ≤ normalizer (A : Set _) := by
    change normalizer ((R : Subgroup L).map q : Set (L ⧸ pCore 2 L)) ≤ _
    rw [←R.normalizer_map_surjective q (QuotientGroup.mk'_surjective _)]
    exact (map_mono hnX).trans (X.le_normalizer_map q)
  have hle : T₀ ≤ quotientSylowOmegaPreimage L R :=
    source_counterexample_residual_edge_le_omega h hB d hc hab hd hb hcomm models w hm hescape R hR hbad
  have hAO : A ≤ omegaCenterIn (S : Subgroup (L ⧸ pCore 2 L)) := by
    have hh := map_mono (f := q) (comap_mono (f := L.subtype) hle)
    change A ≤ ((quotientSylowOmegaPreimage L R).subgroupOf L).map
      (QuotientGroup.mk' (pCore 2 L)) at hh
    rw [quotientSylowOmegaPreimage_image L R] at hh
    exact hh
  have hne : A ≠ ⊥ := by
    intro he
    have hk := (Subgroup.map_eq_bot_iff _).mp he
    rw [QuotientGroup.ker_mk'] at hk
    apply source_residual_edge_not_le_core h hB d w.property R hR
    intro x hx
    have hXL : T₀ ≤ L := inf_le_left.trans (map_subtype_le _)
    rw [←localGroup_core_eq F d w.val]
    exact ⟨⟨x,hXL hx⟩,hk (show (⟨x,hXL hx⟩ : L) ∈ X from hx),rfl⟩
  let : IsElementaryAbelian 2 A := IsElementaryAbelian.of_le hAO
  have heq : A = omegaCenterIn (S : Subgroup (L ⧸ pCore 2 L)) := by
    refine le_antisymm hAO ?_
    rw [←source_rank_one_omega_generated (models w.val) S A (map_mono hXS) hne]
    exact conjugateSpanBy_le le_rfl hnA
  have hQT : Q F w.val ≤ T := by
    rw [←localGroup_core_eq F d w.val]
    exact map_mono (pCore_isPGroup.le_sylow_of_normal R)
  have hkX : q.ker ≤ X := by
    rw [QuotientGroup.ker_mk']
    intro x hx
    have hxQ : (x : G) ∈ Q F w.val := by
      rw [←localGroup_core_eq F d w.val]
      exact mem_map_of_mem L.subtype hx
    exact ⟨hQT hxQ,(show Q F w.val ≤ D from le_sup_right) hxQ⟩
  change T₀ = ((omegaCenterIn (S : Subgroup (L ⧸ pCore 2 L))).comap q).map L.subtype
  rw [←heq,comap_map_eq_self hkX,map_subgroupOf_eq_of_le
    (show T₀ ≤ L from inf_le_left.trans (map_subtype_le _))]


end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingNontrivial
