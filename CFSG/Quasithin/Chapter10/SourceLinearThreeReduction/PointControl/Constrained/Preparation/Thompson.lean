module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Constrained.Action
public import Theory.GroupTheory.ElementaryThompsonQuasisimpleCore

/-!
# Thompson movement without full moved-span inclusion

Suppose J(C_T(v))=J(T) centralizes the literal reduced orbit VI. The
normal component L in L C_T(v) has a quasisimple two-core quotient.
The Thompson commutator theorem makes L normalize J(T), since otherwise
L=[L,J(T)] would centralize VI, contrary to its nonzero action image.
Thus L₀T normalizes J(T), and source uniqueness controls N_G(J(T)).
Thompson Frattini factorization in I C_T(v) then puts I in M.

This argument also covers the fixed-layer orbit: it never requires
[D.fullModule,L]≤VI. The ambient centralizer bound and Thompson equality
remain explicit geometric inputs, discharged in the linear-five consumer.
Source: Aschbacher--Smith, 10.2.9, printed p.751.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter10.PointControl.Constrained
open Chapter3.Section02 ChapterB.InternalThompsonAction
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L} {t v : G} {I : Subgroup G}

private theorem component_normalizes_thompson (c : Context D t v I)
    (hc : centralizer (orbitModule D v I : Set G) ≤ D.maximalLocal)
    (he : elementaryAbelianMaxJ (pointSylow T v) = elementaryAbelianMaxJ (T : Subgroup G))
    (hm : elementaryAbelianMaxJ (pointSylow T v) ≤ centralizer (orbitModule D v I : Set G)) :
    L ≤ normalizer (elementaryAbelianMaxJ (T : Subgroup G) : Set G) := by
  let S := pointSylow T v
  let B := L ⊔ S
  let A := L.subgroupOf B
  have hLB : L ≤ B := le_sup_left
  have hBX : B ≤ centralizer ({v} : Set G) :=
    sup_le (c.escaping.strict.le.trans c.escaping.le_centralizer) inf_le_right
  obtain ⟨P,hP⟩ := c.escaping.sylow.restrict (show S ≤ B from le_sup_right) hBX
  have hP' : (P : Subgroup B) = S.subgroupOf B := by
    apply map_injective B.subtype_injective
    rw [hP,map_subgroupOf_eq_of_le le_sup_right]
  have hA : A.IsCComponent := D.maximal.1.1.subgroupOf_of_le le_sup_left
    (sup_le le_sup_left (inf_le_left.trans le_sup_right))
  let : A.Normal := normal_subgroupOf_of_le_normalizer
    (sup_le L.le_normalizer c.escaping.sylow_normalizes)
  let e : A ≃* L := subgroupOfEquivOfLe hLB
  let eq := QuotientGroup.congr (pCore 2 A) (pCore 2 L) e (pCore_map_iso 2 e)
  let := D.quasisimple
  let : IsQuasisimple (A ⧸ pCore 2 A) := IsQuasisimple.of_mulEquiv eq.symm
  have hgen : A ⊔ (P : Subgroup B) = ⊤ := by
    rw [hP',←subgroupOf_sup le_sup_left le_sup_right,subgroupOf_self]
  have hjmap : (elementaryAbelianMaxJ (P : Subgroup B)).map B.subtype =
      elementaryAbelianMaxJ (T : Subgroup G) := by
    rw [←elementaryAbelianMaxJ_map_injective B.subtype B.subtype_injective,hP]
    exact he
  by_contra hn
  have hn' : ¬ A ≤ normalizer (elementaryAbelianMaxJ (P : Subgroup B) : Set B) := by
    intro h
    apply hn
    rw [←map_subgroupOf_eq_of_le hLB]
    exact (map_mono h).trans (by rw [←hjmap]; exact le_normalizer_map B.subtype)
  have hcomm := eq_commutator_maxJ_of_quasisimple_core_of_not_normalizes P A hA hgen hn'
  have hcomm' := congrArg (Subgroup.map B.subtype) hcomm
  rw [map_commutator,map_subgroupOf_eq_of_le hLB,hjmap] at hcomm'
  have hLC : L ≤ centralizer (orbitModule D v I : Set G) := by
    apply hcomm'.le.trans
    apply (commutator_mono le_rfl (he ▸ hm)).trans
    apply le_normalizer_iff_commutator_le_right.mp
    exact (c.escaping.strict.le.trans (le_normalizer_conjugateSpanBy _ I)).trans
      (normalizer_le_normalizer_centralizer _)
  let H := pointJoin T v I
  let := c.reduced.normal
  apply (c.small_image_strict hc).1
  apply (Subgroup.map_eq_bot_iff _).mpr
  rw [QuotientGroup.ker_mk']
  intro l hl w hw
  exact Subtype.ext (hLC hl w hw)

/-- The actual point Thompson subgroup moves VI once its ambient centralizer
and equality with J(T) are known, including the exceptional fixed-layer case. -/
theorem Context.thompson_moves_of_centralizer_of_eq (c : Context D t v I)
    (hc : centralizer (orbitModule D v I : Set G) ≤ D.maximalLocal)
    (he : elementaryAbelianMaxJ (pointSylow T v) = elementaryAbelianMaxJ (T : Subgroup G)) :
    ¬ elementaryAbelianMaxJ (pointSylow T v) ≤ centralizer (orbitModule D v I : Set G) := by
  intro hm
  let J := elementaryAbelianMaxJ (T : Subgroup G)
  have hTN : (T : Subgroup G) ≤ normalizer (J : Set G) :=
    (T : Subgroup G).le_normalizer.trans (normalizer_le_normalizer_elementaryAbelianMaxJ _)
  have hLN := component_normalizes_thompson c hc he hm
  have hJN : localJoin T L ≤ normalizer (J : Set G) := by
    apply sup_le ?_ hTN
    exact iSup_conjugates_le_of_le_normalizer L T _ hLN
      (hTN.trans (normalizer (J : Set G)).le_normalizer)
  have hu := Chapter1.Section02.nonsolvable_uniqueness_of_theoremsAC
    (fun _ _ _ => ChapterA.Section02.theoremA_knownSimple)
    (fun _ _ _ => ChapterA.Section02.theoremC_knownSimple) D.simpleQTKE T D.maximal
  have hJT : J ≤ (T : Subgroup G) := sSup_le fun _ hA => hA.1
  have hT : (T : Subgroup G) ≠ ⊥ := fun hz =>
    D.module_ne_bot (bot_unique (D.module_le_sylow.trans_eq hz))
  have hN : normalizer (J : Set G) ≤ D.maximalLocal :=
    normalizer_le_of_unique_maximalTwoLocal (D.lemma_3_2_3_uniqueness hu).2.2
      (T.isPGroup'.to_le hJT) (elementaryAbelianMaxJ_ne_bot_of_finite_pGroup _ T.isPGroup' hT) hJN
  let H := pointJoin T v I
  let U := internalModule D v I
  obtain ⟨P,hP⟩ := c.join_sylow
  have hjmap : (elementaryAbelianMaxJ (P : Subgroup H)).map H.subtype = J := by
    rw [←elementaryAbelianMaxJ_map_injective H.subtype H.subtype_injective,hP]
    exact he
  let : U.Normal := c.reduced.normal
  have hm' : elementaryAbelianMaxJ (P : Subgroup H) ≤ centralizer (U : Set H) := by
    intro a ha w hw
    apply Subtype.ext
    have haT : (a : G) ∈ elementaryAbelianMaxJ (T : Subgroup G) := by
      change (a : G) ∈ J
      rw [←hjmap]
      exact mem_map_of_mem H.subtype ha
    exact hm (he.symm ▸ haT) w hw
  have hf := congrArg (Subgroup.map H.subtype) (thompson_frattini P U hm')
  rw [Subgroup.map_sup,←MonoidHom.range_eq_map,range_subtype] at hf
  apply c.escaping.escapes
  apply (show I ≤ H from le_sup_left).trans
  rw [←hf]
  refine sup_le ((le_normalizer_map H.subtype).trans (by rw [hjmap]; exact hN)) ?_
  rintro _ ⟨a,ha,rfl⟩
  apply hc
  intro w hw
  exact congrArg H.subtype (ha ⟨w,c.orbit_le_join hw⟩ hw)

/-- Thompson movement is discharged from the two geometric preparation inputs. -/
theorem Context.prepared_of_centralizer_of_thompson_eq (c : Context D t v I)
    (hc : centralizer (orbitModule D v I : Set G) ≤ D.maximalLocal)
    (he : elementaryAbelianMaxJ (pointSylow T v) = elementaryAbelianMaxJ (T : Subgroup G)) :
    Prepared D v I := ⟨hc,he,c.thompson_moves_of_centralizer_of_eq hc he⟩

/-- Apply the full literal quotient-action theorem with movement proved here. -/
theorem Context.actionFacts_of_centralizer_of_thompson_eq (c : Context D t v I)
    (hc : centralizer (orbitModule D v I : Set G) ≤ D.maximalLocal)
    (he : elementaryAbelianMaxJ (pointSylow T v) = elementaryAbelianMaxJ (T : Subgroup G)) :
    ActionFacts c := c.actionFacts (c.prepared_of_centralizer_of_thompson_eq hc he)

end CFSG.Quasithin.Chapter10.PointControl.Constrained
