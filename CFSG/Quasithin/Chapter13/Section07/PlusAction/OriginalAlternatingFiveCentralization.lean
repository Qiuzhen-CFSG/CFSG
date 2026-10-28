module
public import CFSG.Quasithin.Chapter13.Section07.PlusAction.OriginalAlternatingFiveRadical
public import CFSG.Quasithin.Chapter13.Section07.PlusAction.OriginalAlternatingFiveWitness
public import CFSG.Quasithin.Chapter13.Section07.PlusAction.MarkedAlternatingFiveThompson
public import CFSG.Quasithin.Chapter6.Section01.SourceModelKernel
public import Theory.GroupTheory.NormalModuleCore

/-!
# The original A5 plus-kernel component is centralized by the point residual

If the point residual acts nontrivially on the component quotient, the original
point radical is the product of its component Sylow subgroup and the two-core
of their join. A genuine alternating A5 constituent lies in the point radical.
The factorization gives inner action on that constituent, so its Thompson
subgroup centralizes the constituent. Its detecting centralizer is the join's
two-core. B.2.3(5) now makes the Baumann subgroup normal in the join, contradicting
the source local-escape theorem and the original Baumann normalizer bound.

This removes the component/point-residual centralization premise. The genuine
earlier 13.3.2(3) constituent classification and Baumann bound remain explicit.
Source: Aschbacher–Smith 13.7.4(1), printed p.937, using B.4.2 and B.2.3(5).
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section07.PlusAction.Original
open Chapter12.Section02
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ H : Subgroup G}

/-- The radical factorization places every point-radical action inside the
component action on any original chosen module. -/
theorem chosen_inner_action_of_point_factor
    (h : (ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    {K I : Subgroup G}
    (hKn : H ≤ normalizer (K : Set G)) (chosen : ChosenModule T K I)
    (hfactor : let F := ConjugateIntersections.sourceSetup T L V V₃ V₁ H
      let R := (F.L₁ ⊔ (T : Subgroup G)).pCoreIn 2
      R ≤ K ⊔ (K ⊔ R).pCoreIn 2) :
    let F := ConjugateIntersections.sourceSetup T L V V₃ V₁ H
    let R := (F.L₁ ⊔ (T : Subgroup G)).pCoreIn 2
    (K ⊔ R).pCoreIn 2 ≤ centralizer (I : Set G) ∧
      R ≤ normalizer (I : Set G) ∧
      ∀ r : R, ∃ k : K, ∀ v : I,
        (r : G) * (v : G) * (r : G)⁻¹ = (k : G) * (v : G) * (k : G)⁻¹ := by
  let F := ConjugateIntersections.sourceSetup T L V V₃ V₁ H
  let P := F.L₁ ⊔ (T : Subgroup G)
  let R := P.pCoreIn 2
  let X := K ⊔ R
  let KT := K ⊔ (T : Subgroup G)
  have hRT : R ≤ (T : Subgroup G) := by
    have hh := pCoreIn_le_sylow P (T.subtype (show (T : Subgroup G) ≤ P from le_sup_right))
    simpa only [Sylow.coe_subtype,map_subgroupOf_eq_of_le (show (T : Subgroup G) ≤ P from le_sup_right)] using hh
  have hTK : (T : Subgroup G) ≤ normalizer (K : Set G) := h.T_le_H.trans hKn
  have hTR : (T : Subgroup G) ≤ normalizer (R : Set G) :=
    (show (T : Subgroup G) ≤ P from le_sup_right).trans
      (P.le_normalizer.trans (normalizer_le_normalizer_characteristic_image P (pCore 2 P)))
  have hNX : KT ≤ normalizer (X : Set G) := sup_le
    ((show K ≤ X from le_sup_left).trans X.le_normalizer)
    ((le_inf hTK hTR).trans (normalizer_inf_normalizer_le_normalizer_sup K R))
  have hQ : X.pCoreIn 2 ≤ centralizer (I : Set G) :=
    (pCoreIn_mono_of_normalizes (sup_le le_sup_left (hRT.trans le_sup_right)) hNX).trans
      chosen.core_centralizes
  have hRI : R ≤ normalizer (I : Set G) := hfactor.trans
    (sup_le chosen.normalizes (hQ.trans (Subgroup.centralizer_le_normalizer _)))
  refine ⟨hQ,hRI,?_⟩
  intro r
  let KX := K.subgroupOf X
  have hmap : (KX ⊔ pCore 2 X).map X.subtype = K ⊔ X.pCoreIn 2 := by
    rw [Subgroup.map_sup,map_subgroupOf_eq_of_le (show K ≤ X from le_sup_left)]
    rfl
  have hr : (⟨r,show (r : G) ∈ X from mem_sup_right r.property⟩ : X) ∈ KX ⊔ pCore 2 X := by
    have hh := hfactor r.property
    rw [←hmap] at hh
    obtain ⟨x,hx,he⟩ := hh
    exact (show x = ⟨r,mem_sup_right r.property⟩ from Subtype.ext he) ▸ hx
  obtain ⟨k,hk,q,hq,he⟩ := mem_sup_of_normal_right.mp hr
  refine ⟨⟨k,hk⟩,?_⟩
  intro v
  have he' : (k : G) * (q : G) = r := congrArg X.subtype he
  have hqv : (q : G) * (v : G) * (q : G)⁻¹ = v :=
    mul_inv_eq_iff_eq_mul.mpr ((mem_centralizer_iff.mp
      (hQ (mem_map_of_mem X.subtype hq))) v v.property).symm
  rw [←he',mul_inv_rev]
  simpa only [mul_assoc] using congrArg (fun z : G => (k : G) * z * (k : G)⁻¹) hqv

/-- A normal A5 kernel component cannot supply the noncentral point-radical
factor: its marked constituent makes the Baumann subgroup normal. -/
theorem source_primitive_alternatingFive_point_factor_false
    (d : Section08.SourceCompletion.NaturalSetup T L V V₁ V₂ V₃ M G₁)
    (h1221 : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (h : (ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (hU : IsMulCommutative (Section08.Source.UH H V₃))
    (eL : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6))
    (hne : ⁅V₃,G₁.pCoreIn 2⁆ ≠ ⊥)
    (J : Subgroup H) (hJ : J.IsCComponent) (hs : IsSimpleGroup (J ⧸ pCore 2 J))
    (hJC : J.map H.subtype ≤ kernel (ConjugateIntersections.sourceSetup T L V V₃ V₁ H))
    (hp : IsPPerfect 2 (J.map H.subtype)) (hKne : J.map H.subtype ≠ ⊥)
    (hB : normalizer (ChapterB.baumann
      (((ConjugateIntersections.sourceSetup T L V V₃ V₁ H).L₁ ⊔
        (T : Subgroup G)).pCoreIn 2) : Set G) ≤ M)
    (ha : Nonempty ((J ⧸ pCore 2 J) ≃* alternatingGroup (Fin 5)))
    (modules : Section03.PlaneNoncentralitySource.AlternatingFiveModules1332.{u})
    (hfactor : let F := ConjugateIntersections.sourceSetup T L V V₃ V₁ H
      let K := J.map H.subtype
      let R := (F.L₁ ⊔ (T : Subgroup G)).pCoreIn 2
      R ≤ K ⊔ (K ⊔ R).pCoreIn 2) : False := by
  let F := ConjugateIntersections.sourceSetup T L V V₃ V₁ H
  let K := J.map H.subtype
  let R := (F.L₁ ⊔ (T : Subgroup G)).pCoreIn 2
  let X := K ⊔ R
  have hn := (source_primitive_kernel_normal_of_small_model d h hne J hJ hs hJC
    (Or.inl ha)).2
  obtain ⟨I,⟨chosen⟩,_,hIR,hm⟩ := source_primitive_alternatingFive_chosen_in_fixedLayer
    d h hU hne J hJ hs hJC hp hKne ha modules
  let := chosen.elementary
  obtain ⟨hQ,hRI,hinner⟩ := chosen_inner_action_of_point_factor h hn chosen hfactor
  have hJfix := thompson_centralizes_marked_a5_module K I R hIR hRI hm hinner
  have hXK : X ≤ normalizer (K : Set G) := sup_le K.le_normalizer
    (((pCoreIn_le 2 _).trans h.local_le).trans hn)
  have hc : X ⊓ centralizer (I : Set G) = X.pCoreIn 2 :=
    ambient_centralizer_eq_core_of_normal_supplement K I R
      (((pCoreIn_le 2 _).trans h.local_le).trans hn)
      (hIR.trans le_sup_right) (sup_le chosen.normalizes hRI)
      (isPGroup_pCoreIn 2 _) hm.a5_centralizer_eq_core hQ
  obtain ⟨S,hS⟩ := source_normal_kernel_sylow d h eL hne hJC hn
  have hQR : X.pCoreIn 2 ≤ R := (pCoreIn_le_sylow X S).trans_eq hS
  have hRC : R ⊓ centralizer (I : Set G) = X.pCoreIn 2 :=
    le_antisymm ((inf_le_inf_right _ (show R ≤ X from le_sup_right)).trans hc.le)
      (le_inf hQR hQ)
  have hb : ChapterB.baumann R = ChapterB.baumann (X.pCoreIn 2) := by
    rw [ChapterB.lemma_B_2_3_5 R I hIR hJfix,hRC]
  have hKB : K ≤ normalizer (ChapterB.baumann R : Set G) := by
    rw [hb]
    exact (show K ≤ X from le_sup_left).trans
      ((X.le_normalizer.trans (normalizer_le_normalizer_characteristic_image X (pCore 2 X))).trans
        (Stellmacher.normalizer_le_normalizer_baumann _))
  have hd : 3 ∣ Nat.card (J ⧸ pCore 2 J) := by
    obtain ⟨e⟩ := ha
    rw [Nat.card_congr e.toEquiv,nat_card_alternatingGroup]
    norm_num
  exact source_primitive_kernel_not_le_local_of_three_dvd d h1221 h eL hne
    J hJ hs hJC hd (hKB.trans hB)
/-- The original point residual centralizes an A5 kernel component modulo
its two-core. The earlier constituent classification supplies the actual
alternating-module mark used by the source argument. -/
theorem source_primitive_alternatingFive_centralized
    (d : Section08.SourceCompletion.NaturalSetup T L V V₁ V₂ V₃ M G₁)
    (h1221 : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (h : (ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (hU : IsMulCommutative (Section08.Source.UH H V₃))
    (eL : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6))
    (hne : ⁅V₃,G₁.pCoreIn 2⁆ ≠ ⊥)
    (J : Subgroup H) (hJ : J.IsCComponent) (hs : IsSimpleGroup (J ⧸ pCore 2 J))
    (hJC : J.map H.subtype ≤ kernel (ConjugateIntersections.sourceSetup T L V V₃ V₁ H))
    (hB : normalizer (ChapterB.baumann
      (((ConjugateIntersections.sourceSetup T L V V₃ V₁ H).L₁ ⊔
        (T : Subgroup G)).pCoreIn 2) : Set G) ≤ M)
    (ha : Nonempty ((J ⧸ pCore 2 J) ≃* alternatingGroup (Fin 5)))
    (modules : Section03.PlaneNoncentralitySource.AlternatingFiveModules1332.{u}) :
    ⁅J.map H.subtype,(ConjugateIntersections.sourceSetup T L V V₃ V₁ H).L₁⁆ ≤
      (J.map H.subtype).pCoreIn 2 := by
  by_cases hKne : J.map H.subtype = ⊥
  · rw [hKne,commutator_bot_left]
    exact bot_le
  let : Group.IsPerfect J := hJ.perfect
  let : Group.IsPerfect (J.map H.subtype) := Group.IsPerfect.ofSurjective
    (H.subtype.subgroupMap_surjective J)
  have hp : IsPPerfect 2 (J.map H.subtype) := by
    intro N hN hq
    let := hN
    by_contra hne
    let : Nontrivial ((J.map H.subtype) ⧸ N) := QuotientGroup.nontrivial_iff.mpr hne
    let : Group.IsPerfect ((J.map H.subtype) ⧸ N) :=
      Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective N)
    let : Group.IsNilpotent ((J.map H.subtype) ⧸ N) := hq.isNilpotent
    exact Group.IsPerfect.not_isSolvable ((J.map H.subtype) ⧸ N) inferInstance
  by_contra hnon
  obtain ⟨e⟩ := ha
  have hfactor := source_primitive_alternatingFive_radical_factor d h eL hne J hJ hs hJC e hnon
  exact source_primitive_alternatingFive_point_factor_false d h1221 h hU eL hne
    J hJ hs hJC hp hKne hB ⟨e⟩ modules
    (hfactor.le.trans (sup_le_sup inf_le_left le_rfl))
end CFSG.Quasithin.Chapter13.Section07.PlusAction.Original
