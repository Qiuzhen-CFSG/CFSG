module

public import CFSG.Quasithin.Chapter13.Section07.PairFixedIntersection
public import CFSG.Quasithin.Chapter1.Section02.Uniqueness.Source
public import CFSG.Quasithin.ChapterA.Section02.SourceAssembly.Complete

/-!
# Original 13.7.17 from the preceding source component

The actual maximal faithful local hypothesis and the proved full A/C
classification supply 1.2.7 uniqueness. The original normalizer is M,
since T normalizes L. This discharges the uniqueness premise of the paired
fixed-intersection theorem. The final consumer constructs the source g and
proves both clauses of 13.7.17 on the unchanged U₀, A and Z_I.

The earlier component conclusion [U₀,K]=1 is precisely 13.7.16(2), and
K≰M is its genuine 13.3.9 source input. Their final discharge stays with
the 13.7.8 assembly. No geometric or classification conclusion is relabeled
as a source hypothesis. Source: Aschbacher–Smith 13.7.17, printed p.944.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter13.Section07
open Section08.SourceCompletion ChapterF.Section09.Setup
universe u
variable {G:Type u} [Group G] [Finite G]
  {T:Sylow 2 G} {L V V₁ V₂ V₃ M G₁ H K:Subgroup G}
  (d:NaturalSetup T L V V₁ V₂ V₃ M G₁)
include d

/-- The full original maximal-local uniqueness needed in 13.7.17, with A/C discharged. -/
theorem source_pair_maximal_uniqueness
    (hmax:Chapter12.Section02.Hypothesis1221 KnownSimple.IsKnownSimple T L) :
    ∀N:Subgroup G,IsMaximalTwoLocal N→L⊔(T:Subgroup G)≤N→N=M := by
  have hu:=Chapter1.Section02.nonsolvable_uniqueness_of_theoremsAC
    (fun X _ _=>ChapterA.Section02.theoremA_knownSimple (G:=X))
    (fun X _ _=>ChapterA.Section02.theoremC_knownSimple (G:=X))
    hmax.simpleQTKE T hmax.maximal_faithful.1
  have ho:componentOrbit L (T:Subgroup G)=L := by
    apply le_antisymm _ (le_componentOrbit L _)
    apply iSup_le
    intro t
    exact (mem_normalizer_iff_map_conj_eq.mp (d.normalizes_L t.property)).le
  intro N hN hLN
  have he:=hu.normalizer_unique N hN hLN
  rwa [ho,←d.local_normalizer] at he

/-- Both clauses of original 13.7.17 with a constructed source conjugator.
The original 13.7.16 component and 13.3.9 escape are the only later-branch inputs. -/
theorem source_fixed_intersection
    (hmax:Chapter12.Section02.Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (h:(ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (hU:IsMulCommutative (Section08.Source.UH H V₃))
    (hV:¬IsMulCommutative (Section08.Source.VH H V))
    (hHG:H≤G₁) (hne:⁅V₃,G₁.pCoreIn 2⁆≠⊥)
    (hK:K≤centralizer ((Section08.Source.UH H V₃⊓centralizer (Section08.Source.QH H:Set G):Subgroup G):Set G))
    (hKM:¬K≤M) :
    ∃g:L,
      (QuotientGroup.mk' (pCore 2 (L⊔(T:Subgroup G):Subgroup G)) (inclusion le_sup_left g))^2=1 ∧
      V≤V₃⊔conjugate V₁ (g:G) ∧
      ¬conjugate V₁ (g:G)≤Section08.Source.UH H V₃ ∧
      let U:=Section08.Source.UH H V₃
      let U₀:=U⊓centralizer (Section08.Source.QH H:Set G)
      let E:=Section08.Source.VH H V⊓conjugate (Section08.Source.VH H V) (g:G)
      let A:=conjugate (Section08.Source.VH H V) (g:G)⊓(L⊔(T:Subgroup G):Subgroup G).pCoreIn 2
      U₀⊓conjugate U (g:G)=⊥ ∧ E⊓U₀=V₁ ∧
        (U₀≤⁅U,A⁆⊔V₃→U₀=V₁) := by
  obtain ⟨g,hs,hspan⟩:=exists_chosen_conjugator d
  have hout:=ConjugateIntersections.lemma_13_7_10_one h (g:G) hspan hU hV
  have hunique:=source_pair_maximal_uniqueness d hmax
  have hnon:=seed_noncentral_on_local_core h hHG hne
  have hdis:=pair_fixed_disjoint_conjugate d h hU hV hnon hunique hK hKM (inclusion le_sup_left g) hout
  have he:=pair_intersection_fixed_eq_point d h hU hV hnon hunique hK hKM
    (inclusion le_sup_left g) hs hout
  refine ⟨g,hs,hspan,hout,hdis,he,?_⟩
  intro hc
  have hcomm:=pair_seed_actor_commutator_le_intersection d h hU (inclusion le_sup_left g)
  have hseed:V₃≤Section08.Source.VH H V⊓conjugate (Section08.Source.VH H V) (g:G):=
    (pair_seed_complement d h hU (inclusion le_sup_left g) hs hout).2.2.2.2
  apply le_antisymm
  · exact (le_inf (hc.trans (sup_le hcomm hseed)) le_rfl).trans he.le
  · exact le_inf (h.point_lt.le.trans (le_conjugateSpanBy V₃ H))
      (le_centralizer_iff.mp ((pCoreIn_le 2 H).trans h.H_centralizes))

end CFSG.Quasithin.Chapter13.Section07
