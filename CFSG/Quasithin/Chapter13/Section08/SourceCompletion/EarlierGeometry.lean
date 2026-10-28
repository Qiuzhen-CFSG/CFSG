module

public import CFSG.Quasithin.Chapter13.Section08.SourceCompletion.EdgeCores
public import CFSG.Quasithin.Chapter13.Section08.SourceCompletion.CriticalLines
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.CriticalGeometry.Reorientation.Equivalence

/-!
# Full earlier critical geometry from the original A6 source configuration

The actual edge-core containment and normality of the first ball kernel
identify its intersection with V-gamma as the two-core intersection. The
previous kernel theorem then gives F.9.15. Together with the endpoint,
commutator and line theorems this constructs all eight EarlierGeometry
fields. Natural transitivity and the genuine abelian full V-span discharge
intersecting-conjugate commutativity; equality of critical distances makes
the result uniform over all genuine critical pairs.

The final reorientation theorem applies the existing graph reversal to the
original strict-denominator case. Only original 13.7.8 and 13.5.7 remain as
earlier source inputs; no geometry, path, line or action-kernel conclusion
is assumed. Source: Aschbacher--Smith, F.9.13--17 and 13.8.2--8, pp.322--324,
946--949, combined manuscript of 1 March 2004.
-/

public section
open Subgroup
namespace CFSG.Quasithin.Chapter13.Section08.SourceCompletion
open CriticalGeometry
open ComponentSieve.AlternatingAndLinear.FourStructure.CriticalTransfer.PairConsequences.ReversedSourceData
variable {G : Type*} [Group G] [Finite G]

theorem f9_first_kernel (D:ChapterF.Section09.Setup G) (h:D.Hypothesis)
    (c:CriticalPair D.L (D.T:Subgroup G) D.H D.V) (hb:3≤c.path.length) :
    c.Vgamma⊓firstKernel D.L (D.T:Subgroup G) D.H (base _ _ _ true)=
      Source.Egamma c.Vgamma D.UH D.V₁ := by
  let K:=firstKernel D.L (D.T:Subgroup G) D.H (base _ _ _ true)
  have hKH:K≤D.H := by
    exact (show K≤vertexGroup _ _ _ (base _ _ _ true) from inf_le_left).trans_eq (vertexGroup_base _ _ _ true)
  have hKN:D.H≤normalizer (K:Set G) := by
    intro a ha
    let aH:D.H:=⟨a,ha⟩
    have he:=firstKernel_smul (inG0 (L:=D.L) (T:=(D.T:Subgroup G)) aH) (base _ _ _ true)
    rw [inG0_one] at he
    exact mem_normalizer_iff_map_conj_eq.mpr he.symm
  have hKQ:K.pCoreIn 2≤D.QH :=
    le_pCoreIn_of_normalizes (isPGroup_pCoreIn 2 K) ((pCoreIn_le 2 K).trans hKH)
      (hKN.trans (normalizer_le_normalizer_characteristic_image K (pCore 2 K)))
  have hedge:(graph D.L (D.T:Subgroup G) D.H).Adj (base _ _ _ true) c.second := by
    have he:=c.path.adj_getVert_succ (i:=1) (by omega)
    rwa [c.first] at he
  have hKE:K≤edgeGroup D.L (D.T:Subgroup G) D.H (base _ _ _ true) c.second :=
    le_inf inf_le_left (inf_le_right.trans ((iInf_le _ c.second).trans (iInf_le _ hedge)))
  have hinter:c.Vgamma⊓K≤D.QH := by
    have he:=f9_endpoint_edge_cores D h c hb
    exact ((le_inf inf_le_right (inf_le_left.trans he.2)).trans
      (inf_pCoreIn_le_of_le 2 hKE)).trans hKQ
  have hid:c.Vgamma⊓K=c.Vgamma⊓D.QH :=
    le_antisymm (le_inf inf_le_left hinter) (inf_le_inf_left _ (f9_core_le_firstKernel D h))
  have hg:=f9_commutatorPreimage_eq D h c.Vgamma (f9_endpoint_spans D h c hb).2
  exact hid.trans hg.symm

theorem f9_earlierGeometry (D:ChapterF.Section09.Setup G) (h:D.Hypothesis)
    (c:CriticalPair D.L (D.T:Subgroup G) D.H D.V) (hb:3≤c.path.length)
    (hcomm:∀g:G,D.V⊓D.V.map (MulAut.conj g).toMonoidHom≠⊥ →
      ⁅D.V,D.V.map (MulAut.conj g).toMonoidHom⁆=⊥) :
    Reorientation.EarlierGeometry c D.Vplus D.V₁ where
  length:=hb
  VH_endpoint:=(f9_endpoint_spans D h c hb).1
  Vgamma_H:=(f9_endpoint_spans D h c hb).2
  DH_kernel:=(f9_endpoint_kernels D h c hb).1
  Dgamma_kernel:=(f9_endpoint_kernels D h c hb).2
  lines_disjoint:=f9_lines_disjoint D h c hb hcomm
  cross_centralizes:=f9_denominators_centralize D h c hb hcomm
  first_kernel:=f9_first_kernel D h c hb

namespace NaturalSetup
variable {T:Sylow 2 G} {L V V₁ V₂ V₃ M G₁ H:Subgroup G}

theorem intersecting_conjugates_commute (d:NaturalSetup T L V V₁ V₂ V₃ M G₁)
    (hspan:IsMulCommutative (conjugateSpanBy V G₁)) (g:G)
    (hi:V⊓V.map (MulAut.conj g).toMonoidHom≠⊥) :
    ⁅V,V.map (MulAut.conj g).toMonoidHom⁆=⊥ := by
  obtain ⟨z,hz,huniq⟩:=(Nat.card_eq_two_iff' (1:V₁)).mp d.line_card
  have hzG:(z:G)≠1:=fun he=>hz (Subtype.ext he)
  have hp:V₁=zpowers (z:G) := by
    apply le_antisymm
    · intro x hx
      by_cases hx1:x=1
      · exact hx1 ▸ (zpowers (z:G)).one_mem
      · have he:(⟨x,hx⟩:V₁)=z:=huniq _ (fun h=>hx1 (congrArg Subtype.val h))
        rw [show x=(z:G) from congrArg Subtype.val he]
        exact mem_zpowers (z:G)
    · exact zpowers_le.mpr z.property
  have hCG:centralizer ({(z:G)}:Set G)≤G₁ := by
    rw [d.first_normalizer]
    have hc:centralizer ({(z:G)}:Set G)≤normalizer (zpowers (z:G):Set G) := by
      have he:centralizer (zpowers (z:G):Set G)=centralizer ({(z:G)}:Set G) := by
        rw [zpowers_eq_closure,centralizer_closure]
      exact he.symm.le.trans (Subgroup.centralizer_le_normalizer _)
    exact hc.trans_eq (congrArg (fun A:Subgroup G=>normalizer (A:Set G)) hp.symm)
  let : IsMulCommutative (conjugateSpanBy V G₁):=hspan
  let : IsMulCommutative (centralizerConjugateClosure V (z:G)) := by
    rw [centralizerConjugateClosure_eq_conjugateSpanBy]
    exact conjugateSpanBy_isMulCommutative_of_le le_rfl hCG
  have hzV:(z:G)∈V:=d.line_le_plane.trans (d.plane_le_seed.trans d.seed_le) z.property
  exact Section08.intersecting_conjugates_commute L V hzG
    (le_sup_left.trans d.normalizes_V)
    (fun x hx hx1=>Section07.natural_nonzero_transitive d hzV hx hzG hx1) g hi

/-- The original source hypotheses supply the geometry uniformly, so the
reorientation theorem may choose a different genuine critical pair. -/
theorem earlierGeometry (d:NaturalSetup T L V V₁ V₂ V₃ M G₁)
    (hspan:IsMulCommutative (conjugateSpanBy V G₁))
    (hF9:(Section07.ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (c:CriticalPair L (T:Subgroup G) H V) :
    Reorientation.EarlierGeometry c V₃ V₁ := by
  obtain ⟨c₀,hb,_⟩:=d.exists_criticalPair hspan hF9
  have he:c.path.length=c₀.path.length:=c.length_eq.trans c₀.length_eq.symm
  exact f9_earlierGeometry _ hF9 c (he ▸ hb)
    (fun g hi=>d.intersecting_conjugates_commute hspan g hi)

/-- Actual reorientation consumer: the strict denominator selects the
opposite critical pair using the now-derived first-kernel identity. -/
theorem exists_reversal_of_strict (d:NaturalSetup T L V V₁ V₂ V₃ M G₁)
    (hspan:IsMulCommutative (conjugateSpanBy V G₁))
    (hF9:(Section07.ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (c:CriticalPair L (T:Subgroup G) H V)
    (hstrict:Source.Dgamma (c.Ugamma V₃) (Source.UH H V₃) V₁<c.Ugamma V₃) :
    Nonempty (Reversal c) := by
  have hg:=d.earlierGeometry hspan hF9 c
  exact Reorientation.exists_reversal_of_strict c V₃ V₁ hg.length d.seed_le
    hg.Vgamma_H (hF9.H_centralizes.trans (Subgroup.centralizer_le_normalizer _))
    hg.first_kernel hstrict

theorem exists_earlierGeometry (d:NaturalSetup T L V V₁ V₂ V₃ M G₁)
    (hspan:IsMulCommutative (conjugateSpanBy V G₁))
    (hF9:(Section07.ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis) :
    ∃c:CriticalPair L (T:Subgroup G) H V, Odd c.path.length ∧
      Reorientation.EarlierGeometry c V₃ V₁ ∧ ¬⁅c.Ugamma V₃,V⁆≤c.Aone V₁ := by
  obtain ⟨c,hb,ho⟩:=d.exists_criticalPair hspan hF9
  refine ⟨c,ho,f9_earlierGeometry _ hF9 c hb ?_,f9_commutator_not_le_Aone _ hF9 c hb⟩
  exact fun g hi=>d.intersecting_conjugates_commute hspan g hi

end NaturalSetup
end CFSG.Quasithin.Chapter13.Section08.SourceCompletion
