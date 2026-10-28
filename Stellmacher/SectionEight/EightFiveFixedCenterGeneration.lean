module
public import Stellmacher.SectionThree.NormalSubgroupCoreControl
public import Stellmacher.SectionEight.LemmaEightThree
public import Stellmacher.QuotientModuleOffenderFixedPoints

/-!
# Fixed-center vector centralizers generate the next local group

In the noncommuting critical-pair context with central next center, assume
that the actual offender fixed subgroup F of the initial center is normal
in the next stabilizer P. Every vector of F has centralizer in P generating
P together with the full initial edge stabilizer. This supplies the generation
premise of the canonical (6.4) vector criterion in the opening of (8.5).

The kernel K = C_P(F) is normal in P. The initial residual's two-core lies
in the edge Sylow and centralizes F, because F lies in the initial center.
By (8.3), that two-subgroup is not contained in the next two-core. The proved
normal-subgroup core control from (3.3) consequently forces K and the Sylow
to generate P. Enlarging K to the vector centralizer and the Sylow to the
full edge gives the assertion. No numbered (8.4) placeholder is used; its
fixed-subgroup normality conclusion remains the exact explicit input.

Source: Stellmacher, Journal of Algebra 190 (1997), (8.5), printed p.40,
and (8.3); refs/latex/stellmacher-n-group.tex.
-/

namespace Stellmacher.SectionEight
open Later SectionsFiveToSeven CosetGraphContext SevenSix

private theorem fixed_normal_centralizer_generates
    {G : Type*} [Group G] [Finite G]
    (S P F T : Subgroup G) (h : SectionThree.Hypotheses G S)
    (hP : P ∈ SectionThree.PSet (⊤ : Subgroup G) S)
    (hsolv : Group.IsSolvable P)
    (hFN : NormalIn F P) (hTS : T ≤ S)
    (hTF : T ≤ Subgroup.centralizer (F : Set G))
    (hTnot : ¬ T ≤ twoCoreAmbient P) :
    (P ⊓ Subgroup.centralizer (F : Set G)) ⊔ S = P := by
  let K := P ⊓ Subgroup.centralizer (F : Set G)
  have hSP : S ≤ P := by
    obtain ⟨R,hR⟩ := hP.1.2.1
    rw [← hR]
    exact Subgroup.map_subtype_le _
  have hKN : (K.subgroupOf P).Normal := by
    have hPnormF : P ≤ Subgroup.normalizer (F : Set G) :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hFN.1).mp hFN.2
    have hNormCentralizer : Subgroup.normalizer (F : Set G) ≤
        Subgroup.normalizer (Subgroup.centralizer (F : Set G) : Set G) :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer
        (Subgroup.centralizer_le_normalizer (F : Set G))).mp inferInstance
    apply (Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_left).mpr
    exact (le_inf P.le_normalizer (hPnormF.trans hNormCentralizer)).trans
      Subgroup.inf_normalizer_le_normalizer_inf
  apply le_antisymm (sup_le inf_le_left hSP)
  by_contra hnot
  have hcore := SectionThree.normal_inf_sylow_le_twoCore S h P K hP hsolv
    inf_le_left hKN hnot
  exact hTnot ((le_inf (le_inf (hTS.trans hSP) hTF) hTS).trans hcore)

private theorem fixed_vector_centralizer_generates
    {G : Type*} [Group G] [Finite G]
    (S P F T D : Subgroup G) (h : SectionThree.Hypotheses G S)
    (hP : P ∈ SectionThree.PSet (⊤ : Subgroup G) S)
    (hsolv : Group.IsSolvable P)
    (hFN : NormalIn F P) (hTS : T ≤ S)
    (hTF : T ≤ Subgroup.centralizer (F : Set G))
    (hTnot : ¬ T ≤ twoCoreAmbient P)
    (hSD : S ≤ D) (hDP : D ≤ P)
    (v : G) (hv : v ∈ F) :
    (P ⊓ Subgroup.centralizer ({v} : Set G)) ⊔ D = P := by
  have hgen := fixed_normal_centralizer_generates S P F T h hP hsolv hFN hTS hTF hTnot
  apply le_antisymm (sup_le inf_le_left hDP)
  apply hgen.ge.trans
  exact sup_le_sup (inf_le_inf_left P (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hv))) hSD

public theorem eight_five_fixed_vector_centralizer_generation
    {H : Type*} [Group H] [Finite H]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    (ctx : SectionEightContext H S0 S P1 P2)
    (hcenter : ZAt ctx.Γ ctx.criticalPath.firstStep ≤
      CenterAmbient (GAt ctx.Γ ctx.criticalPath.firstStep))
    (w : QuotientModuleWitness
      (GAt ctx.Γ ctx.criticalPath.a)
      (GAt ctx.Γ ctx.criticalPath.a ⊓
        Subgroup.centralizer (ZAt ctx.Γ ctx.criticalPath.a : Set H))
      (ZAt ctx.Γ ctx.criticalPath.a))
    (hnormal : NormalIn (w.oneJFixedPoints S)
      (GAt ctx.Γ ctx.criticalPath.firstStep))
    (v : H) (hv : v ∈ w.oneJFixedPoints S) :
    (GAt ctx.Γ ctx.criticalPath.firstStep ⊓
      Subgroup.centralizer ({v} : Set H)) ⊔
      (GAt ctx.Γ ctx.criticalPath.a ⊓ GAt ctx.Γ ctx.criticalPath.firstStep) =
        GAt ctx.Γ ctx.criticalPath.firstStep := by
  let h := ctx.hypothesisTwo.sectionSevenHypotheses ctx.generated
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let T := twoCoreIn (EAt Γ cp.a)
  have hTQ : T ≤ q Γ cp.a := by
    change twoCoreIn (e Γ cp.a) ≤ q Γ cp.a
    rw [CosetGraphContext.e, Γ.twoResidualAt_def, q, Γ.twoCoreAt_def,
      residual_core_eq_inter_core]
    exact inf_le_right
  have hTS : T ≤ S := hTQ.trans (local_cores_le_edge_sylow h Γ cp).1
  have hFZ : w.oneJFixedPoints S ≤ z Γ cp.a := Subgroup.map_subtype_le _
  have hZcentral : z Γ cp.a ≤ Subgroup.centralizer (q Γ cp.a : Set H) := by
    have hb : cp.firstStep ∈ neighborhood Γ cp.a :=
      (mem_neighborhood_iff_adjacent Γ).mpr cp.firstStep_adj
    exact ((lemma_seven_three h Γ).center_core cp.a cp.firstStep hb).trans
      ((omegaOneCenter_le_centerAmbient _).trans (centerAmbient_le_centralizer _))
  have hTF : T ≤ Subgroup.centralizer (w.oneJFixedPoints S : Set H) :=
    hTQ.trans ((Subgroup.le_centralizer_iff.mp hZcentral).trans
      (Subgroup.centralizer_le hFZ))
  have hTnot : ¬ T ≤ twoCoreAmbient (GAt Γ cp.firstStep) := by
    have hn := lemma_eight_three ctx hcenter
    change ¬ T ≤ Γ.twoCoreAt cp.firstStep at hn
    rw [Γ.twoCoreAt_def] at hn
    exact hn
  exact fixed_vector_centralizer_generates S (GAt Γ cp.firstStep)
    (w.oneJFixedPoints S) T (GAt Γ cp.a ⊓ GAt Γ cp.firstStep)
    (sectionThreeHypotheses h)
    ((pFamily_iff_pSet _ _ _).mp (edge_local_data h Γ cp).2.1)
    (edge_local_data h Γ cp).2.2 hnormal hTS hTF hTnot
    cp.S_le_edge_stabilizers inf_le_right v hv

end Stellmacher.SectionEight
