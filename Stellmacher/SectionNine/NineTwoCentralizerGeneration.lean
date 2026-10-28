module
public import Stellmacher.SectionNine.GeneratedContext
public import Stellmacher.SectionFiveToSeven.Result7_6.LocalFacts
public import Stellmacher.SectionFiveToSeven.Result7_6.GraphFacts
public import Stellmacher.SectionThree.LocalFamilyGeneratingExtraction

/-!
# Generation from a neighboring center vector in (9.2)

In the normalized Section Nine graph, suppose the core at a chosen neighbor
of the next vertex generates the next stabilizer together with the original
full edge stabilizer. Every vector in that neighbor's center then has a
centralizer in the next stabilizer which generates it together with the
distinguished Sylow subgroup T. The conclusion uses the literal cyclic
subgroup centralizer from `sectionSixCentralizerJoin`.

The full edge is proper: otherwise the initial stabilizer is the whole
graph group, and its nontrivial normal two-core contradicts the ambient
trivial two-core. Unique maximal containment above T therefore promotes
the given generation equation to generation by the neighboring core and T.
The neighboring center lies in the omega-center of its core, so that core
centralizes the chosen vector and its cyclic subgroup. Enlarging this core
to the indicated centralizer gives the desired equality.

This is the generating contradiction used when applying (6.4) in
Stellmacher (9.2), Journal of Algebra 190 (1997), p.48. Source:
`refs/files/stellmacher-n-group.pdf`. The full edge is kept distinct from T;
no centralization of that edge is assumed. Only the genuine local graph
hypotheses are used, and no numbered Section Nine conclusion is imported.
-/
namespace Stellmacher.SectionNine
open Later SectionsFiveToSeven CosetGraphContext SevenSix
universe u

public theorem nine_two_centralizer_generation
    {G : Type u} [Group G] [Finite G] {T A B : Subgroup G}
    (ctx : SectionNineLocalContext G T A B)
    (m : ctx.Γ.Vertex) (hm : m ∈ Neighborhood ctx.Γ ctx.criticalPath.firstStep)
    (hgenerate : QAt ctx.Γ m ⊔ (GAt ctx.Γ ctx.criticalPath.a ⊓
      GAt ctx.Γ ctx.criticalPath.firstStep) = GAt ctx.Γ ctx.criticalPath.firstStep)
    (w : G) (hw : w ∈ ZAt ctx.Γ m) :
    sectionSixCentralizerJoin (GAt ctx.Γ ctx.criticalPath.firstStep) T w =
      GAt ctx.Γ ctx.criticalPath.firstStep := by
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let Pa := GAt Γ cp.a
  let P := GAt Γ cp.firstStep
  let D := Pa ⊓ P
  let R := QAt Γ m
  have hlocal := edge_local_data ctx.sectionSeven Γ cp
  have hPa : Pa ∈ PFamily (⊤ : Subgroup G) T := hlocal.1.1
  have hP : P ∈ SectionThree.PSet (⊤ : Subgroup G) T :=
    (pFamily_iff_pSet _ _ _).mp hlocal.2.1
  have hTD : T ≤ D := cp.S_le_edge_stabilizers
  have hjoin : Pa ⊔ P = ⊤ := by
    change stabilizer Γ cp.a ⊔ stabilizer Γ cp.firstStep = ⊤
    rcases cp.edge_stabilizers_are_P with hedge | hedge
    · rw [hedge.1, hedge.2]
      exact ctx.sectionSeven.generated
    · rw [hedge.1, hedge.2, sup_comm]
      exact ctx.sectionSeven.generated
  have hDproper : D ≠ P := by
    intro he
    have hPPa : P ≤ Pa := he ▸ (inf_le_left : D ≤ Pa)
    have hPatop : Pa = ⊤ := by rwa [sup_eq_left.mpr hPPa] at hjoin
    let Q := QAt Γ cp.a
    have hQne : Q ≠ ⊥ := by
      change q Γ cp.a ≠ ⊥
      rw [q, Γ.twoCoreAt_def]
      exact hPa.1.2.2.1
    have hQp : IsPGroup 2 Q := by
      change IsPGroup 2 (q Γ cp.a)
      rw [q, Γ.twoCoreAt_def]
      exact (pCore_isPGroup (p := 2) (G := Pa)).map Pa.subtype
    have hQn : Q.Normal := by
      apply Subgroup.normalizer_eq_top_iff.mp
      apply top_unique
      rw [← hPatop]
      exact stabilizer_le_normalizer_q Γ cp.a
    have hQle : Q ≤ pCore 2 G := le_sSup ⟨hQn, hQp⟩
    exact hQne (bot_unique (hQle.trans_eq ctx.sectionSeven.twoCore_eq_bot))
  have hRP : R ≤ P := le_sup_left.trans_eq hgenerate
  have hRT : R ⊔ T = P := by
    by_contra hproper
    obtain ⟨M, hM, hTM, huniq⟩ := hP.2
    have hRTM : R ⊔ T ≤ M.map P.subtype :=
      SectionThree.le_unique_maximal_over huniq le_sup_right
        (sup_le hRP (hTD.trans inf_le_right)) hproper
    have hDM : D ≤ M.map P.subtype :=
      SectionThree.le_unique_maximal_over huniq hTD inf_le_right hDproper
    have hPM : P ≤ M.map P.subtype :=
      hgenerate.ge.trans (sup_le (le_sup_left.trans hRTM) hDM)
    apply hM.ne_top
    apply Subgroup.map_injective P.subtype_injective
    rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
    exact le_antisymm (Subgroup.map_subtype_le _) hPM
  have hneighbor : cp.firstStep ∈ neighborhood Γ m :=
    (mem_neighborhood_iff_adjacent Γ).mpr
      (Γ.adjacent_symm ((mem_neighborhood_iff_adjacent Γ).mp hm))
  have hcenter : ZAt Γ m ≤ Subgroup.centralizer (R : Set G) :=
    ((lemma_seven_three ctx.sectionSeven Γ).center_core m cp.firstStep hneighbor).trans
      ((omegaOneCenter_le_centerAmbient _).trans (centerAmbient_le_centralizer _))
  have hRcent : R ≤ Subgroup.centralizer (Subgroup.zpowers w : Set G) := by
    intro r hr
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    have hwr : w * r = r * w :=
      (Subgroup.mem_centralizer_iff.mp (hcenter hw) r hr).symm
    exact (show Commute w r from hwr).zpow_left n
  apply le_antisymm
  · exact sup_le inf_le_left (hTD.trans inf_le_right)
  · exact hRT.ge.trans (sup_le_sup_right (le_inf hRP hRcent) T)
end Stellmacher.SectionNine
