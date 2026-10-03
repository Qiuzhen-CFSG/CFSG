module
public import Stellmacher.SectionNine.NineTwoAmbientSetup
public import Stellmacher.SectionNine.NineTwoCenterSectionSixModule
public import Stellmacher.SectionFiveToSeven.Result6_4
public import Stellmacher.SectionThree.LocalFamilyGeneratingExtraction
public import Stellmacher.BaumannMap


/-!
# Generating vectors fixed by the canonical barred subgroup

Assume only that the canonical barred critical subgroup is nontrivial in the
actual ambient Section Nine context. A vector of the initial center fixed by
its entire canonical preimage is subject directly to (6.4). No identification
with the native Baumann subgroup or nontrivial native Thompson action is needed.

If R generates the next stabilizer with the full initial edge and centralizes
the vector, unique maximality over T turns this into generation with T. Mapping
to the original ambient group identifies the exact Section Six module and
Sylow omega-center. The canonical (6.4) rules out the vector outside that
omega-center, proving it belongs to the next vertex center.

This proves the fixed-space implication used in Stellmacher (9.3), Journal
of Algebra 190 (1997), p.50, `refs/files/stellmacher-n-group.pdf`, directly
for the barred subgroup of (6.4). It also covers a trivial native Thompson
image when the canonical action still has a nontrivial offender.
-/

namespace Stellmacher.SectionNine
open Later SectionsFiveToSeven CosetGraphContext SevenSix
universe u

private theorem sylow_generation
    {G : Type u} [Group G] [Finite G] {T A B : Subgroup G}
    (ctx : SectionNineLocalContext G T A B) (R : Subgroup G)
    (hgenerate : R ⊔ (GAt ctx.Γ ctx.criticalPath.a ⊓
      GAt ctx.Γ ctx.criticalPath.firstStep) = GAt ctx.Γ ctx.criticalPath.firstStep) :
    R ⊔ T = GAt ctx.Γ ctx.criticalPath.firstStep := by
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let Pa := GAt Γ cp.a
  let P := GAt Γ cp.firstStep
  let D := Pa ⊓ P
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
  exact hRT

public theorem nine_three_canonical_fixed_generation
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (hJ : sectionSixBarredCritical ctx.hypothesisTwo ≠ ⊥)
    (R : Subgroup G)
    (hgenerate : R ⊔ (GAt ctx.Γ ctx.criticalPath.a ⊓
      GAt ctx.Γ ctx.criticalPath.firstStep) = GAt ctx.Γ ctx.criticalPath.firstStep) :
    ∀ w : G, w ∈ ZAt ctx.Γ ctx.criticalPath.a →
      embedding w ∈ Subgroup.centralizer
        (sectionSixBarredCriticalPreimage ctx.hypothesisTwo : Set H) →
      w ∈ Subgroup.centralizer (R : Set G) → w ∈ ZAt ctx.Γ ctx.criticalPath.firstStep := by
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  have hsetup := nine_two_ambient_setup ctx
  have hfirstMap : (GAt Γ cp.a).map embedding = P1 := hsetup.2.1
  have hnextMap : (GAt Γ cp.firstStep).map embedding = P2 := hsetup.2.2.1
  have hVmap : (ZAt Γ cp.a).map embedding = sectionSixV S P1 :=
    nine_two_center_eq_sectionSixV ctx hfirstMap
  have hnext := (lemma_seven_five ctx.sectionSeven Γ cp ctx.commutator_eq).next_center
  have homega : (ZAt Γ cp.firstStep).map embedding = omegaOneCenter S := by
    rw [show ZAt Γ cp.firstStep = omegaOneCenter T from hnext.1,← ctx.map_S]
    exact (omegaOneCenterAmbient_map_injective embedding ctx.embedding_injective T).symm
  have hcomm : ⁅P2,omegaOneCenter S⁆ = ⊥ := by
    rw [← hnextMap,← homega,← Subgroup.map_commutator]
    have hlocal : ⁅GAt Γ cp.firstStep,ZAt Γ cp.firstStep⁆ = ⊥ := by
      apply Subgroup.commutator_eq_bot_iff_le_centralizer.mpr
      apply Subgroup.le_centralizer_iff.mpr
      rw [show ZAt Γ cp.firstStep = omegaOneCenter (GAt Γ cp.firstStep) from hnext.2]
      exact (omegaOneCenter_le_centerAmbient _).trans (centerAmbient_le_centralizer _)
    rw [hlocal,Subgroup.map_bot]
  have hRT : R ⊔ T = GAt Γ cp.firstStep :=
    sylow_generation ctx.toLocalContext R hgenerate
  have hRTH : R.map embedding ⊔ S = P2 := by
    rw [← ctx.map_S,← Subgroup.map_sup,hRT,hnextMap]
  intro w hwZa hwJ hwR
  have hwV : embedding w ∈ sectionSixV S P1 := hVmap ▸
    Subgroup.mem_map_of_mem embedding hwZa
  by_contra hwZ
  have hwOmega : embedding w ∉ omegaOneCenter S := by
    intro hm
    rw [← homega] at hm
    obtain ⟨w0,hw0,he⟩ := hm
    exact hwZ (ctx.embedding_injective he ▸ hw0)
  have hRcentral : R.map embedding ≤
      Subgroup.centralizer (Subgroup.zpowers (embedding w) : Set H) := by
    rintro r ⟨r0,hr0,rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    obtain ⟨k,rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
    apply (show Commute (embedding w) (embedding r0) from ?_).zpow_left k
    change embedding w * embedding r0 = embedding r0 * embedding w
    simpa only [map_mul] using congrArg embedding
      (Subgroup.mem_centralizer_iff.mp hwR r0 hr0).symm
  have hgen : sectionSixCentralizerJoin P2 S (embedding w) = P2 := by
    apply le_antisymm
    · exact sup_le inf_le_left ctx.hypothesisTwo.fiveOne.P2_mem.1.2.1.1
    · exact hRTH.ge.trans (sup_le_sup_right
        (le_inf (le_sup_left.trans_eq hRTH) hRcentral) S)
  exact lemma_six_four S0 S P1 P2 ctx.hypothesisTwo (sectionSixV S P1) rfl
    hcomm hJ (embedding w) hwV hwJ hwOmega hgen.symm

end Stellmacher.SectionNine
