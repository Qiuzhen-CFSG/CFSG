module

public import CFSG.Quasithin.Chapter15.Section04.Centralizer.Preliminaries.MaximalPrimeSource.SolvableXiSource
public import CFSG.Quasithin.Chapter1.Section02.Adequate.Families
public import CFSG.Quasithin.Chapter1.Section02.Uniqueness.NoncentralStructure

/-!
# The initial empty-family and solvability deductions in 15.4.2

For a local component L, put J = L sup T and Q = O₂(J). Characteristic
two puts the original central omega of T inside the central omega of Q.
The proved A.4.8 module comparison then puts its commutator with L inside
V(L). The empty faithful family makes this module trivial. A maximal local
component therefore centralizes the original omega, and 1.2.7(3) contradicts
the two different maximal two-local overgroups in Hypothesis 15.4.1.

Every C-component of a maximal two-local containing T belongs to L(G,T).
Thus the empty local family and 1.2.1(1) make each such overgroup solvable.
The existing solvable Ξ theorem then assembles all of 15.4.2(1–3), retaining
the literal normalizer automizer in 3.2.13. The genuine universal A.3.12
containment, the noncentral structural branch of A.3.6, A.3.9(1), and
3.2.13 inputs remain explicit. The proved orbit bound from the noncentral
branch supplies all orbit information required by uniqueness. Their discharge
belongs to the Chapter A and Chapter 3 owners and the final prime-reduction
assembly. No complete Section 1.2 or full A.3.8 classification is assumed.

Source: Aschbacher–Smith, combined manuscript, 1 March 2004,
Hypothesis 15.4.1 and Lemma 15.4.2(1–3), printed pp.1155–1156.
-/

open Subgroup Theory.GroupTheory

namespace CFSG.Quasithin.Chapter15.Section04.MaximalPrimeSource.InitialSource
open ChapterA.Section04 Chapter1.Section02
universe u
variable {G : Type u} [Group G] [Finite G]

private theorem local_le_centralizer_of_empty_faithful
    (T : Sylow 2 G) (h : SourceHypotheses T) {L : Subgroup G}
    (hL : L ∈ Chapter1.L G (T : Subgroup G)) :
    L ≤ centralizer (Stellmacher.omegaOneCenterAmbient (T : Subgroup G) : Set G) := by
  let J := L ⊔ (T : Subgroup G)
  let Q := J.pCoreIn 2
  have hp : IsPPerfect 2 L := Adequate.mem_L_isPPerfect hL
  have hJ : J ∈ Chapter1.He G :=
    Chapter1.lemma_1_1_4_6 T (h.simpleQTKE.evenCharacteristic T)
      ⟨hL.2.2, show (T : Subgroup G) ≤ J from le_sup_right⟩
  have hQT : Q ≤ (T : Subgroup G) := by
    simpa only [Sylow.coe_subtype, map_subgroupOf_eq_of_le
      (show (T : Subgroup G) ≤ J from le_sup_right)] using
      pCoreIn_le_sylow J (T.subtype (show (T : Subgroup G) ≤ J from le_sup_right))
  have hZQ : Stellmacher.omegaOneCenterAmbient (T : Subgroup G) ≤
      Stellmacher.omegaOneCenterAmbient Q := by
    intro z hz
    obtain ⟨hzT, hzpow, hzcentral⟩ :=
      (Stellmacher.mem_omegaOneCenterAmbient_iff (T : Subgroup G) z).mp hz
    have hzC : z ∈ centralizer (Q : Set G) := by
      apply mem_centralizer_iff.mpr
      intro q hq
      exact hzcentral q (hQT hq)
    have hzQ : z ∈ Q := hJ ⟨(show (T : Subgroup G) ≤ J from le_sup_right) hzT, hzC⟩
    exact (Stellmacher.mem_omegaOneCenterAmbient_iff Q z).mpr
      ⟨hzQ, hzpow, fun q hq => hzcentral q (hQT hq)⟩
  have hLQ : L ≤ normalizer (Q : Set G) :=
    (show L ≤ J from le_sup_left).trans
      (J.le_normalizer.trans (normalizer_le_normalizer_intrinsicCore J))
  have hsub : (L.subgroupOf J).IsSubnormal := hL.1.subnormal
  have hcore : L.pCoreIn 2 ≤ Q :=
    pCoreAmbient_mono_of_isSubnormalIn L J 2 le_sup_left hsub
  have hsig : IsTwoSignalizer L J Q :=
    (isTwoSignalizer_iff L J Q).mpr ⟨pCoreIn_le 2 J, isPGroup_pCoreIn 2 J, hLQ⟩
  have hcomm : ⁅L, Q⁆ ≤ L.pCoreIn 2 :=
    signalizer_commutator_le_pCore L J Q le_sup_left hsub hp hsig
  have hV : intrinsicSignalizerModule L = ⊥ := by
    by_contra hn
    have hf := (Adequate.mem_faithfulLocalComponents_iff_module T
      (h.simpleQTKE.evenCharacteristic T) (B := L)).mpr ⟨hL, hn⟩
    rw [h.empty_faithful] at hf
    exact hf.elim
  apply commutator_eq_bot_iff_le_centralizer.mp
  apply bot_unique
  calc
    ⁅L, Stellmacher.omegaOneCenterAmbient (T : Subgroup G)⁆ ≤
        ⁅L, Stellmacher.omegaOneCenterAmbient Q⁆ := commutator_mono le_rfl hZQ
    _ = signalizerModule L Q := (signalizerModule_eq_commutator_omegaCenter L Q).symm
    _ ≤ intrinsicSignalizerModule L := signalizerModule_le_intrinsicModule L Q hp hLQ hcore hcomm
    _ = ⊥ := hV

variable
  (hA312 : ∀ (X : Type u) [Group X] [Finite X],
    IsSQTK KnownSimple.IsKnownSimple X → pCore 2 X = ⊥ →
    ∀ (S : Sylow 2 X) (B : Subgroup X),
      B ∈ ChapterA.Section03.localCComponents S →
      ∃! K : Subgroup X, K.IsCComponent ∧ B ≤ K)
  (h36 : ChapterA.Section03.CComponentCommutation.NoncentralStructureInput
    KnownSimple.IsKnownSimple.{u})
  (hA39 : ∀ (X : Type u) [Group X] [Finite X],
    IsSQTK KnownSimple.IsKnownSimple X → pCore 2 X = ⊥ →
      cComponentLayer X = solvableResidual X)

include hA312 h36 in
/-- Source 15.4.2(1), with the actual maximal local component and T-orbit
normalizer. Only the genuine earlier A.3 containment and noncentral structural
results remain; the needed orbit bound is proved from the latter. -/
public theorem source_lemma_15_4_2_one
    (T : Sylow 2 G) (h : SourceHypotheses T) : Chapter1.L G (T : Subgroup G) = ∅ := by
  apply Set.eq_empty_of_forall_notMem
  intro B hB
  obtain ⟨L, hL, _⟩ := Chapter1.exists_mem_LStar_ge hB
  have hu := nonsolvable_uniqueness_of_noncentral_structure hA312 h36 h.simpleQTKE T hL
  have hLC := local_le_centralizer_of_empty_faithful T h hL.1
  have hTC : (T : Subgroup G) ≤
      centralizer (Stellmacher.omegaOneCenterAmbient (T : Subgroup G) : Set G) := by
    intro t ht
    apply mem_centralizer_iff.mpr
    intro z hz
    exact ((Stellmacher.mem_omegaOneCenterAmbient_iff (T : Subgroup G) z).mp hz).2.2 t ht |>.symm
  obtain ⟨M₁, M₂, hM₁, hM₂, hC₁, hC₂, hne⟩ := h.centralizer_overgroups
  exact hne ((hu.normalizer_unique M₁ hM₁ ((sup_le hLC hTC).trans hC₁)).trans
    (hu.normalizer_unique M₂ hM₂ ((sup_le hLC hTC).trans hC₂)).symm)

include hA312 h36 hA39 in
/-- Source 15.4.2(2). The intrinsic C-components map to the canonical local
family, and the actual quotient by O₂ supplies 1.2.1(1). -/
public theorem source_lemma_15_4_2_two
    (T : Sylow 2 G) (h : SourceHypotheses T)
    {M : Subgroup G} (hM : IsMaximalTwoLocal M) (hTM : (T : Subgroup G) ≤ M) :
    Group.IsSolvable M := by
  have hempty := source_lemma_15_4_2_one hA312 h36 T h
  have hMH : M ∈ Chapter1.H G := Chapter1.mem_H_of_isTwoLocal hM.1
  have hgen : cComponentLayer M = solvableResidual M :=
    proposition_1_2_1_one_of_A_3_9 hA39 (uniqueness_local_quotient_sqtk h.simpleQTKE hMH)
  have hnone (B : Subgroup M) (hB : B.IsCComponent) : False := by
    have hb : B.map M.subtype ∈ Chapter1.cComponentsIn M := by
      refine ⟨map_subtype_le B, ?_⟩
      simpa only [subgroupOf, comap_map_eq_self_of_injective M.subtype_injective] using hB
    have hlocal := (Chapter1.lemma_1_2_6 T ⟨hMH, hTM⟩).2
      ((Chapter1.lemma_1_2_6 T ⟨hMH, hTM⟩).1 hb)
    rw [hempty] at hlocal
    exact hlocal.elim
  have hzero : solvableResidual M = ⊥ := by
    rw [← hgen]
    apply bot_unique
    exact sSup_le fun B hB => (hnone B hB).elim
  obtain ⟨n, hn⟩ := exists_derivedSeries_eq_solvableResidual (G := M)
  exact ⟨n, hn.trans hzero⟩

include hA312 h36 hA39 in
/-- The complete source 15.4.2(1–3) conclusion, applying the proved solvable
Ξ deduction to clauses (1),(2) established here. The genuine 3.2.13 inclusion
retains the action of the original ambient normalizer on X/O₂(X). -/
public theorem source_earlier1542Conclusion
    (T : Sylow 2 G) (h : SourceHypotheses T)
    (h3213 : Chapter1.XiStarF G (T : Subgroup G) ⊆ Chapter3.XiMinus G (T : Subgroup G)) :
    Earlier1542Conclusion T :=
  source_earlier1542Conclusion_of_solvable T h
    (source_lemma_15_4_2_one hA312 h36 T h)
    (fun _ hM hTM => source_lemma_15_4_2_two hA312 h36 hA39 T h hM hTM) h3213

include hA312 h36 hA39 in
/-- The literal earlier-source input consumed by the published maximal-prime
and C.2.6-free centralizer source families. All three A.3 implications and
the genuine 3.2.13 assertion remain with their existing source producers. -/
public theorem source_earlier1542
    (h3213 : ∀ T : Sylow 2 G, SourceHypotheses T →
      Chapter1.XiStarF G (T : Subgroup G) ⊆ Chapter3.XiMinus G (T : Subgroup G)) :
    Earlier1542 (G := G) :=
  fun T h => source_earlier1542Conclusion hA312 h36 hA39 T h (h3213 T h)

end CFSG.Quasithin.Chapter15.Section04.MaximalPrimeSource.InitialSource
