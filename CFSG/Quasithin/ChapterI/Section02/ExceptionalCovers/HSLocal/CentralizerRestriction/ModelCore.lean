module

public import CFSG.Quasithin.Chapter16.Section01To02.OtherPreliminaries.JankoTwoHigmanSims.HSInner.CoreStructure
public import Theory.SpecificGroups.SymmetricFive.AutomorphismRank
public import Theory.GroupTheory.PCoreSurjective

public import CFSG.Quasithin.ChapterI.Section02.ExceptionalCovers.HSLocal.CentralizerRestriction.InvolutionLifting

/-!
# The HS pair kernel and its involutions

The actual five-point action identifies the full centralizer's two-core with
its pair kernel. The existing two quaternion factors and cyclic factor cover
that kernel by its proved order bound. A single-letter square test on those
coordinates certifies that its involutions have fixed letters, hence belong
to the two-central HS class. Conjugation gives the same assertion for every
two-central involution centralizer.

The alternating preimage and its literal A₅ quotient are also defined here.
Identifying this preimage with O² of the full local, and calculating its
noncentral order-four orbit, remain separate obligations.

Source: Aschbacher–Smith I.2.2(5), printed pp.411–412 / PDF pp.422–423;
the exact centralizer structure is 16.1.5(10), printed p.1172.
-/

public section
open CFSG.Quasithin.Chapter16.OtherPreliminaries.JankoTwoHigmanSims
open Subgroup
open Sporadic.LeechRelated.HS Sporadic.LeechRelated.HS.EvenLocalCandidates
open Sporadic.LeechRelated.HS.EvenLocalCandidates.CentralInvolutionCore
open CFSG.Quasithin.Chapter16.OtherPreliminaries.JankoTwoHigmanSims.HSInner
open CFSG.Quasithin.Chapter16.OtherPreliminaries.JankoTwoHigmanSims.HSInner.CoreStructure
namespace CFSG.Quasithin.ChapterI.Section02.ExceptionalCovers.HSLocal.CentralizerRestriction

@[expose] noncomputable def modelResidual : Subgroup (localGroup 0) :=
  (alternatingGroup (Fin 5)).comap CentralNormalizerThreePart.PairQuotient.fiveHom

@[expose] noncomputable def modelResidualAction : modelResidual →* alternatingGroup (Fin 5) :=
  CentralNormalizerThreePart.PairQuotient.fiveHom.restrict (fun _ hx => hx)

theorem modelResidualAction_surjective : Function.Surjective modelResidualAction := by
  intro y
  obtain ⟨x, hx⟩ := CentralNormalizerThreePart.PairQuotient.fiveHom_surjective y.val
  exact ⟨⟨x, show CentralNormalizerThreePart.PairQuotient.fiveHom x ∈
    alternatingGroup (Fin 5) from hx.symm ▸ y.property⟩, Subtype.ext hx⟩

theorem modelResidualAction_ker : modelResidualAction.ker = core.subgroupOf modelResidual := by
  ext x
  change modelResidualAction x = 1 ↔ x.val ∈ core
  rw [← CentralNormalizerThreePart.PairQuotient.fiveHom_kernel]
  exact Subtype.ext_iff

instance modelCore_normal : (core.subgroupOf modelResidual).Normal := by
  rw [← modelResidualAction_ker]
  infer_instance

@[expose] noncomputable def modelResidualQuotient :
    modelResidual ⧸ core.subgroupOf modelResidual ≃* alternatingGroup (Fin 5) :=
  (QuotientGroup.quotientMulEquivOfEq modelResidualAction_ker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective modelResidualAction modelResidualAction_surjective)

theorem modelResidualQuotient_mk (x : modelResidual) :
    modelResidualQuotient (QuotientGroup.mk' (core.subgroupOf modelResidual) x) =
      modelResidualAction x := rfl

theorem model_pCore_eq : pCore 2 (localGroup 0) = core := by
  rw [← CentralNormalizerThreePart.PairQuotient.fiveHom.comap_pCore_of_ker_isPGroup
    CentralNormalizerThreePart.PairQuotient.fiveHom_surjective
    (by rw [CentralNormalizerThreePart.PairQuotient.fiveHom_kernel]; exact core_isPGroup),
    Theory.SpecificGroups.SymmetricFive.pCore_two_eq_bot, MonoidHom.comap_bot,
    CentralNormalizerThreePart.PairQuotient.fiveHom_kernel]

theorem model_core_expression (g : core) :
    ∃ a b : QuaternionGroup 2, ∃ c : C4,
      leftEmbedding a * rightEmbedding b * cyclicEmbedding c = g := by
  have he : embeddedCore = ⊤ := by
    apply eq_of_le_of_card_ge le_top
    simpa only [Nat.card_congr (topEquiv : (⊤ : Subgroup core) ≃* core).toEquiv,
      embeddedCore_card] using core_card_le
  have hg : g ∈ embeddedCore := he ▸ mem_top g
  have hn : quaternionPart ≤ normalizer (cyclicPart : Set core) := by
    apply le_trans ?_ (centralizer_le_normalizer _)
    intro b hb c hc
    exact (parts_commute b hb c hc).symm
  change g ∈ (↑(quaternionPart ⊔ cyclicPart) : Set core) at hg
  rw [coe_mul_of_left_le_normalizer_right quaternionPart cyclicPart hn] at hg
  obtain ⟨q, hq, c, hc, hqc⟩ := hg
  obtain ⟨a, b, rfl⟩ := (mem_quaternionPart q).mp hq
  obtain ⟨d, rfl⟩ := hc
  exact ⟨a, b, d, hqc⟩

set_option maxRecDepth 10000 in
private theorem model_core_fixed_test :
    ∀ a b : QuaternionGroup 2, ∀ c : C4,
      inclusion (leftEmbedding a * rightEmbedding b * cyclicEmbedding c).val.val
        (inclusion (leftEmbedding a * rightEmbedding b * cyclicEmbedding c).val.val 1) = 1 →
      ∃ p : Fin 100,
        inclusion (leftEmbedding a * rightEmbedding b * cyclicEmbedding c).val.val p = p := by
  decide +kernel

theorem model_core_fixed_letter (g : core) (hg : g ^ 2 = 1) :
    ∃ p : Fin 100, inclusion g.val.val p = p := by
  obtain ⟨a, b, c, rfl⟩ := model_core_expression g
  apply model_core_fixed_test a b c
  have h := congrArg (fun x : core => inclusion x.val.val 1) hg
  simpa only [pow_two, coe_mul, coe_one, map_mul, map_one, Equiv.Perm.mul_apply,
    Equiv.Perm.one_apply] using h

/-- The model kernel's involutions all have the two-central marking. -/
theorem model_core_twoCentral (g : core) (hg : orderOf g.val.val = 2) :
    Theory.GroupTheory.DoubleCoverCentralizer.TwoCentral g.val.val := by
  have hsq : g ^ 2 = 1 := by
    apply Subtype.ext
    apply Subtype.ext
    have h := pow_orderOf_eq_one g.val.val
    rw [hg] at h
    exact h
  obtain ⟨p, hp⟩ := model_core_fixed_letter g hsq
  exact twoCentral_of_fixed_letter _ hg p hp

/-- Purity for the full two-core of the marked model centralizer. -/
theorem marked_centralizer_core_twoCentral (x : Carrier)
    (hx : x ∈ (centralizer ({e0} : Set Carrier)).pCoreIn 2)
    (hx2 : orderOf x = 2) : Theory.GroupTheory.DoubleCoverCentralizer.TwoCentral x := by
  rw [← localGroup_zero_eq_centralizer] at hx
  obtain ⟨g, hg, rfl⟩ := hx
  rw [model_pCore_eq] at hg
  exact model_core_twoCentral ⟨g, hg⟩ hx2

/-- Conjugation transports kernel purity to every two-central model centralizer. -/
theorem model_centralizer_core_twoCentral (t : Carrier) (ht : orderOf t = 2)
    (htc : Theory.GroupTheory.DoubleCoverCentralizer.TwoCentral t)
    (x : Carrier) (hx : x ∈ (centralizer ({t} : Set Carrier)).pCoreIn 2)
    (hx2 : orderOf x = 2) : Theory.GroupTheory.DoubleCoverCentralizer.TwoCentral x := by
  obtain ⟨g, hg⟩ := isConj_iff.mp ((twoCentral_iff_isConj_e0 t ht).mp htc)
  have hm : ((centralizer ({e0} : Set Carrier)).pCoreIn 2).map
      (MulAut.conj g).toMonoidHom = (centralizer ({t} : Set Carrier)).pCoreIn 2 := by
    rw [map_pCoreIn_of_injective 2 _ _ (MulAut.conj g).injective,
      Theory.GroupTheory.map_centralizer_singleton, MulAut.conj_apply, hg]
  rw [← hm] at hx
  obtain ⟨y, hy, rfl⟩ := hx
  have hy2 : orderOf y = 2 := ((MulAut.conj g).orderOf_eq y).symm.trans hx2
  exact (marked_centralizer_core_twoCentral y hy hy2).map (MulAut.conj g)

/-- The central cyclic factor has the same marked involution as the quaternion factors. -/
theorem cyclicGenerator_square : cyclicGenerator ^ 2 = commonInvolution := by
  decide +kernel

end CFSG.Quasithin.ChapterI.Section02.ExceptionalCovers.HSLocal.CentralizerRestriction
