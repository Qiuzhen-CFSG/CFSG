module
public import CFSG.Quasithin.Chapter13.Section05.NormalBranch.SourceSixBlock
public import CFSG.Quasithin.Chapter13.Section05.NormalBranch.ReturningPlane.Seed
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.TransvectionModules.Quotients.FiveSeed.BarMarking.Action
public import CFSG.Quasithin.Chapter3.Section02

/-!
# The original maximal local group in 13.5.15(7)

Once O₂(LT) is the original module V, the core sandwich gives O₂(M)=V.
Maximal two-locality and even characteristic identify N_G(V)=M and C_G(V)=V.
The natural A₆ action extends to M through its concrete six-letter linear
normalizer. The image of LT contains A₆ and the action kernel lies in LT,
so [M:LT] divides two. It is also odd because LT contains the original Sylow
subgroup. Hence M=LT, proving clause (7) without assuming equality of actions.

Source: Aschbacher–Smith 13.5.15(7), printed p.921, using 3.2.11 and the
original natural module; the preceding core equality and maximal two-locality
retain their source producers.
-/

@[expose] public section
open Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section05.NormalBranch.SourceMaximalCore
open Section08.SourceCompletion
open Section08.TransvectionQuotients.FiveSeed.BarMarking
variable {G : Type*} [Group G] [Finite G] {D : ChapterF.Section09.Setup G}
  {V₂ M : Subgroup G}
  (d : NaturalSetup D.T D.L D.V D.V₁ V₂ D.Vplus M D.Gz)
  (h : D.Hypothesis) (e : (D.L ⧸ pCore 2 D.L) ≃* alternatingGroup (Fin 6))
  (hseed : D.Vplus = ⁅D.V,D.L₁⁆) (hn : (D.L₁.subgroupOf D.H).Normal)
  (hU : ¬IsMulCommutative D.UH)
include d h e hseed hn hU

/-- Core, normalizer and centralizer equalities retain the original V and M. -/
theorem maximal_core_normalizer (hQ : D.LT.pCoreIn 2 = D.V)
    (hmax : IsMaximalTwoLocal M) :
    M.pCoreIn 2 = D.V ∧ normalizer (D.V : Set G) = M ∧
      centralizer (D.V : Set G) = D.V := by
  let := h.elementary
  have hHM : D.LT ≤ M := by
    rw [d.local_normalizer]
    exact sup_le D.L.le_normalizer d.normalizes_L
  have hVL : D.V ≤ D.L.pCoreIn 2 := by
    rw [←(SourceSixBlock.source13_5_15_four d h e hseed hn hU).2.1]
    exact map_mono (ChapterC.blockU_le_core (L := D.L))
  have hne : D.V ≠ ⊥ := by
    intro hz
    have hc := ReturningPlane.module_card d
    rw [hz,card_bot] at hc
    contradiction
  have hh := Chapter3.Section02.lemma_3_2_11_of_core_containment D.T
    D.L D.LT M D.V le_sup_right hHM (le_sup_left.trans hHM) d.local_normalizer
    hmax (d.counterexample.qtke.evenCharacteristic D.T M hmax
      (le_sup_right.trans hHM)) hQ.symm hVL hne
  exact ⟨hh.1,hh.2.1,hh.2.2.1⟩

omit d h e hseed hn hU in
private theorem full_of_sixLetter_image {P : Type*} [Group P] [Finite P]
    (T : Sylow 2 P) (H : Subgroup P) (hTH : (T : Subgroup P) ≤ H)
    (f : P →* Equiv.Perm (Fin 6)) (hker : f.ker ≤ H)
    (himage : alternatingGroup (Fin 6) ≤ H.map f) : H = ⊤ := by
  have hdiv : H.index ∣ 2 := by
    have hi := (H.dvd_index_map hker).trans (index_dvd_of_le himage)
    simpa only [alternatingGroup.index_eq_two] using hi
  have hodd : ¬ 2 ∣ H.index := fun hh =>
    T.not_dvd_index (hh.trans (index_dvd_of_le hTH))
  apply index_eq_one.mp
  rcases (Nat.dvd_prime Nat.prime_two).mp hdiv with hi | hi
  · exact hi
  · exact (hodd (by rw [hi])).elim

/-- The original natural action extends to all of M with its literal centralizer kernel. -/
theorem maximal_permutation_extension (hQ : D.LT.pCoreIn 2 = D.V)
    (hmax : IsMaximalTwoLocal M) :
    ∃ f : M →* Equiv.Perm (Fin 6),
      (∀ l : D.L, f (inclusion (show D.L ≤ M from by
        rw [d.local_normalizer]; exact D.L.le_normalizer) l) =
        (SourceSixBlock.actor d l).val) ∧
      f.ker = D.V.subgroupOf M := by
  let := h.elementary
  obtain ⟨_,hNV,hCV⟩ := maximal_core_normalizer d h e hseed hn hU hQ hmax
  have hLM : D.L ≤ M := by rw [d.local_normalizer]; exact D.L.le_normalizer
  have hML : M ≤ normalizer (D.L : Set G) := d.local_normalizer.le
  have hMV : M ≤ normalizer (D.V : Set G) := hNV.symm.le
  let a : Additive D.V ≃ₗ[ZMod 2] BinaryPermutation.natural (Fin 6) :=
    d.coordinate.toAdditiveLeft.toLinearEquiv (ZMod.map_smul _)
  obtain ⟨f,hfL,_,hfker⟩ := natural_extension M D.L D.V hLM hML hMV
    (SourceSixBlock.actor d) (SourceSixBlock.actor_surjective d) a
    (fun l v => d.conjugation l v.toMul)
  refine ⟨f,hfL,?_⟩
  rw [hfker,Section08.TransvectionQuotients.FiveSeed.actorKernel,hCV]

/-- Clause (7) of the literal source theorem, after the preceding Q=V conclusion. -/
theorem source13_5_15_seven (hQ : D.LT.pCoreIn 2 = D.V)
    (hmax : IsMaximalTwoLocal M) : M = D.LT ∧ D.V = M.pCoreIn 2 := by
  obtain ⟨hcore,_,_⟩ := maximal_core_normalizer d h e hseed hn hU hQ hmax
  have hHM : D.LT ≤ M := by
    rw [d.local_normalizer]
    exact sup_le D.L.le_normalizer d.normalizes_L
  have hLM : D.L ≤ M := le_sup_left.trans hHM
  obtain ⟨f,hfL,hfker⟩ := maximal_permutation_extension d h e hseed hn hU hQ hmax
  have htop : D.LT.subgroupOf M = ⊤ := by
    apply full_of_sixLetter_image (D.T.subtype (le_sup_right.trans hHM)) _
      (by intro x hx; exact (show (D.T : Subgroup G) ≤ D.LT from le_sup_right) hx) f
    · rw [hfker]
      exact subgroupOf_mono M h.V_le_LT
    · intro a ha
      obtain ⟨l,hl⟩ := SourceSixBlock.actor_surjective d ⟨a,ha⟩
      refine ⟨inclusion hLM l,mem_sup_left l.property,?_⟩
      exact (hfL l).trans (congrArg Subtype.val hl)
  refine ⟨?_,hcore.symm⟩
  apply le_antisymm ?_ hHM
  intro x hx
  have ht : (⟨x,hx⟩ : M) ∈ D.LT.subgroupOf M := by rw [htop]; trivial
  exact ht

end CFSG.Quasithin.Chapter13.Section05.NormalBranch.SourceMaximalCore
end
