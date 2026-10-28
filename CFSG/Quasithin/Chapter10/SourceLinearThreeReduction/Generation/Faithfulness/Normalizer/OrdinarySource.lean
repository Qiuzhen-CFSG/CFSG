module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.Faithfulness.Normalizer.CoveringSource
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.Faithfulness.Normalizer.OrdinaryModels

/-!
# The original covering counterexample after ordinary model exclusion

The actual intersection component retains its inclusion-compatible
quotient L/O₂(L). Its center is trivial by nonnormality of the original
T-action. The ordinary dispatcher leaves only J₄ and Held
central quotients, preserving every ambient, radical and module premise.
The second theorem applies this to the literal elementary Hall kernel.

These are reductions, not covering uniqueness or Hall faithfulness.
The remaining ordinary rows, module fixation and odd-normalizer cases
remain obligations of this task.
Source: Aschbacher--Smith 4.2.12 and 4.4.6--7, pp.610,620, applied
in 10.2.3(2), p.745.
-/

public section
open Subgroup Theory.GroupTheory
open scoped Pointwise
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02 Chapter4 Chapter4.Section02.Unitary
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)

theorem source_nonnormal_covering_ordinary_models
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    {I : Subgroup G} (hIM : I ≤ D.maximalLocal)
    (hcover : (localOrbit T L : Set G) ⊆
      (I : Set G) * ((localOrbit T L).pCoreIn 2 : Set G))
    (hcore : I.pCoreIn 2 ≠ ⊥)
    (horbit : componentOrbit L I = localOrbit T L)
    (hnot : ¬ UniqueMaximalOvergroup I D.maximalLocal) :
    ∃ (J H : Subgroup G)
      (S : Sylow 2 (sectionCentralizerIn D.maximalLocal (localOrbit T L))),
      let LH := (solvableResidual (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype
      PushLE (localOrbit T L) I J ∧ IsMaximalTwoLocal H ∧ J ≤ H ∧
      H ⊓ D.maximalLocal < H ∧
      ChapterC.HypothesisC28 KnownSimple.IsKnownSimple H (H ⊓ D.maximalLocal)
        LH (J.pCoreIn 2)
        (fullModule (localOrbit T L)
          ((S : Subgroup (sectionCentralizerIn D.maximalLocal (localOrbit T L))).map
            (sectionCentralizerIn D.maximalLocal (localOrbit T L)).subtype)) ∧
      ¬ H ⊓ D.maximalLocal ≤ normalizer (LH : Set G) ∧
      (∃ eH : (LH ⧸ pCore 2 LH) ≃* (L ⧸ pCore 2 L),
        ∀ x : LH, eH (QuotientGroup.mk' (pCore 2 LH) x) =
          QuotientGroup.mk' (pCore 2 L)
            ⟨x.val, ((map_subtype_le _).trans inf_le_left) x.property⟩) ∧
      ∃ K : Subgroup H, IsComponent H K ∧
        ¬ K ≤ (H ⊓ D.maximalLocal).subgroupOf H ∧
        ChapterC.HypothesisC28.SimpleOrdinaryRemainder (K ⧸ center K) := by
  obtain ⟨J,H,S,hpush,hH,hJH,hlt,hC,hnorm,⟨e,he⟩,K,hK,hout⟩ :=
    source_nonnormal_covering_ordinary_remainder D hn hIM hcover hcore horbit hnot
  let LH := (solvableResidual (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype
  let := D.quasisimple
  let : IsQuasisimple (LH ⧸ pCore 2 LH) := IsQuasisimple.of_mulEquiv e.symm
  have hz : center (LH ⧸ pCore 2 LH) = ⊥ := by
    apply bot_unique
    intro x hx
    have hx' := (centerCongr e ⟨x,hx⟩).property
    have he : e x = 1 := (source_nonnormal_component_core_center D hn).le hx'
    exact e.map_eq_one_iff.mp he
  exact ⟨J,H,S,hpush,hH,hJH,hlt,hC,hnorm,⟨e,he⟩,K,hK,hout,
    hC.nonnormal_simple_ordinary_models hz hnorm K hK⟩

theorem source_hall_kernel_twoCore_ordinary_models
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    {H : Subgroup G} (Y : Subgroup H)
    (hfix : Y.map H.subtype ⊓ sectionCentralizer (localOrbit T L) ≤
      centralizer (D.fullModule : Set G))
    {p : ℕ} [Fact p.Prime] (hp : Odd p)
    (A : Subgroup G) (hA : IsElementaryAbelian p A)
    (hAY : A ≤ Y.map H.subtype) (hAC : A ≤ sectionCentralizer (localOrbit T L))
    (hAT : (A : Set G) * (T : Set G) = (T : Set G) * (A : Set G))
    (hout : ¬ normalizer (A : Set G) ≤ D.maximalLocal)
    (hcore : pCore 2 (normalizer (A : Set G)) ≠ ⊥) :
    ∃ (J X : Subgroup G)
      (S : Sylow 2 (sectionCentralizerIn D.maximalLocal (localOrbit T L))),
      let LX := (solvableResidual (L ⊓ X : Subgroup G)).map (L ⊓ X).subtype
      X ⊓ D.maximalLocal < X ∧
      ChapterC.HypothesisC28 KnownSimple.IsKnownSimple X (X ⊓ D.maximalLocal)
        LX (J.pCoreIn 2)
        (fullModule (localOrbit T L)
          ((S : Subgroup (sectionCentralizerIn D.maximalLocal (localOrbit T L))).map
            (sectionCentralizerIn D.maximalLocal (localOrbit T L)).subtype)) ∧
      ¬ X ⊓ D.maximalLocal ≤ normalizer (LX : Set G) ∧
      ∃ K : Subgroup X, IsComponent X K ∧
        ¬ K ≤ (X ⊓ D.maximalLocal).subgroupOf X ∧
        ChapterC.HypothesisC28.SimpleOrdinaryRemainder (K ⧸ center K) := by
  let := hA
  have hodd : Odd (Nat.card A) := by
    obtain ⟨n,he⟩ := (IsElementaryAbelian.isPGroup p A).exists_card_eq
    rw [he]
    exact hp.pow
  have hAV : A ≤ centralizer (D.fullModule : Set G) := (le_inf hAY hAC).trans hfix
  let F := (solvableResidual (localOrbit T L ⊓ centralizer (A : Set G) : Subgroup G)).map
    (localOrbit T L ⊓ centralizer (A : Set G)).subtype
  let I := F ⊔ ((T : Subgroup G) ⊓ normalizer (A : Set G))
  obtain ⟨hIM,hIN,hcover,hIcore⟩ := source_oddActor_normalizerJoin_input D A hAC hodd hAV
  have hIo : componentOrbit L I = localOrbit T L := by
    apply le_antisymm
    · exact iSup_conjugates_le_of_le_normalizer _ _ _ (le_componentOrbit L T) hIM
    · apply (source_oddPrimeActor_normalizer_orbit D hp A
        (IsElementaryAbelian.isPGroup p A) hAC hAT).symm.le.trans
      exact iSup_le fun t => le_iSup_of_le
        (⟨t,(show (T : Subgroup G) ⊓ normalizer (A : Set G) ≤ I from le_sup_right)
          t.property⟩ : I) le_rfl
  have hnot : ¬ UniqueMaximalOvergroup I D.maximalLocal := by
    intro hu
    obtain ⟨N,hN,hAN⟩ := exists_maximalTwoLocal_overgroup_of_twoCore_ne_bot
      (normalizer (A : Set G)) hcore
    exact hout ((hu.2.2 N hN (hIN.trans hAN)) ▸ hAN)
  obtain ⟨J,X,S,_,_,_,hlt,hC28,hnorm,_,hK⟩ :=
    source_nonnormal_covering_ordinary_models D hn hIM hcover hIcore hIo hnot
  exact ⟨J,X,S,hlt,hC28,hnorm,hK⟩

end CFSG.Quasithin.Chapter10
