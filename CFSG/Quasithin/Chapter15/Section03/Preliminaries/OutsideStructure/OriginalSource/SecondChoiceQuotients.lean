module
public import CFSG.Quasithin.Chapter15.Section03.Preliminaries.SelectedSource
public import CFSG.Quasithin.Chapter15.Section03.Preliminaries.OutsideStructure.LocalBranches.QuotientTheta.SecondChoice
public import CFSG.Quasithin.Chapter15.Section03.Preliminaries.ResidualStructure.OriginalSource
/-!
# The literal second-choice rank-two quotients

Original 15.3.7 and the selected 15.3.11 Sylow subgroup supply the two
second-choice quotient alternatives. The rank-two Frattini quotient rules
out the S3 alternative by order divisibility. Hence the chosen residual
has elementary order-nine core quotient, and its join with S has the
literal S3-by-S3 quotient by O2, without an additional quotient premise.

Source: Aschbacher--Smith 15.3.7, 15.3.10 and 15.3.11(5), pp.1122--1124.
-/

set_option backward.isDefEq.respectTransparency false
public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section03.OutsideStructure
open LocalBranches.QuotientTheta
variable {G : Type*} [Group G] [Finite G]
theorem source_rankTwo_secondChoice_quotients
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (d : CharacteristicTwo.LocalData G)
    (hempty : MainForward.faithfulLocalComponents d.T = ∅)
    (hM : ChapterA.Section05To06.IsOrderingMaximal d.T d.M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions d.T : Set G)) = {d.Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (d.T : Subgroup G)).ncard)
    {I : Subgroup G} (hI : I ∈ d.Hplus) (htwo : RankTwoCase d I)
    (hsecond : SecondChoice d) :
    Nonempty ((d.Yplus ⧸ pCore 2 d.Yplus) ≃* Multiplicative (Fin 2 → ZMod 3)) ∧
    Nonempty (((d.Yplus ⊔ d.S : Subgroup G) ⧸ pCore 2 (d.Yplus ⊔ d.S : Subgroup G)) ≃*
      (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3))) := by
  obtain ⟨hne,_,_⟩ := InitialSource.UniformControl.source_controls_of_ordering_maximal
    hG d.T hempty hM hu hmany (d.action.card_centralInvolutions d.T d.sylow_le)
  have h7 := source_lemma_15_3_7_of_orthogonal_action hG d.T hempty d.action hM hu hmany hne
  have h11 := source_lemma_15_3_11_from_selection hG d hempty hM hu hmany I hI
  have hh := second_choice_quotient_and_core d I hI hsecond
    (earlier_three_alternatives_of_source d h7.2.2.2.2.2.2) h7.1 h7.2.2.2.2.2.1 h11.sylow
  rcases hh with ⟨⟨e⟩,_⟩ | ⟨hE,hP,_⟩
  · obtain ⟨a⟩ := htwo.2.1
    let A := (d.Yplus ⊔ d.S : Subgroup G)
    have hc : pCore 2 A ≤ coreFrattiniSubgroup A := by
      intro x hx
      change QuotientGroup.mk' (pCore 2 A) x ∈ frattini (A ⧸ pCore 2 A)
      have hxq : QuotientGroup.mk' (pCore 2 A) x = 1 :=
        (QuotientGroup.eq_one_iff (N := pCore 2 A) x).mpr hx
      rw [hxq]
      exact one_mem _
    have hd : Nat.card (A ⧸ coreFrattiniSubgroup A) ∣ Nat.card (A ⧸ pCore 2 A) := by
      simpa only [index_eq_card] using Subgroup.index_dvd_of_le hc
    rw [Nat.card_congr a.toEquiv,Nat.card_congr e.toEquiv] at hd
    norm_num [Nat.card_prod, Nat.card_perm, Nat.card_fin, Fintype.card_perm, Fintype.card_fin, Nat.factorial] at hd
  · exact ⟨hE,hP⟩
end CFSG.Quasithin.Chapter15.Section03.OutsideStructure
