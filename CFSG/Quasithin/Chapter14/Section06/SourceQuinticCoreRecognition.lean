module

public import CFSG.Quasithin.Chapter14.Section06.SourceQuinticKernelStructure
public import CFSG.Quasithin.Chapter14.Section06.SourceQuinticCoreClass
public import CFSG.Quasithin.Chapter14.Section02.SolvableAmalgam.QuinticFirstParabolic
public import CFSG.Quasithin.Chapter14.Section02.SolvableAmalgam.QuinticSecondParabolic
public import CFSG.Quasithin.Chapter14.Section02.SolvableAmalgam.QuinticEnumeration
public import CFSG.Quasithin.Chapter14.Section02.SolvableAmalgam.TitsCompletion

/-!
# Full Frattini layers and recognition of the actual 512-core branch

The reciprocal Frattini argument gives the full core layers and the exact
kernel/core pairs (32,512) or (64,1024). In the first case the full kernel
equals the elementary span. The existing intrinsic first-parabolic theorem
then constructs a genuine endpoint isomorphism from the original source
hypotheses. The proved second-endpoint and overlap theorems construct a
compatible Tits marking, and the ambient recognition theorem applies.

The unconditional conclusion retains the other pair exactly, together
with its full Frattini quotient and endpoint orders. No identification of
that branch with FullRee is inferred from its orders or core layers.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section06
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open Section02.SolvableAmalgam
variable {G : Type*} [Group G] [Finite G]

/-- The actual order-512 branch has elementary full kernel and a genuine
marked Tits amalgam, yielding recognition of the original ambient group. -/
theorem source_quintic_core512_recognition
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃*
      Equiv.Perm (Fin 3))
    (H : Subgroup G) (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (hi : (T : Subgroup G).relIndex H = 5)
    (h512 : Nat.card (H.pCoreIn 2) = 512) :
    let X := sourceResidual M Mc ⊔ (T : Subgroup G)
    let U := conjugateSpanBy (localModule T M) H
    let Q := H.pCoreIn 2
    let C := H ⊓ centralizer (U : Set G)
    C = U ∧ frattini C = ⊥ ∧
      (center Q).map Q.subtype = centralInvolutions T ∧
      (Subgroup.upperCentralSeries Q 2).map Q.subtype = U ∧
      Nat.card (Q ⧸ frattini Q) = 16 ∧
      Nonempty (Tits.ExceptionalParabolics.first ≃* H) ∧
      Nonempty (Tits.ExceptionalParabolics.second ≃* X) ∧
      ChapterF.GreenBook.IsAtlasTitsAmalgam
        (RankTwoAmalgam.ofSubgroups H (H ⊓ X) X inf_le_left inf_le_right) ∧
      H = Mc ∧ M = X ∧ H = centralizer (centralInvolutions T : Set G) ∧
      Nat.card (T : Subgroup G) = 2048 ∧ Nat.card H = 10240 ∧
      Nat.card X = 6144 ∧ Nat.card (pCore 2 X) = 1024 ∧
      Nonempty ((X ⧸ pCore 2 X) ≃* Equiv.Perm (Fin 3)) ∧
      Nonempty (G ≃* Tits.ParrottGroup) ∧ ClassificationModels.IsTheoremEModel G := by
  let U := conjugateSpanBy (localModule T M) H
  let Q := H.pCoreIn 2
  let C := H ⊓ centralizer (U : Set G)
  let : IsElementaryAbelian 2 U :=
    (source_index_five_closure_structure hG T hempty hM hu hmany hcard e H hH.1 hi).1
  obtain ⟨_, horders, _, hderived, _⟩ := source_quintic_full_kernel_structure
    hG T hempty hM hu hmany hcard e H hH hi
  have hCcard : Nat.card C = 32 := by
    rcases horders with ⟨hc, _⟩ | ⟨_, hq⟩
    · exact hc
    · omega
  have hUcard : Nat.card U = 32 :=
    (source_quintic_span_card_and_core_radical hG T hempty hM hu hmany hcard e H hH hi).1
  have hUC : U ≤ C := le_inf
    ((hderived.ge.trans (commutator_le_self Q)).trans (pCoreIn_le 2 H)) (le_centralizer U)
  have hCU : C = U := (eq_of_le_of_card_ge hUC (by rw [hCcard, hUcard])).symm
  have hPhiC : frattini C = ⊥ := by
    rw [hCU]
    let : Fact (IsPGroup 2 U) := ⟨IsElementaryAbelian.isPGroup 2 U⟩
    exact frattini_eq_bot_of_isElementaryAbelian (p := 2)
  have hupper : Nat.card (pCore 2 H) ≤ 512 := by
    rw [← card_map_of_injective (K := pCore 2 H) H.subtype_injective]
    exact h512.le
  have hcenter := QuinticFirstParabolic.source_core512_core_center
    hG T hempty hM hu hmany hcard e H hH hi hupper
  obtain ⟨_, _, hupperCenter, hPhiIndex⟩ := QuinticFirstParabolic.source_core512_characteristic_layers
    hG T hempty hM hu hmany hcard e H hH hi hupper
  obtain ⟨hfirst, hHMc, hMX, hHZ, hTcard, hXcard, hXcore, hXquot⟩ :=
    source_quintic_data_of_core_upper_bound hG T hempty hM hu hmany hcard e H hH hi hupper
  have hsecond := QuinticSecondParabolic.source_second_parabolic
    hG T hempty hM hu hmany hcard e H hH hi hfirst
  have hmark := source_quintic_tits_of_endpoint_equivalences
    hG T hempty hM hu hmany hcard e H hH hi hfirst.some hsecond.some
  have hrecognition := source_tits_recognition
    hG T hempty hM hu hmany hcard e H hH hmark
  have hHcard : Nat.card H = 10240 :=
    (Nat.card_congr hfirst.some.symm.toEquiv).trans Tits.ExceptionalParabolics.first_card
  exact ⟨hCU, hPhiC, hcenter, hupperCenter, hPhiIndex, hfirst, hsecond,
    hmark, hHMc, hMX, hHZ, hTcard, hHcard, hXcard, hXcore, hXquot,
    hrecognition, .tits hrecognition⟩

/-- Unconditional full Frattini and core structure, with genuine recognition
of the 512 branch and the exact unresolved 64/1024 branch retained. -/
theorem source_quintic_full_phi_and_recognition
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃*
      Equiv.Perm (Fin 3))
    (H : Subgroup G) (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (hi : (T : Subgroup G).relIndex H = 5) :
    let X := sourceResidual M Mc ⊔ (T : Subgroup G)
    let U := conjugateSpanBy (localModule T M) H
    let Q := H.pCoreIn 2
    let C := H ⊓ centralizer (U : Set G)
    IsElementaryAbelian 2 U ∧ Nat.card U = 32 ∧ IsMulCommutative C ∧
      (frattini C).map C.subtype ≤ centralInvolutions T ∧
      ⁅Q,Q⁆ = U ∧ (frattini Q).map Q.subtype = U ∧
      ⁅⁅Q,Q⁆,Q⁆ = centralInvolutions T ∧
      Group.nilpotencyClass Q = 3 ∧ Monoid.exponent Q = 4 ∧
      ((Nat.card C = 32 ∧ Nat.card Q = 512 ∧ C = U ∧ frattini C = ⊥ ∧
        (center Q).map Q.subtype = centralInvolutions T ∧
        (Subgroup.upperCentralSeries Q 2).map Q.subtype = U ∧
        Nat.card (Q ⧸ frattini Q) = 16 ∧
        Nonempty (Tits.ExceptionalParabolics.first ≃* H) ∧
        Nonempty (Tits.ExceptionalParabolics.second ≃* X) ∧
        ChapterF.GreenBook.IsAtlasTitsAmalgam
          (RankTwoAmalgam.ofSubgroups H (H ⊓ X) X inf_le_left inf_le_right) ∧
        H = Mc ∧ M = X ∧ H = centralizer (centralInvolutions T : Set G) ∧
        Nat.card (T : Subgroup G) = 2048 ∧ Nat.card H = 10240 ∧
        Nat.card X = 6144 ∧ Nat.card (pCore 2 X) = 1024 ∧
        Nonempty ((X ⧸ pCore 2 X) ≃* Equiv.Perm (Fin 3)) ∧
        Nonempty (G ≃* Tits.ParrottGroup) ∧ ClassificationModels.IsTheoremEModel G) ∨
       (Nat.card C = 64 ∧ Nat.card Q = 1024 ∧
        Nat.card (Q ⧸ frattini Q) = 32 ∧
        Nat.card (T : Subgroup G) = 4096 ∧ Nat.card H = 20480)) := by
  let U := conjugateSpanBy (localModule T M) H
  let Q := H.pCoreIn 2
  let C := H ⊓ centralizer (U : Set G)
  obtain ⟨hCcomm, horders, hPhiC, hderived, hPhiQ⟩ := source_quintic_full_kernel_structure
    hG T hempty hM hu hmany hcard e H hH hi
  have hUcard := (source_quintic_span_card_and_core_radical
    hG T hempty hM hu hmany hcard e H hH hi).1
  have hthird := (source_quintic_full_core_layers hG T hempty hM hu hmany hcard e H hH hi).2.2
  obtain ⟨hclass, hexp⟩ := source_quintic_full_core_class_and_exponent
    hG T hempty hM hu hmany hcard e H hH hi
  refine ⟨(source_index_five_closure_structure hG T hempty hM hu hmany hcard e H hH.1 hi).1,
    hUcard, hCcomm, hPhiC, hderived, hPhiQ, hthird, hclass, hexp, ?_⟩
  rcases horders with ⟨hC32, hQ512⟩ | ⟨hC64, hQ1024⟩
  · exact Or.inl ⟨hC32, hQ512, source_quintic_core512_recognition
      hG T hempty hM hu hmany hcard e H hH hi hQ512⟩
  · have hPhiCard : Nat.card (frattini Q) = 32 := by
      rw [← card_map_of_injective Q.subtype_injective, hPhiQ]
      exact hUcard
    have hPhiIndex : Nat.card (Q ⧸ frattini Q) = 32 := by
      have hh := (frattini Q).card_mul_index
      rw [index_eq_card, hPhiCard, hQ1024] at hh
      omega
    obtain ⟨_, ⟨eSuz⟩⟩ := source_quintic_suzuki_zero_quotient
      hG T hempty hM hu hmany hcard e H hH hi
    have hquot : Nat.card (H ⧸ pCore 2 H) = 20 :=
      (Nat.card_congr eSuz.toEquiv).trans BenderSuzuki.MatrixGroups.suzukiZero_card
    have hQcard : Nat.card (pCore 2 H) = 1024 :=
      (card_map_of_injective H.subtype_injective).symm.trans hQ1024
    have hHcard : Nat.card H = 20480 := by
      have hh := (pCore 2 H).card_mul_index
      rw [index_eq_card, hQcard, hquot] at hh
      exact hh.symm
    have hTcard : Nat.card (T : Subgroup G) = 4096 := by
      have hh := relIndex_mul_card_of_le hH.1.1.2
      rw [hi, hHcard] at hh
      omega
    exact Or.inr ⟨hC64, hQ1024, hPhiIndex, hTcard, hHcard⟩

/-- Outside the Theorem E models, only the exact large kernel/core pair
can remain. This does not identify that pair with the FullRee model. -/
theorem source_quintic_nonmodel_exact_large_core
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃*
      Equiv.Perm (Fin 3))
    (H : Subgroup G) (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (hi : (T : Subgroup G).relIndex H = 5)
    (hnomodel : ¬ ClassificationModels.IsTheoremEModel G) :
    let U := conjugateSpanBy (localModule T M) H
    let Q := H.pCoreIn 2
    Nat.card (H ⊓ centralizer (U : Set G) : Subgroup G) = 64 ∧
      Nat.card Q = 1024 ∧ Nat.card (Q ⧸ frattini Q) = 32 ∧
      Nat.card (T : Subgroup G) = 4096 ∧ Nat.card H = 20480 := by
  obtain ⟨_, _, _, _, _, _, _, _, _, hcases⟩ := source_quintic_full_phi_and_recognition
    hG T hempty hM hu hmany hcard e H hH hi
  rcases hcases with hsmall | hlarge
  · obtain ⟨_, h512, _⟩ := hsmall
    have hfirst := source_quintic_core512_recognition
      hG T hempty hM hu hmany hcard e H hH hi h512
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hmodel⟩ := hfirst
    exact (hnomodel hmodel).elim
  · exact hlarge

end CFSG.Quasithin.Chapter14.Section06
