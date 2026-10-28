module
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.Recognition.OriginalSolvable
public import CFSG.Quasithin.ChapterG.Section09.FittingRecognition.Four.OrthogonalOrder
public import Theory.GroupTheory.CentralizerSmallKernelTransport

/-!
# The original point normalizer has order prime to five

The solvable source geometry identifies the kernel of the terminal action
with O₂(H) and its quotient with the binary plus-type orthogonal group of
order 72. Consequently the order of H is 72 times a power of two.

For the marked nonidentity point z, H is the literal centralizer C_G(z).
Conjugation preserves centralizer order, so an element centralizing any
subgroup of order divisible by five cannot be conjugate to z. The subgroup
adapter accepts the actual order-960 point centralizer used in source 20.

Source: Aschbacher--Smith 14.3.15 and the second paragraph of the proof
of 14.3.20, printed pp.995 and 997.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section03.NonabelianSource.Recognition
open Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter14.Section02 SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
private theorem point_normalizer_eq_element_centralizer
    {T : Sylow 2 G} {V : Subgroup G} (F : InvariantFlag T V 2)
    (z:G) (hz:z∈F.Vi 1) (hz1:z≠1) : F.H=centralizer ({z}:Set G) := by
  have hc : Nat.card (F.Vi 1)=2 := by simpa using F.card 1 (by decide)
  obtain ⟨u,hu,huniq⟩ := (Nat.card_eq_two_iff' (1:F.Vi 1)).mp hc
  have hzsub : (⟨z,hz⟩:F.Vi 1)≠1 := fun he=>hz1 (congrArg Subtype.val he)
  apply le_antisymm
  · exact (normalizer_le_centralizer_of_card_two (F.Vi 1) hc).trans
      (centralizer_le (Set.singleton_subset_iff.mpr hz))
  · intro x hx
    apply _root_.centralizer_le_normalizer (F.Vi 1)
    intro v hv
    by_cases hv1:v=1
    · simp [hv1]
    have hvsub : (⟨v,hv⟩:F.Vi 1)≠1 := fun he=>hv1 (congrArg Subtype.val he)
    have hvz : v=z := congrArg Subtype.val ((huniq ⟨v,hv⟩ hvsub).trans
      (huniq ⟨z,hz⟩ hzsub).symm)
    rw [hvz]
    exact (mem_centralizer_singleton_iff.mp hx).symm

theorem source_point_fiveFree_of_solvable
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hnot : ¬ ClassificationModels.IsTheoremEModel G)
    (F : InvariantFlag T (rankTwoSeed T M) 2)
    [IsElementaryAbelian 2 (rankTwoSeed T M)]
    (hne : ¬ IsMulCommutative F.U)
    (g : G) (hgP : g∈F.P (sourceResidual M Mc)) (hgH : g∉F.H)
    (hs : Group.IsSolvable F.TerminalHdot) : ¬5∣Nat.card F.H := by
  let h := source_lemma_14_2_4 hG T hempty hM hu hmany hcard e
  obtain ⟨dg,he,_,_,_,_,_⟩ := rankTwo_terminal_hypothesis h F hne g hgP hgH
  let := he
  have hZ := source_center_eq_point_of_solvable
    hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs
  have hr := source_full_orthogonal_of_solvable
    hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs
  have hquot : Nat.card F.TerminalHdot=72 := by
    obtain ⟨a,f,ha⟩ := hr
    exact (Nat.card_congr (a.trans topEquiv).toEquiv).trans
      ChapterG.Section09.FittingRecognition.Four.card_orthogonalFour
  have hindex : F.terminalHatAction.ker.index=72 := hquot
  have hker : F.terminalHatAction.ker=pCore 2 F.H :=
    terminal_kernel_of_center_point F dg hZ
  obtain ⟨n,hn⟩ := (pCore_isPGroup (p:=2) (G:=F.H)).exists_card_eq
  have horder := F.terminalHatAction.ker.index_mul_card
  rw [hindex,hker,hn] at horder
  rw [←horder]
  exact (by decide : Nat.Prime 5).coprime_iff_not_dvd.mp
    ((by decide : Nat.Coprime 5 72).mul_right
      ((by decide : Nat.Coprime 5 2).pow_right n))

theorem source_not_isConj_point_of_five_dvd_centralizer
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hnot : ¬ ClassificationModels.IsTheoremEModel G)
    (F : InvariantFlag T (rankTwoSeed T M) 2)
    [IsElementaryAbelian 2 (rankTwoSeed T M)]
    (hne : ¬ IsMulCommutative F.U)
    (g : G) (hgP : g∈F.P (sourceResidual M Mc)) (hgH : g∉F.H)
    (hs : Group.IsSolvable F.TerminalHdot)
    (z d:G) (hz:z∈F.Vi 1) (hz1:z≠1)
    (hd:5∣Nat.card (centralizer ({d}:Set G))) : ¬IsConj z d := by
  intro hconj
  obtain ⟨x,rfl⟩ := isConj_iff.mp hconj
  have hc := Nat.card_congr
    (CentralizerSmallKernelTransport.centralizerEquiv (MulAut.conj x) z).toEquiv
  change Nat.card (centralizer ({z}:Set G))=
    Nat.card (centralizer ({x*z*x⁻¹}:Set G)) at hc
  rw [←hc,←point_normalizer_eq_element_centralizer F z hz hz1] at hd
  exact source_point_fiveFree_of_solvable
    hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs hd

theorem source_not_isConj_point_of_five_dvd_subgroup
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hnot : ¬ ClassificationModels.IsTheoremEModel G)
    (F : InvariantFlag T (rankTwoSeed T M) 2)
    [IsElementaryAbelian 2 (rankTwoSeed T M)]
    (hne : ¬ IsMulCommutative F.U)
    (g : G) (hgP : g∈F.P (sourceResidual M Mc)) (hgH : g∉F.H)
    (hs : Group.IsSolvable F.TerminalHdot)
    (z d:G) (hz:z∈F.Vi 1) (hz1:z≠1)
    (D:Subgroup G) (hD:D≤centralizer ({d}:Set G)) (hd:5∣Nat.card D) :
    ¬IsConj z d := by
  exact source_not_isConj_point_of_five_dvd_centralizer
    hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs z d hz hz1
    (hd.trans (card_dvd_of_le hD))

end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.Recognition
