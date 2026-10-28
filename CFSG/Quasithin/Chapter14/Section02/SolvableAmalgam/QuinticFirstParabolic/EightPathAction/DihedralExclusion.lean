module

public import CFSG.Quasithin.Chapter14.Section02.SolvableAmalgam.Source
public import CFSG.Quasithin.Chapter14.Section02.RankTwoLocal
public import CFSG.Quasithin.ChapterG.Section02.CentralClosureConsequences
public import Theory.GroupTheory.AmalgamLocalCores
public import Theory.GroupTheory.SymmetricThreeTwoCoreStructure

/-!
# Crossing local cores in the original dihedral quintic branch

Put X=YT, QH=O₂(H) and QX=O₂(X), with both cores embedded in the
original ambient group. A genuine D₁₀ quotient makes QH have index two
in the common Sylow T, as does the cubic quotient for QX. Faithfulness
and local characteristic two exclude equal cores. Consequently the two
cores generate T and their intersection has index four.

The original identity QX=X∩C_G(V) makes QH move the plane V. The G.2.2
commutator bound then gives [V,QH]=[⟨Vᴴ⟩,QH]=Ω₁Z(T), and excludes an
abelian QH. These are reductions for the D₁₀ exclusion; they do not yet
prove that this source branch is impossible. No path-transitivity,
parabolic model, order bound or amalgam-recognition premise is used.

Source: Aschbacher--Smith 14.2.6 and 14.2.20--21, printed pp.982,
988--989; G.2.2, printed p.332. The printed F.1.12(I)(9) numerical
Tits package is not used.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section02.SolvableAmalgam
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open Chapter12.Section08
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
private theorem core_relIndex_sylow (T : Sylow 2 G) (A : Subgroup G)
    (hTA : (T : Subgroup G) ≤ A) (n : ℕ) (hn : 0 < n)
    (hidx : (T : Subgroup G).relIndex A = n)
    (hq : Nat.card (A ⧸ pCore 2 A) = 2 * n) :
    (A.pCoreIn 2).relIndex (T : Subgroup G) = 2 := by
  let S := T.subtype hTA
  have hm := relIndex_mul_index (pCore_isPGroup.le_sylow_of_normal S)
  have hq' : (pCore 2 A).index = 2 * n := hq
  have hi : (S : Subgroup A).index = n := hidx
  rw [hi, hq'] at hm
  have he : (pCore 2 A).relIndex (S : Subgroup A) = 2 :=
    Nat.eq_of_mul_eq_mul_right hn hm
  have hmap : (S : Subgroup A).map A.subtype = (T : Subgroup G) :=
    map_subgroupOf_eq_of_le hTA
  rw [← hmap, pCoreIn, relIndex_map_map_of_injective _ _ A.subtype_injective]
  exact he

private theorem crossing_index_two (S A B : Subgroup G)
    (hA : A ≤ S) (hB : B ≤ S)
    (hiA : A.relIndex S = 2) (hiB : B.relIndex S = 2) (hne : A ≠ B) :
    A ⊔ B = S ∧ (A ⊓ B).relIndex S = 4 ∧ ¬ A ≤ B := by
  have hnot : ¬ A ≤ B := by
    intro hab
    have hm := relIndex_mul_relIndex A B S hab hB
    rw [hiA, hiB] at hm
    have hb : B ≤ A := relIndex_eq_one.mp (by omega : A.relIndex B = 1)
    exact hne (le_antisymm hab hb)
  have hnot' : ¬ B ≤ A := by
    intro hba
    have hm := relIndex_mul_relIndex B A S hba hA
    rw [hiA, hiB] at hm
    exact hnot (relIndex_eq_one.mp (by omega : B.relIndex A = 1))
  have hsup : A ⊔ B = S := by
    have hm := relIndex_mul_relIndex A (A ⊔ B) S le_sup_left (sup_le hA hB)
    rw [hiA] at hm
    have hneq : A.relIndex (A ⊔ B) ≠ 1 := fun he =>
      hnot' (le_sup_right.trans (relIndex_eq_one.mp he))
    have hh : (A ⊔ B).relIndex S = 1 := by
      rcases Nat.prime_mul_iff.mp (hm ▸ Nat.prime_two) with hh | hh
      · exact hh.2
      · exact (hneq hh.2).elim
    exact le_antisymm (sup_le hA hB) (relIndex_eq_one.mp hh)
  have hint : (A ⊓ B).relIndex A = 2 := by
    rw [inf_relIndex_left]
    have hu : B.relIndex A ≤ 2 := by
      simpa only [hiB] using relIndex_le_of_le_right (H := B) hA
        (by rw [hiB]; decide)
    have hp : B.relIndex A ≠ 0 := index_ne_zero_of_finite
    have hn : B.relIndex A ≠ 1 := fun he => hnot (relIndex_eq_one.mp he)
    omega
  have hm := relIndex_mul_relIndex (A ⊓ B) A S inf_le_left hA
  rw [hint, hiA] at hm
  exact ⟨hsup, hm.symm, hnot⟩

/-- The two intrinsic cores cross inside the prescribed Sylow, and the
quintic core moves the original plane. All subgroup maps are literal. -/
theorem source_dihedral_core_configuration
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (H : Subgroup G) (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (hi : (T : Subgroup G).relIndex H = 5)
    (eD : (H ⧸ pCore 2 H) ≃* DihedralGroup 5) :
    let X := sourceResidual M Mc ⊔ (T : Subgroup G)
    let QH := H.pCoreIn 2
    let QX := X.pCoreIn 2
    QH.relIndex (T : Subgroup G) = 2 ∧
      QX.relIndex (T : Subgroup G) = 2 ∧
      QH ⊔ QX = (T : Subgroup G) ∧
      (QH ⊓ QX).relIndex (T : Subgroup G) = 4 ∧
      ¬ QH ≤ centralizer (localModule T M : Set G) := by
  let X := sourceResidual M Mc ⊔ (T : Subgroup G)
  have hTX : (T : Subgroup G) ≤ X := le_sup_right
  have hTH : (T : Subgroup G) ≤ H := hH.1.1.2
  have hQHT : H.pCoreIn 2 ≤ (T : Subgroup G) := by
    simpa only [Sylow.coe_subtype, map_subgroupOf_eq_of_le hTH] using
      pCoreIn_le_sylow H (T.subtype hTH)
  have hQXT : X.pCoreIn 2 ≤ (T : Subgroup G) := by
    simpa only [Sylow.coe_subtype, map_subgroupOf_eq_of_le hTX] using
      pCoreIn_le_sylow X (T.subtype hTX)
  have hiH : (H.pCoreIn 2).relIndex (T : Subgroup G) = 2 := by
    apply core_relIndex_sylow T H hTH 5 (by decide) hi
    exact (Nat.card_congr eD.toEquiv).trans DihedralGroup.nat_card
  obtain ⟨hQX, ⟨eX⟩⟩ := source_residualSylow_quotient hG T hempty hM hu hmany hcard e
  have hiX : (X.pCoreIn 2).relIndex (T : Subgroup G) = 2 := by
    apply core_relIndex_sylow T X hTX 3 (by decide)
      (SymmetricThreeTwoCore.sylow_index_three eX (T.subtype hTX))
    exact (Nat.card_congr eX.toEquiv).trans (by
      simp [Nat.card_eq_fintype_card, Fintype.card_perm, Nat.factorial])
  have hF := (source_hypothesis_F_1_1 hG T hempty hM hu hmany hcard e H hH
    (Or.inl ⟨eD⟩)).1
  have hne : H.pCoreIn 2 ≠ X.pCoreIn 2 := by
    intro heq
    have hnH : H ≤ normalizer (H.pCoreIn 2 : Set G) := H.le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image H (pCore 2 H))
    have hnX : X ≤ normalizer (H.pCoreIn 2 : Set G) := by
      rw [heq]
      exact X.le_normalizer.trans
        (normalizer_le_normalizer_characteristic_image X (pCore 2 X))
    have hc := AmalgamLocalCores.common_normal_eq_bot H X (H.pCoreIn 2)
      (le_inf (pCoreIn_le 2 H) (hQHT.trans hTX)) hnH hnX
      (source_solvable_amalgam_twoCore_eq_bot hG T hempty hM hu hmany hcard e H hH.1.2)
      (hF.local_core_selfCentralizing 0)
    exact (hF.local_twoCore_ne_bot 0) hc
  obtain ⟨hsup, hint, hcross⟩ := crossing_index_two (T : Subgroup G)
    (H.pCoreIn 2) (X.pCoreIn 2) hQHT hQXT hiH hiX hne
  refine ⟨hiH, hiX, hsup, hint, ?_⟩
  intro hc
  apply hcross
  rw [hQX]
  exact le_inf (hQHT.trans hTX) hc

/-- Applying the core movement to the original G.2 setup identifies both
commutators with the original central point. In particular O₂(H) is nonabelian. -/
theorem source_dihedral_core_commutators
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (H : Subgroup G) (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (hi : (T : Subgroup G).relIndex H = 5)
    (eD : (H ⧸ pCore 2 H) ≃* DihedralGroup 5) :
    ⁅localModule T M, H.pCoreIn 2⁆ = centralInvolutions T ∧
      ⁅conjugateSpanBy (localModule T M) H, H.pCoreIn 2⁆ = centralInvolutions T ∧
      ¬ IsMulCommutative (H.pCoreIn 2) := by
  have hmove := (source_dihedral_core_configuration
    hG T hempty hM hu hmany hcard e H hH hi eD).2.2.2.2
  obtain ⟨he, F, hp, _, _, hloc⟩ := source_lemma_14_2_6
    hG T hempty hM hu hmany hcard e
  let := he
  obtain ⟨_, hlocal, _, _, _, _⟩ := hloc H hH.1
  have hc : ⁅conjugateSpanBy (localModule T M) H, H.pCoreIn 2⁆ ≤
      centralInvolutions T := by
    have hh := hlocal.commutator_U_core_le_point
    change ⁅conjugateSpanBy (rankTwoSeed T M) H, H.pCoreIn 2⁆ ≤ F.Vi 1 at hh
    simpa only [rankTwoSeed_eq_localModule, hp] using hh
  have hv : ⁅localModule T M, H.pCoreIn 2⁆ ≤ centralInvolutions T :=
    (commutator_mono (le_conjugateSpanBy _ _) le_rfl).trans hc
  have hne : ⁅localModule T M, H.pCoreIn 2⁆ ≠ ⊥ := by
    intro heq
    exact hmove (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp heq))
  have hvEq : ⁅localModule T M, H.pCoreIn 2⁆ = centralInvolutions T := by
    apply eq_of_le_of_card_ge hv
    rw [plane_centralInvolutions_card T M hM.1.2 hcard e]
    have hcpos := Nat.card_pos (α := (⁅localModule T M, H.pCoreIn 2⁆ : Subgroup G))
    have hcone : Nat.card (⁅localModule T M, H.pCoreIn 2⁆ : Subgroup G) ≠ 1 :=
      fun hh => hne (card_eq_one.mp hh)
    omega
  have huEq : ⁅conjugateSpanBy (localModule T M) H, H.pCoreIn 2⁆ =
      centralInvolutions T := le_antisymm hc (by
    rw [← hvEq]
    exact commutator_mono (le_conjugateSpanBy _ _) le_rfl)
  refine ⟨hvEq, huEq, ?_⟩
  intro hab
  have hU : conjugateSpanBy (localModule T M) H ≤ H.pCoreIn 2 := by
    have hh := hlocal.U_le_core
    change conjugateSpanBy (rankTwoSeed T M) H ≤ H.pCoreIn 2 at hh
    simpa only [rankTwoSeed_eq_localModule] using hh
  apply hne
  exact bot_unique ((commutator_mono ((le_conjugateSpanBy _ _).trans hU) le_rfl).trans
    (commutator_self_eq_bot_iff.mpr hab).le)

end CFSG.Quasithin.Chapter14.Section02.SolvableAmalgam
