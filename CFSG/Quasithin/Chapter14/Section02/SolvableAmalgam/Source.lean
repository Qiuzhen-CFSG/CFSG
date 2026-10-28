module
public import CFSG.Quasithin.Chapter14.Section02.ResidualSylow
public import CFSG.Quasithin.Chapter3.Section01.LocalGeometry
public import CFSG.Quasithin.ChapterF.Section01.SourceIncidence
public import Theory.GroupTheory.SylowSmallCoreQuotient
public import Theory.GroupTheory.SpecificGroups.SLTwoPermThree
public import Theory.SpecificGroups.SL2.BinaryProjective
public import BenderSuzuki.MatrixGroups.SuzukiZero
/-!
# The genuine source amalgam in 14.2.20

For an actual minimal outside subgroup H with quotient D₁₀, Sz(2), or S₃,
put X = YT for the residual Y of 14.1.18. The plane source identifies
X/O₂(X) with S₃. The small quotient orders make both Sylow normalizers
equal to T, and give H ∩ X = T. Original even characteristic and the
core-free amalgam calculation then establish all six clauses of the
corrected F.1.1 hypothesis on the literal pair (H, X).

This constructs the input to the amalgam classification; it does not assume
or assert its classification conclusion. Source: Aschbacher--Smith 14.2.20,
printed pp.988--989, and F.1.1, printed p.255.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section02.SolvableAmalgam
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]

@[expose] def SmallSolvableModel (H : Type*) [Group H] : Prop :=
  Nonempty (H ≃* DihedralGroup 5) ∨
    Nonempty (H ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup 0) ∨
    Nonempty (H ≃* Equiv.Perm (Fin 3))

private theorem rankOne_of_permThree {H : Type*} [Group H]
    (e : H ≃* Equiv.Perm (Fin 3)) : ChapterF.Source.IsRankOneModel H := by
  apply ChapterF.Source.IsRankOneModel.linear 1 (by decide)
  refine ⟨ZMod 2,inferInstance,inferInstance,by simp,?_⟩
  exact ⟨e.trans (SLTwoPermThree.sl2Two_equiv_perm_three.some.symm.trans
    Matrix.SpecialLinearGroup.sl2TwoEquivPSL2Two)⟩

theorem SmallSolvableModel.rankOne {H : Type*} [Group H] (h : SmallSolvableModel H) :
    ChapterF.Source.IsRankOneModel H := by
  exact h.elim (fun hh => .dihedral hh) (fun hh => hh.elim
    (fun hhh => .suzuki 0 hhh) (fun hhh => rankOne_of_permThree hhh.some))

theorem SmallSolvableModel.card {H : Type*} [Group H] (h : SmallSolvableModel H) :
    Nat.card H = 6 ∨ Nat.card H = 10 ∨ Nat.card H = 20 := by
  apply h.elim
  · intro hd
    exact Or.inr (Or.inl ((Nat.card_congr hd.some.toEquiv).trans (by rw [DihedralGroup.nat_card])))
  · intro hs
    apply hs.elim
    · intro hz
      exact Or.inr (Or.inr ((Nat.card_congr hz.some.toEquiv).trans BenderSuzuki.MatrixGroups.suzukiZero_card))
    · intro ht
      exact Or.inl ((Nat.card_congr ht.some.toEquiv).trans (by
        simp [Nat.card_eq_fintype_card,Fintype.card_perm,Nat.factorial]))

private theorem relative_sylow_normalizer (T : Sylow 2 G) (H : Subgroup G)
    (hTH : (T : Subgroup G) ≤ H)
    (hc : Nat.card (H ⧸ pCore 2 H) = 6 ∨ Nat.card (H ⧸ pCore 2 H) = 10 ∨
      Nat.card (H ⧸ pCore 2 H) = 20) : H ⊓ normalizer (T : Set G) = T := by
  have hn := (sylow_normalizer_small_core_quotient (T.subtype hTH) hc).1
  have hm := congrArg (Subgroup.map H.subtype) hn
  change (normalizer ((T : Subgroup G).subgroupOf H : Set H)).map H.subtype =
    ((T : Subgroup G).subgroupOf H).map H.subtype at hm
  rw [←subgroupOf_normalizer_eq hTH,subgroupOf_map_subtype,map_subgroupOf_eq_of_le hTH,
    inf_comm] at hm
  exact hm

private theorem small_intersection (T : Sylow 2 G) {M H : Subgroup G}
    (hTM : (T : Subgroup G) ≤ M)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (hc : Nat.card (H ⧸ pCore 2 H) = 6 ∨ Nat.card (H ⧸ pCore 2 H) = 10 ∨
      Nat.card (H ⧸ pCore 2 H) = 20) : H ⊓ M = T := by
  have hTH : (T : Subgroup G) ≤ H := hH.1.1.2
  have he := (sylow_normalizer_small_core_quotient (T.subtype hTH) hc).2
    (M.subgroupOf H) (fun x hx => hTM hx) (lt_top_iff_ne_top.mpr (by
      intro ht
      apply hH.1.2
      intro x hx
      exact show (⟨x,hx⟩ : H) ∈ M.subgroupOf H from ht.ge (mem_top _)))
  have hm := congrArg (Subgroup.map H.subtype) he
  rw [subgroupOf_map_subtype,Sylow.coe_subtype,map_subgroupOf_eq_of_le hTH,inf_comm] at hm
  exact hm

/-- Construct all six original F.1.1 clauses for the actual 14.2.20 pair. -/
theorem source_hypothesis_F_1_1
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃*
      Equiv.Perm (Fin 3))
    (H : Subgroup G) (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (hq : SmallSolvableModel (H ⧸ pCore 2 H)) :
    let X := sourceResidual M Mc ⊔ (T : Subgroup G)
    ChapterF.Source.HypothesisF11 ![H,X] (T : Subgroup G) ∧
      H ⊓ X = T ∧
      H ⊓ normalizer (T : Set G) = T ∧ X ⊓ normalizer (T : Set G) = T ∧
      (T : Subgroup G) ≤ normalizer (sourceResidual M Mc : Set G) ∧
      Nat.card (centralInvolutions T) = 2 ∧ H ≤ centralizer (centralInvolutions T : Set G) := by
  classical
  let X := sourceResidual M Mc ⊔ (T : Subgroup G)
  have hXM : X ≤ M := sup_le (sourceResidual_le _ _) hM.1.2
  have hTX : (T : Subgroup G) ≤ X := le_sup_right
  obtain ⟨hcore,⟨eX⟩⟩ := source_residualSylow_quotient hG T hempty hM hu hmany hcard e
  have hXcard : Nat.card (X ⧸ pCore 2 X) = 6 :=
    (Nat.card_congr eX.toEquiv).trans (by simp [Nat.card_eq_fintype_card,Fintype.card_perm,Nat.factorial])
  have hNH := relative_sylow_normalizer T H hH.1.1.2 hq.card
  have hNX := relative_sylow_normalizer T X hTX (Or.inl hXcard)
  have hHM := small_intersection T hM.1.2 hH hq.card
  have hHX : H ⊓ X = (T : Subgroup G) := le_antisymm
    ((inf_le_inf_left H hXM).trans_eq hHM) (le_inf hH.1.1.2 hTX)
  have hXH : X ∈ Chapter1.HOver G (T : Set G) :=
    Chapter3.mem_HOver_of_sylow_interval T hTX hXM
      ⟨Chapter1.mem_H_of_isTwoLocal hM.1.1.1,hM.1.2⟩
  have hfit (A : Subgroup G) (hA : A ∈ Chapter1.HOver G (T : Set G)) :
      generalizedFitting A = pCore 2 A :=
    generalizedFitting_eq_pCore_of_selfCentralizing 2
      (Chapter1.mem_He_iff.mp (Chapter1.lemma_1_1_4_6 T (hG.evenCharacteristic T) hA))
  let L : Fin 2 → Subgroup G := ![H,X]
  have hLi (i : Fin 2) : (T : Subgroup G) ≤ L i := by
    fin_cases i
    · exact hH.1.1.2
    · exact hTX
  have hB (i : Fin 2) : ChapterF.Source.borel (L i) (T : Subgroup G) = T := by
    change L i ⊓ normalizer ((T : Subgroup G) ⊓ L i : Subgroup G) = T
    rw [inf_eq_left.mpr (hLi i)]
    fin_cases i
    · exact hNH
    · exact hNX
  have hP (i : Fin 2) : ChapterF.Source.parabolic L (T : Subgroup G) i = L i := by
    change L i ⊔ (T : Subgroup G) ⊔ ChapterF.Source.borel (L (ChapterF.Source.other i)) _ = L i
    rw [hB,sup_eq_left.mpr (hLi i),sup_eq_left.mpr (hLi i)]
  have hgen : ChapterF.Source.generated L (T : Subgroup G) = H ⊔ X := by
    change H ⊔ X ⊔ (T : Subgroup G) = H ⊔ X
    exact sup_eq_left.mpr (hTX.trans le_sup_right)
  have hF : ChapterF.Source.HypothesisF11 L (T : Subgroup G) := by
    refine ⟨inferInstance,T.isPGroup',?_,?_,?_,?_,?_,?_⟩
    · intro i
      exact (hLi i).trans (L i).le_normalizer
    · intro i
      refine ⟨T.subtype (hLi i),?_⟩
      rw [Sylow.coe_subtype,map_subgroupOf_eq_of_le (hLi i),inf_eq_left.mpr (hLi i)]
    · intro i
      fin_cases i
      · exact hq.rankOne
      · exact rankOne_of_permThree eX
    · intro i
      rw [hB]
      exact (hLi i).trans (L i).le_normalizer
    · rw [hgen]
      exact source_solvable_amalgam_twoCore_eq_bot hG T hempty hM hu hmany hcard e H hH.1.2
    · intro i
      rw [hP]
      fin_cases i
      · exact hfit H hH.1.1
      · exact hfit X hXH
  refine ⟨hF,hHX,hNH,hNX,?_,plane_centralInvolutions_card T M hM.1.2 hcard e,
    (source_lemma_14_2_3 hG T hempty hM hu hmany hcard e H hH.1.1 hH.1.2).2⟩
  exact hM.1.2.trans ((normal_subgroupOf_iff_le_normalizer (sourceResidual_le M Mc)).mp
    (residualY_normal M Mc))

end CFSG.Quasithin.Chapter14.Section02.SolvableAmalgam
