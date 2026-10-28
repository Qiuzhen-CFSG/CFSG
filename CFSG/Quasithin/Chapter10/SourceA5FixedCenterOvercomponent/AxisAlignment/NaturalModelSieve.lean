module
public import CFSG.Quasithin.Chapter2.Section04.SmallBlocks.AlternatingTerminal.FullSylow
public import CFSG.Quasithin.Chapter2.Section04.SmallBlocks.AlternatingTerminal.BinaryFive
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.AlternatingFiveDeletedMathieu
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.AlternatingFiveDeletedHS
public import CFSG.Quasithin.Chapter10.SourceA5FixedCenterOvercomponent.AxisAlignment.NaturalSimple

/-!
# The remaining simple carriers for the original deleted-five block

The literal block, its full Sylow and its local C-component condition exclude
all Lie-type and alternating rows of Theorem C. Canonical layer normalizers
supply the Mathieu and binary-five exclusions without a Sylow order bound.
The precise remainder consists of the four large sporadic carriers; their
local structure remains a separate input to the original normalizer argument.

Source: Aschbacher–Smith 10.2.1, printed p.743, inspecting A.3.14.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10.FixedCenterOvercomponent.DeletedModelSieve
open ChapterC ChapterA.Section03.SourceEmbeddings
open Chapter2.AlternatingTerminal
open Chapter13.Section05.NormalBranch.DeletedFive
variable {X : Type*} [Group X] [Finite X]

private theorem no_invariant_escape (T : Sylow 2 X) (A N : Subgroup X)
    (hlocal : A ∈ ChapterA.Section03.localCComponents T)
    (hn : (T : Subgroup X) ≤ normalizer (A : Set X)) (hAN : A ≤ N)
    (hInv : ∀ a : MulAut X, ((blockU A).map A.subtype).map a.toMonoidHom =
      (blockU A).map A.subtype → N.map a.toMonoidHom = N)
    (hbad : ∀ Q : Sylow 2 N, A.subgroupOf N ∉ ChapterA.Section03.localCComponents Q) :
    False := by
  have hTN : (T : Subgroup X) ≤ normalizer (N : Set X) := by
    intro t ht
    apply mem_normalizer_iff_map_conj_eq.mpr
    apply hInv
    exact mem_normalizer_iff_map_conj_eq.mp
      ((hn.trans (normalizer_le_normalizer_characteristic_image A (blockU A))) ht)
  let J := N ⊔ (T : Subgroup X)
  have hNJ : N ≤ J := le_sup_left
  obtain ⟨Q,hQ⟩ := (T.subtype (show (T : Subgroup X) ≤ J from le_sup_right)).exists_map_subtype_eq_inf_of_normalizes hNJ
    (sup_le N.le_normalizer hTN)
  have hQT : (Q : Subgroup N) = (T : Subgroup X).subgroupOf N := by
    apply map_injective N.subtype_injective
    rw [hQ,subgroupOf_map_subtype]
    have ht : ((T.subtype (show (T : Subgroup X) ≤ J from le_sup_right) : Sylow 2 J) : Subgroup J).map J.subtype = T :=
      map_subgroupOf_eq_of_le le_sup_right
    rw [ht,inf_comm]
  exact hbad Q (hQT.symm ▸ local_restrict hlocal hAN)

omit [Finite X] in
private theorem no_normalizer_escape (T : Sylow 2 X) (A : Subgroup X)
    (hlocal : A ∈ ChapterA.Section03.localCComponents T)
    (hn : (T : Subgroup X) ≤ normalizer (A : Set X))
    (hbad : ∀ Q : Sylow 2 (normalizer ((blockU A).map A.subtype : Set X)),
      A.subgroupOf (normalizer ((blockU A).map A.subtype : Set X)) ∉
      ChapterA.Section03.localCComponents Q) : False := by
  let N := normalizer ((blockU A).map A.subtype : Set X)
  have hAN : A ≤ N := A.le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image A (blockU A))
  have hTN : (T : Subgroup X) ≤ N := hn.trans
    (normalizer_le_normalizer_characteristic_image A (blockU A))
  exact hbad (T.subtype hTN) (local_restrict hlocal hAN)


private theorem no_binary_five (T : Sylow 2 X) (A : Subgroup X)
    (hA : IsAlternatingBlock A 5) (hc : Nat.card ((blockU A).map A.subtype) = 16)
    (hl : A ∈ ChapterA.Section03.localCComponents T)
    (hn : (T : Subgroup X) ≤ normalizer (A : Set X))
    (hm : ClassicalGroup.IsPSL X 5 2) : False := by
  obtain ⟨F,_,_,hF,⟨a⟩⟩ := hm
  let : Fintype F := Fintype.ofFinite F
  let b : F ≃+* ZMod 2 := FiniteField.ringEquivOfCardEq (by
    simpa only [← Nat.card_eq_fintype_card,Nat.card_zmod] using hF)
  let e : X ≃* BinaryLinear.OuterCyclic.LinearGroup 5 :=
    (a.trans (Atlas.fieldEquivPSL 5 b)).trans
      (BinaryLinear.OuterCyclic.projectiveEquivLinear (by decide : 0 < 5))
  let B := A.map e.toMonoidHom
  have hB : IsAlternatingBlock B 5 :=
    RankOne.Solvable.isAlternatingBlock_of_equiv (e.subgroupMap A) hA
  have hBc : Nat.card ((blockU B).map B.subtype) = 16 := by
    rw [blockU_image_of_injective_restriction A e.toMonoidHom
      (e.injective.comp A.subtype_injective),card_map_of_injective e.injective]
    exact hc
  obtain ⟨hN,_,hbad⟩ := binary_five_normalizer_obstruction B hB hBc
  obtain ⟨_,hbad'⟩ := normalizer_obstruction_of_equiv e A hN hbad
  exact no_normalizer_escape T A hl hn hbad'

/-- The exact large-sporadic remainder; no bound on the full Sylow is assumed. -/
theorem simple_model_remaining [IsSimpleGroup X] [Group.IsPerfect X]
    (T : Sylow 2 X) (A : Subgroup X) (hA : IsAlternatingBlock A 5)
    (hl : A ∈ ChapterA.Section03.localCComponents T)
    (hn : (T : Subgroup X) ≤ normalizer (A : Set X))
    (hm : ChapterA.Section02.IsTheoremCModel X) :
    ∃ name : ClassificationModels.SporadicName,
      (name = .m24 ∨ name = .j4 ∨ name = .he ∨ name = .ru) ∧
      Nonempty (X ≃* name.Carrier) := by
  have hc : Nat.card ((blockU A).map A.subtype) = 16 :=
    (card_map_of_injective A.subtype_injective).trans hA.blockU_card
  let := hA.2.1.elementary
  have hE : IsElementaryAbelian 2 ((blockU A).map A.subtype) := IsElementaryAbelian.map _
  cases hm with
  | alternating n hnum he => exact (not_alternating_of_alternatingFive A hA hc hnum he.some).elim
  | odd hm => exact (not_oddModel_of_elementary_sixteen _ hE hc hm).elim
  | bender hm => exact (bender_no_alternating_five_block hm A hA).elim
  | linear_binary n hnum hm =>
    rcases hnum with rfl | rfl
    · exact (not_psl4Two_of_alternatingFive A hA hc hm).elim
    · exact (no_binary_five T A hA hc hl hn hm).elim
  | rank_two f hm =>
    have hr : Chapter1.Section02.LocalModels.RankTwoTheoremC X := by
      cases hm with
      | linear hf hm => exact .linear f hf hm
      | symplectic hf hm => exact .symplectic f hf hm
      | g2 hf hm => exact .g2 f hf hm
      | triality hf hm => exact .triality f hf hm
      | ree_f4 m hm _ he =>
        obtain ⟨e⟩ := he
        exact (no_alternatingFive_of_reeF4_equiv hm e A hA hc).elim
      | symplectic_derived _ he => exact .symplectic_derived he
      | g2_derived _ he => exact .g2_derived he
      | tits _ he => exact .tits he
    obtain ⟨N,_,hAN,hInv,hbad⟩ := rank_two_invariant_obstruction hr A hA hc
    exact (no_invariant_escape T A N hl hn hAN hInv hbad).elim
  | sporadic hm =>
    rcases hm with ⟨name,hne,⟨e⟩⟩ | ⟨e⟩
    · cases name with
      | m11 => exact (small_sporadic_no_alternating_five_block .m11 (Or.inl rfl) e A hA hc).elim
      | m12 => exact (small_sporadic_no_alternating_five_block .m12 (Or.inr (Or.inl rfl)) e A hA hc).elim
      | j2 => exact (small_sporadic_no_alternating_five_block .j2 (Or.inr (Or.inr rfl)) e A hA hc).elim
      | j3 => exact (hne rfl).elim
      | m22 => exact (alternatingFiveDeleted_not_m22 e T A hA hl hn).elim
      | m23 => exact (alternatingFiveDeleted_not_m23 e T A hA hl hn).elim
      | m24 => exact ⟨.m24,by simp,⟨e⟩⟩
      | j4 => exact ⟨.j4,by simp,⟨e⟩⟩
      | hs => exact (alternatingFiveDeleted_not_hs e T A hA hn).elim
      | he => exact ⟨.he,by simp,⟨e⟩⟩
      | ru => exact ⟨.ru,by simp,⟨e⟩⟩
    · obtain ⟨e⟩ := e
      have hd := card_dvd_of_alternatingFive A hA hc
      rw [Nat.card_congr e.toEquiv,Janko1.card_model] at hd
      exact ((by decide : ¬960 ∣ 175560) hd).elim

end CFSG.Quasithin.Chapter10.FixedCenterOvercomponent.DeletedModelSieve
