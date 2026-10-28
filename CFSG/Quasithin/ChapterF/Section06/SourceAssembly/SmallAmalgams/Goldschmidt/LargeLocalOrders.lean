module

public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.SmallAmalgams.Goldschmidt.LargeLocalQuotients
public import Theory.GroupTheory.SelfCentralizingNormalFourRecognition
public import Theory.GroupTheory.SymmetricFourNormalFour
public import Theory.GroupTheory.NormalCenterQuotient

/-!
# Local orders in Goldschmidt's large residual branch

The local S₃ quotient and self-centralizing two-core force an order greater
than twenty-four after excluding an alternating-four residual. Indeed, a
smaller two-core has order one or two and is central. At order twenty-four,
the self-centralizing normal four-group recognizes S₄ and hence its A₄
residual. Conjugation carries the resulting bound to every actual vertex.

This is the local order input to the even-singularity exclusion in
Goldschmidt, *Automorphisms of trivalent graphs* (1980), (4.3), p.393.
-/

public section
open Subgroup Theory.GroupTheory
open Subgroup.CosetGeometry
namespace CFSG.Quasithin.ChapterF.SourceAssembly.Goldschmidt

private theorem order_gt_twentyFour {H : Type*} [Group H] [Finite H]
    (e : (H ⧸ pCore 2 H) ≃* Equiv.Perm (Fin 3))
    (hcent : centralizer (pCore 2 H : Set H) ≤ pCore 2 H)
    (hA : ¬ Nonempty (pResidual 2 H ≃* alternatingGroup (Fin 4))) :
    24 < Nat.card H := by
  by_contra! hsmall
  have hc := SymmetricThreeTwoCore.card_eq e
  have hle : Nat.card (pCore 2 H) ≤ 4 := by omega
  have hcases : Nat.card (pCore 2 H) = 1 ∨ Nat.card (pCore 2 H) = 2 ∨
      Nat.card (pCore 2 H) = 4 := by
    obtain ⟨n, hn⟩ := (pCore_isPGroup (p := 2) (G := H)).exists_card_eq
    have hnle : n ≤ 2 := by
      by_contra! hgt
      have hpow : 2 ^ 3 ≤ 2 ^ n := Nat.pow_le_pow_right (by decide) (by omega)
      norm_num at hpow
      omega
    interval_cases n <;> simp_all
  have hfour : Nat.card (pCore 2 H) = 4 := by
    rcases hcases with h1 | h2 | h4
    · have hbot := Subgroup.card_eq_one.mp h1
      have ht : centralizer (pCore 2 H : Set H) = ⊤ :=
        centralizer_eq_top_iff_subset.mpr
          (by rw [hbot]; exact (bot_le : (⊥ : Subgroup H) ≤ center H))
      have he : pCore 2 H = ⊤ := top_unique (ht ▸ hcent)
      have hcard : Nat.card (pCore 2 H) = Nat.card H := by rw [he, card_top]
      omega
    · have hz := central_of_normal_card_two (pCore 2 H) h2
      have ht : centralizer (pCore 2 H : Set H) = ⊤ :=
        centralizer_eq_top_iff_subset.mpr hz
      have he : pCore 2 H = ⊤ := top_unique (ht ▸ hcent)
      have hcard : Nat.card (pCore 2 H) = Nat.card H := by rw [he, card_top]
      omega
    · exact h4
  have hcard : Nat.card H = 24 := by omega
  obtain ⟨f⟩ := mulEquiv_perm_four_of_selfCentralizing_normal_four
    (pCore 2 H) pCore_isPGroup hfour hcent hcard
  exact hA (twoResidual_equiv_alternatingFour_of_equiv f)

variable {G : Type*} [Group G] {F : Bool → Subgroup G}

/-- Each original endpoint group has order greater than twenty-four in
the branch excluding the cubic and alternating-four residuals. -/
theorem CubicTreeAction.local_card_gt_twentyFour_of_large_residual
    (h : CubicTreeAction F)
    (hC : ∀ i, ¬ Nonempty ((pResidual 2 (F i)) ≃* Multiplicative (ZMod 3)))
    (hA : ∀ i, ¬ Nonempty ((pResidual 2 (F i)) ≃* alternatingGroup (Fin 4)))
    (i : Bool) : 24 < Nat.card (F i) := by
  let : Finite (F i) := h.finite i
  obtain ⟨e⟩ := h.local_quotient_symmetricThree_of_large_residual hC hA i
  have hc := h.stabilizer_centralizer_twoCore_le_of_large_residual hC hA (base F i)
  rw [show RankTwo.stabilizer F (base F i) = F i from stabilizer_base F i] at hc
  exact order_gt_twentyFour e hc (hA i)

/-- The same bound on every literal vertex stabilizer, including vertices
away from the original edge in the infinite completion. -/
theorem CubicTreeAction.stabilizer_card_gt_twentyFour_of_large_residual
    (h : CubicTreeAction F)
    (hC : ∀ i, ¬ Nonempty ((pResidual 2 (F i)) ≃* Multiplicative (ZMod 3)))
    (hA : ∀ i, ¬ Nonempty ((pResidual 2 (F i)) ≃* alternatingGroup (Fin 4)))
    (v : RankTwo.Vertex F) : 24 < Nat.card (RankTwo.stabilizer F v) := by
  obtain ⟨g, hg⟩ := exists_smul_base F v
  have he := Nat.card_congr (MulAction.stabilizerEquivStabilizer hg.symm).toEquiv
  change Nat.card (RankTwo.stabilizer F (base F v.type)) =
    Nat.card (RankTwo.stabilizer F v) at he
  rw [show RankTwo.stabilizer F (base F v.type) = F v.type from stabilizer_base F v.type] at he
  rw [← he]
  exact h.local_card_gt_twentyFour_of_large_residual hC hA v.type

end CFSG.Quasithin.ChapterF.SourceAssembly.Goldschmidt
