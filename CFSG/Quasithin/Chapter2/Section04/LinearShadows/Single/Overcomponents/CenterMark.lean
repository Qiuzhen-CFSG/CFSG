module
public import CFSG.Quasithin.Chapter2.Section04.LinearShadows.Single.Overcomponents.SmallModels
public import Theory.SpecificGroups.PSL3Even.TwoRank
public import Theory.ElementaryAbelian.EightQuotientRank
/-!
# The center marking in the PSL₃(4) overcomponent

The original elementary core has order64. Its image in PSL₃(4) has order at
most16, so the central kernel has order at least4. Containment in the original
block center, already of order4, gives equality with that same marked center.
Source: Aschbacher–Smith 2.4.11, printed p.532.
-/
public section
open Subgroup Theory.GroupTheory
open CFSG.Quasithin.ChapterC
open CFSG.Quasithin.Chapter2.LinearShadows.Single.Overcomponents
namespace CFSG.Quasithin.Chapter2.LinearShadows.Single.Overcomponents
variable {L K : Type*} [Group L] [Group K] [Finite L] [Finite K]
lemma center_eq_map_of_psl_three_four {n : ℕ} (h : IsL2EvenBlock L n)
    (hc : pCore 2 L = blockU L) (hz : Nat.card (center L) = 2^n)
    (f : L →* K) (hf : Function.Injective f)
    (e : (K ⧸ center K) ≃* Matrix.PSL3Four.PSL)
    (hZ : center K ≤ (center L).map f) :
    n = 2 ∧ center K = (center L).map f := by
  have hn := degree_two_of_psl_three_four h hc f hf e
  subst n
  norm_num at hz
  let := h.2.1.elementary
  let E := (blockU L).map f
  let : IsElementaryAbelian 2 E := IsElementaryAbelian.map f (A := blockU L)
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (center K))
  have hq : q.ker = center K := by
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective, QuotientGroup.ker_mk']
  have hZE : center K ≤ E := hZ.trans (map_mono (h.center_le_module hc))
  have hfixed : Nat.card (blockFixed L) = Nat.card (center L) :=
    Nat.card_congr (subgroupOfEquivOfLe (h.center_le_module hc)).toEquiv
  have hE : Nat.card E = 64 := by
    rw [card_map_of_injective hf,card_eq_card_quotient_mul_card_subgroup (blockFixed L), hfixed,hz]
    rw [show Nat.card (blockU L ⧸ blockFixed L) = 2^(2*2) from h.module_card]
    norm_num
  have hr : primeRank 2 Matrix.PSL3Four.PSL ≤ 4 := by
    rw [Matrix.PSL3Even.two_rank Matrix.PSL3Four.F (n := 2) (by decide)
      (by simpa using Matrix.PSL3Four.card_F)]
  have hm : Nat.card (E.map q) ≤ 16 :=
    (primeRank_le_iff_elementary_card_le Matrix.PSL3Four.PSL).mp hr _ (IsElementaryAbelian.map q)
  have hh := IsElementaryAbelian.card_inf_ker_mul_card_map E q
  rw [hq, inf_eq_right.mpr hZE,hE] at hh
  have hsmall : Nat.card (center K) ≤ 4 := by
    have hh := card_le_of_le hZ
    rwa [card_map_of_injective hf,hz] at hh
  have hbig : 4 ≤ Nat.card (center K) := by nlinarith
  exact ⟨rfl,eq_of_le_of_card_ge hZ (by rw [card_map_of_injective hf,hz]; exact hbig)⟩
end CFSG.Quasithin.Chapter2.LinearShadows.Single.Overcomponents
