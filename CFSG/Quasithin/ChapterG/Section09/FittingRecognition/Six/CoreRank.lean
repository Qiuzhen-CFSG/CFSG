module
public import Theory.Representation.BinarySixThreeRank
public import Theory.GroupTheory.PrimeRankInvolutionLift
public import Theory.GroupTheory.PGroup.AbelianIndexThreeStructure
public import CFSG.Quasithin.ChapterG.Section09.FittingRecognition.ThreeCore.Source
import Mathlib.Tactic

/-!
# The elementary rank-three alternative in G.9.4

The original faithful degree-six action bounds the three-core rank by
three. If it exceeds two, its elementary rank witness has order 27.
The ambient linear order bounds the three-core order by 81, making the
witness normal with index one or three. The cubic source rank lower bound
therefore gives rank two or this literal normal elementary 27-group.

The characteristic property of that group, its three binary weight planes,
and the normalizer exclusions remain separate source obligations. This
module does not assert the final rank-two bound from normality alone.

Source: Aschbacher--Smith G.9.4, printed p.355.
-/

open Subgroup
namespace CFSG.Quasithin.ChapterG.Section09.FittingRecognition
variable {G V : Type*} [Group G] [Finite G]
  [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]

/-- The actual three-core in the cubic degree-six source branch has rank
at most three, and rank three supplies its elementary 27-group. -/
public theorem source_six_threeCore_rank_le_three
    {K : GroupClass} {ρ : Representation (ZMod 2) G V} {A : Subgroup G}
    (h : FittingHypothesis K ρ A 2)
    (hd : Module.finrank (ZMod 2) V = 6) :
    primeRank 3 (pCore 3 G) ≤ 3 := by
  exact (primeRank_subgroup_le 3 (pCore 3 G)).trans
    (Representation.BinarySixThreeRank.primeRank_three_le_three ρ h.faithful hd.le)

public theorem source_six_rank_three_has_elementary_twentyseven
    {K : GroupClass} {ρ : Representation (ZMod 2) G V} {A : Subgroup G}
    (h : FittingHypothesis K ρ A 2)
    (hd : Module.finrank (ZMod 2) V = 6)
    (hr : 2 < primeRank 3 (pCore 3 G)) :
    ∃ E : Subgroup (pCore 3 G), IsElementaryAbelian 3 E ∧ Nat.card E = 27 := by
  obtain ⟨E,hE,hEc⟩ := exists_elementaryAbelian_card_primeRank (G := pCore 3 G) (p := 3)
  refine ⟨E,hE,?_⟩
  have hu := source_six_threeCore_rank_le_three h hd
  have heq : primeRank 3 (pCore 3 G) = 3 := by omega
  simpa only [heq,show (3:ℕ)^3=27 by decide] using hEc

/-- The actual faithful degree-six action bounds the three-core order by 81. -/
public theorem source_six_threeCore_card_le_eightyone
    {K : GroupClass} {ρ : Representation (ZMod 2) G V} {A : Subgroup G}
    (h : FittingHypothesis K ρ A 2)
    (hd : Module.finrank (ZMod 2) V = 6) :
    Nat.card (pCore 3 G) ≤ 81 := by
  have hBdiv : Nat.card (pCore 3 G) ∣ 20158709760 := by
    let Vmul := Multiplicative V
    let : Finite V := Module.finite_of_finite (ZMod 2)
    let : IsElementaryAbelian 2 Vmul := Representation.BinaryGroupAction.elementary
    let := Representation.BinaryGroupAction.action ρ
    let f : G →* MulAut Vmul := MulDistribMulAction.toMulAut G Vmul
    have hf : Function.Injective f := by
      intro g k he
      apply h.faithful
      ext v
      exact congrArg Multiplicative.toAdd
        (MulEquiv.congr_fun he (Multiplicative.ofAdd v))
    have hV : Nat.card Vmul ≤ 64 := by
      change Nat.card V ≤ 64
      rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod, hd]
      decide
    exact (card_dvd_of_injective (f.comp (pCore 3 G).subtype)
      (hf.comp (pCore 3 G).subtype_injective)).trans
      (card_mulAut_dvd_of_elementary_card_le_sixtyfour hV)
  obtain ⟨n,hn⟩ := (pCore_isPGroup (p := 3) (G := G)).exists_card_eq
  have hnle : n ≤ 4 := by
    by_contra hh
    have hbad : 3 ^ 5 ∣ 20158709760 :=
      (pow_dvd_pow 3 (by omega : 5 ≤ n)).trans (hn ▸ hBdiv)
    norm_num at hbad
  rw [hn]
  exact Nat.pow_le_pow_right (by decide : 0 < 3) hnle

/-- Above rank two, the elementary 27-group has index at most three in
the actual three-core, hence is normal there. -/
public theorem source_six_large_rank_normal_elementary_twentyseven
    {K : GroupClass} {ρ : Representation (ZMod 2) G V} {A : Subgroup G}
    (h : FittingHypothesis K ρ A 2)
    (hd : Module.finrank (ZMod 2) V = 6)
    (hr : 2 < primeRank 3 (pCore 3 G)) :
    ∃ E : Subgroup (pCore 3 G), IsElementaryAbelian 3 E ∧
      Nat.card E = 27 ∧ E.Normal ∧
      (E = ⊤ ∨ Nat.card (pCore 3 G) = 81) := by
  obtain ⟨E,hE,hEc⟩ := source_six_rank_three_has_elementary_twentyseven h hd hr
  obtain ⟨n,hn⟩ := (pCore_isPGroup (p := 3) (G := G)).exists_card_eq
  have hnle : n ≤ 4 := by
    have hb := source_six_threeCore_card_le_eightyone h hd
    rw [hn] at hb
    exact (Nat.pow_le_pow_iff_right (by decide : 1 < 3)).mp hb
  have hnge : 3 ≤ n := by
    have hcard := E.card_subgroup_dvd_card
    rw [hEc,hn] at hcard
    by_contra hh
    have : n ≤ 2 := by omega
    have hsmall := Nat.pow_le_pow_right (by decide : 0 < 3) this
    norm_num at hsmall
    exact (Nat.le_of_dvd (pow_pos (by decide : 0 < 3) n) hcard).not_gt (by omega)
  have hnalt : n = 3 ∨ n = 4 := by omega
  rcases hnalt with h3 | h4
  · have hB : Nat.card (pCore 3 G) = 27 := by rw [hn,h3]; decide
    have htop : E=⊤ := Subgroup.eq_top_of_card_eq E (by rw [hEc,hB])
    let : E.Normal := htop ▸ inferInstance
    exact ⟨E,hE,hEc,inferInstance,Or.inl htop⟩
  · have hB : Nat.card (pCore 3 G) = 81 := by rw [hn,h4]; decide
    have hi : E.index = 3 := by
      have hc := E.card_mul_index
      rw [hEc,hB] at hc
      omega
    let : E.Normal := normal_of_index_three_of_isPGroup pCore_isPGroup E hi
    exact ⟨E,hE,hEc,inferInstance,Or.inr hB⟩

/-- The original cubic source hypotheses leave rank two or a literal
normal elementary 27-group in the three-core. Its characteristic property
and monomial normalizer are the remaining rank-three source step. -/
public theorem source_six_threeCore_rank_alternative
    {K : GroupClass} {ρ : Representation (ZMod 2) G V} {A : Subgroup G}
    (h : FittingHypothesis K ρ A 2)
    (hc : IsPGroup 3 (⁅fittingSubgroup G,A⁆ : Subgroup G))
    (hd : Module.finrank (ZMod 2) V = 6) :
    primeRank 3 (pCore 3 G) = 2 ∨
      ∃ E : Subgroup (pCore 3 G), IsElementaryAbelian 3 E ∧
        Nat.card E = 27 ∧ E.Normal ∧
        (E = ⊤ ∨ Nat.card (pCore 3 G) = 81) := by
  have hl := (threeCoreData_from_source h (by decide) hc).core_rank_ge
  by_cases heq : primeRank 3 (pCore 3 G) = 2
  · exact Or.inl heq
  · exact Or.inr (source_six_large_rank_normal_elementary_twentyseven h hd (by omega))

end CFSG.Quasithin.ChapterG.Section09.FittingRecognition
