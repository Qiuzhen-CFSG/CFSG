module

public import CFSG.Quasithin.ChapterA.Section02.MinimalReduction.PrimeCore.OddCore
public import Theory.GroupTheory.GeneralizedFitting.SemisimpleQuasisimpleImage
public import Theory.SpecificGroups.SL2.OddCoreAndRank
public import GorensteinWalter.SL2ProjectiveCover

/-!
# Excluding a prime-field SL₂ image of the minimal counterexample

The original covering kernel lies in the odd core. Every homomorphism onto
odd-characteristic SL₂ kills that core, so it factors through the given
semisimple section. That section has odd center, and a quasisimple image
of it must again have odd center, contradicting the scalar involution of SL₂.

Source: the rank-two action step of Aschbacher–Smith A.2.12, printed p.36.
Only the original minimal-covering hypotheses are used.
-/

public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterA.Section02
universe u
variable {K : GroupClass.{u}} {G S : Type u}
    [Group G] [Group S] [Finite G] [Finite S] {p : ℕ}

theorem CounterexampleToTheoremA.section_center_odd_card
    (h : CounterexampleToTheoremA K G S p) (ih : TheoremAOnProperSections K G) :
    Odd (Nat.card (center S)) := by
  obtain ⟨f, hf⟩ := h.exists_surjective ih
  have hm : ((center S).comap f).map f = center S :=
    map_comap_eq_self_of_surjective hf _
  have hdvd := ((center S).comap f).card_map_dvd f
  rw [hm] at hdvd
  exact (h.center_preimage_odd_card ih f hf).of_dvd_nat hdvd

theorem CounterexampleToTheoremA.not_surjective_SL2
    (h : CounterexampleToTheoremA K G S p) (ih : TheoremAOnProperSections K G)
    {r : ℕ} [Fact r.Prime] (hr : 3 < r)
    (g : G →* SL(2, ZMod r)) : ¬ Function.Surjective g := by
  intro hg
  let : Fact (3 < Nat.card (ZMod r)) := ⟨by simpa using hr⟩
  let : IsQuasisimple SL(2, ZMod r) := {
    toIsPerfect := GorensteinWalter.sl2_isPerfect_of_card_gt_three _ (by simpa using hr)
    simple := Matrix.ProjectiveSpecialLinearGroup.rank_two_simple (by rw [Nat.card_zmod]; omega) }
  have hr2 : (2 : ZMod r) ≠ 0 := GorensteinWalter.two_ne_zero_of_odd_card _
    (by simpa using (Fact.out : r.Prime).odd_of_ne_two (by omega))
  have hoddmap : (pPrimeCore 2 G).map g = ⊥ := by
    apply le_bot_iff.mp
    rw [← Matrix.SpecialLinearGroup.pPrimeCore_two_eq_bot hr2]
    exact le_sSup ⟨Normal.map inferInstance g hg,
      pPrimeCore_coprime_card.of_dvd_right ((pPrimeCore 2 G).card_map_dvd g)⟩
  have hoddk : pPrimeCore 2 G ≤ g.ker := (map_eq_bot_iff (pPrimeCore 2 G)).mp hoddmap
  obtain ⟨f, hf⟩ := h.exists_surjective ih
  have hker : f.ker ≤ g.ker := by
    apply le_trans _ hoddk
    rw [← h.center_preimage_eq_oddCore ih f hf]
    intro x hx
    change f x ∈ center S
    rw [show f x = 1 from hx]
    exact one_mem _
  let e := QuotientGroup.quotientKerEquivOfSurjective f hf
  let d : S →* SL(2, ZMod r) := (QuotientGroup.lift f.ker g hker).comp e.symm.toMonoidHom
  have hdf : d.comp f = g := by
    apply MonoidHom.ext
    intro x
    change QuotientGroup.lift f.ker g hker (e.symm (f x)) = g x
    rw [show e.symm (f x) = QuotientGroup.mk' f.ker x from
      e.symm_apply_apply (QuotientGroup.mk' f.ker x)]
    rfl
  have hd : Function.Surjective d := by
    intro y
    obtain ⟨x, hx⟩ := hg y
    exact ⟨f x, (DFunLike.congr_fun hdf x).trans hx⟩
  have hcenter := odd_center_of_quasisimple_image_of_semisimple
    h.2.2.2.1 (h.section_center_odd_card ih) d hd
  have hneg : (-1 : SL(2, ZMod r)) ∈ center SL(2, ZMod r) := by
    apply mem_center_iff.mpr
    intro x
    simp
  exact hcenter.not_two_dvd_nat (by
    simpa only [Matrix.SpecialLinearGroup.orderOf_neg_one_eq_two hr2] using
      (center SL(2, ZMod r)).orderOf_dvd_natCard hneg)

end CFSG.Quasithin.ChapterA.Section02
