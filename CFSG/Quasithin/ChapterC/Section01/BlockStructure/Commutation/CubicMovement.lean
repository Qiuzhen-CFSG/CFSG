module
public import CFSG.Quasithin.ChapterC.Section01.BlockStructure.Commutation.CubicSetup
public import Theory.GroupTheory.PResidual.CommutatorImage
public import Theory.GroupTheory.Commutator.NormalizesSupplement

/-!
# Thompson movement of a cubic block

If a two-subgroup normalizing a cubic block commutes with it modulo the
ambient two-core, adjoining that core gives a two-group normalized by the
block. The short-group core-action theorem then forces centralization of
its elementary layer. Consequently actual movement makes the quotient
commutator the full cubic group; two-perfection lifts this equality.

Source: Aschbacher--Smith C.1.26--28, printed pp.132--134.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterC
variable {G : Type*} [Group G] [Finite G]

/-- Movement of the cubic block layer forces generation by the same actor. -/
theorem IsBlock.eq_commutator_of_cubic_movement {R J : Subgroup G}
    (hR : IsBlock R) (hq : Nat.card (R ⧸ pCore 2 R) = 3)
    (hJ : IsPGroup 2 J) (hn : J ≤ normalizer (R : Set G))
    (hm : ¬ J ≤ centralizer ((blockU R).map R.subtype : Set G)) :
    R = ⁅R,J⁆ := by
  let q := QuotientGroup.mk' (pCore 2 G)
  have hr : Nat.card (R.map q) = 3 :=
    (Nat.card_congr (BlockCommutation.coreQuotientEquiv R hR.subnormal).toEquiv).symm.trans hq
  have hnq : J.map q ≤ normalizer (R.map q : Set _) :=
    (map_mono hn).trans (R.le_normalizer_map q)
  have hle : ⁅R.map q,J.map q⁆ ≤ R.map q :=
    le_normalizer_iff_commutator_le_left.mp hnq
  have hcne : ⁅R.map q,J.map q⁆ ≠ ⊥ := by
    intro hz
    have hc : ⁅J,R⁆ ≤ pCore 2 G := by
      rw [commutator_comm, ← map_commutator, Subgroup.map_eq_bot_iff,
        QuotientGroup.ker_mk'] at hz
      exact hz
    let Q := J ⊔ pCore 2 G
    have hpQ : IsPGroup 2 Q := hJ.to_sup_of_normal_right pCore_isPGroup
    have hRQ : R ≤ normalizer (Q : Set G) :=
      le_normalizer_sup_of_commutator_le J R J (pCore 2 G) le_rfl hc
    have hQR : Q ≤ normalizer (R : Set G) := sup_le hn
      (le_normalizer_of_isSubnormal_isPPerfect R _ hR.subnormal hR.short.twoPerfect
        pCore_isPGroup le_normalizer_of_normal)
    exact hm (le_sup_left.trans (hR.short.normalizing_twoGroup_centralizes_blockU hpQ hRQ hQR))
  have he : ⁅R.map q,J.map q⁆ = R.map q := by
    have hd := card_dvd_of_le hle
    rw [hr] at hd
    rcases (Nat.dvd_prime Nat.prime_three).mp hd with hb | ht
    · exact (hcne (card_eq_one.mp hb)).elim
    · exact eq_of_le_of_card_ge hle (by rw [ht,hr])
  exact eq_commutator_of_isPPerfect_of_map_eq R J hR.short.twoPerfect hn q
    (by rw [QuotientGroup.ker_mk']; exact pCore_isPGroup) he.symm
end CFSG.Quasithin.ChapterC
