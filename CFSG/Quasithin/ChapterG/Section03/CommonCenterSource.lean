module

public import CFSG.Quasithin.ChapterG.Section03.TwoCore
public import Mathlib.GroupTheory.Schreier

/-!
# G.3.1 from an actual common-center subgroup

A subgroup of order greater than two fixing a nonzero vector and moving
every vector only along its binary line supplies the genuine root-rank
input on the whole orbit. The trivial-two-core source theorem then gives
the full actions and the internal orbit decompositions.

Source application: Aschbacher--Smith12.7.16, printed p.844.
-/

public section
open Subgroup BinaryLinear BinaryTransvectionGroups
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterG.Section03
variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

/-- A genuine common-center group of rank at least two supplies all the
G.3.1 conclusions on its center orbit in a group with trivial two-core. -/
theorem source_conclusions_of_common_center
    {H : Subgroup (BinaryLinear.GL V)} [Finite H] (hcore : pCore 2 H = ⊥)
    (x : V) (hx : x ≠ 0) (A : Subgroup (BinaryLinear.GL V)) (hAH : A ≤ H)
    (hc : 2 < Nat.card A) (hfix : ∀ g ∈ A, g x = x)
    (hmove : ∀ g ∈ A, ∀ v : V, g v-v ∈ centerLine x) :
    FullAction H (MulAction.orbit H x) ∧
      Decomposition H (MulAction.orbit H x) ∧
      LocalStructure H (MulAction.orbit H x) := by
  have hAR : A ≤ rootGroup H x := by
    intro g hg
    refine ⟨hAH hg,?_,hmove g hg⟩
    intro v hv
    obtain ⟨c,rfl⟩ := Submodule.mem_span_singleton.mp hv
    rw [map_smul,hfix g hg]
  have hcard : 2 < Nat.card (rootGroup H x) := hc.trans_le (card_le_of_le hAR)
  have hs : Hypotheses H (MulAction.orbit H x) := by
    refine ⟨?_,⟨x,rfl⟩,?_⟩
    · rintro y ⟨g,rfl⟩
      exact fun he => hx (g.val.injective (he.trans (g.val.map_zero).symm))
    · intro y hy
      obtain ⟨g,rfl⟩ := MulAction.mem_orbit_iff.mp hy
      change 1 < Group.rank (rootQuotientImage H (g.val x))
      have hc' : 2 < Nat.card (rootGroup H (g.val x)) := by
        rw [←rootGroup_conjugate g.property x]
        exact hcard.trans_eq
          (Nat.card_congr ((MulAut.conj g.val).subgroupMap (rootGroup H x)).toEquiv)
      let q := QuotientGroup.mk' (pCore 2 H)
      have hi : Function.Injective q := by
        apply (MonoidHom.ker_eq_bot_iff _).mp
        rw [QuotientGroup.ker_mk',hcore]
      have hqcard : Nat.card (rootQuotientImage H (g.val x)) =
          Nat.card (rootGroup H (g.val x)) :=
        (Nat.card_congr (((rootGroup H (g.val x)).subgroupOf H).equivMapOfInjective q hi).toEquiv).symm.trans
          (Nat.card_congr (subgroupOfEquivOfLe (rootGroup_le H (g.val x))).toEquiv)
      let : IsElementaryAbelian 2 (rootQuotientImage H (g.val x)) :=
        rootQuotientImage_elementaryAbelian H (g.val x)
      have hb : Nat.card (rootQuotientImage H (g.val x)) ≤
          2 ^ Group.rank (rootQuotientImage H (g.val x)) :=
        Nat.le_of_dvd (by positivity) (card_dvd_exponent_pow_rank' _
          (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
            (IsElementaryAbelian.exponent_dvd_p 2 _)))
      by_contra hn
      have hp := pow_le_pow_right' (by decide : 1 ≤ (2:ℕ)) (not_lt.mp hn)
      rw [hqcard] at hb
      omega
  exact source_conclusions_of_twoCore_eq_bot hs hcore

end CFSG.Quasithin.ChapterG.Section03
