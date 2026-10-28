module
public import CFSG.Quasithin.ChapterE.Section02.Witnesses.Involution.Basic
/-!
# Trivial normal core of the order-two source pair

A nontrivial normal core inside a subgroup of order two would equal that
subgroup. Its conjugates would then generate only that normal subgroup,
contradicting the nontrivial dihedral quotient. Applied to the constructed
pair this proves the full core-free conclusion in the opening case of E.2.7.

Source: Aschbacher–Smith E.2.7, printed p.218.
-/

public section
noncomputable section
open Subgroup
namespace CFSG.Quasithin.ChapterE.Witnesses.Involution
variable {H : Type*} [Group H] [Finite H]
private theorem pair_core_eq_bot {T : Sylow 2 H} {M V : Subgroup H}
    (w : QuotientLift.Pair T M V) (hcard : Nat.card V = 2)
    (hMV : M.subgroupOf w.subgroup = V.subgroupOf w.subgroup)
    (hquot : 1 < Nat.card (w.subgroup ⧸ (M.subgroupOf w.subgroup).normalCore)) :
    (M.subgroupOf w.subgroup).normalCore = ⊥ := by
  by_contra hne
  have hc := (one_lt_card_iff_ne_bot _).mpr hne
  have hAc : Nat.card (M.subgroupOf w.subgroup) = 2 := by
    rw [hMV,Nat.card_congr (subgroupOfEquivOfLe w.le).toEquiv,hcard]
  have he : (M.subgroupOf w.subgroup).normalCore = M.subgroupOf w.subgroup :=
    eq_of_le_of_card_ge (normalCore_le _) (by omega)
  have hn : (V.subgroupOf w.subgroup).Normal := by
    rw [← hMV,← he]
    infer_instance
  have hg := w.generate
  have hcj : (V.subgroupOf w.subgroup).map (MulAut.conj w.conjugator).toMonoidHom =
      V.subgroupOf w.subgroup := normal_iff_map_conj_eq.mp hn w.conjugator
  rw [hcj,sup_idem] at hg
  have hM : M.subgroupOf w.subgroup = ⊤ := hMV.trans hg
  rw [hM,normalCore_eq_self] at hquot
  have hq : Nat.card (w.subgroup ⧸ (⊤ : Subgroup w.subgroup)) = 1 := by simp
  omega

/-- The core-free source pair in the original order-two branch. -/
theorem source_order_two_core_free (T : Sylow 2 H)
    (hP : ChapterB.IsMinimalParabolicOver T ⊤) (V : Subgroup H)
    [IsElementaryAbelian 2 V] (hVT : V ≤ T)
    (hcore : V ≤ (ChapterB.minimalParabolicMax T hP).pCoreIn 2)
    (hcard : Nat.card V = 2) (hJ : ChapterB.minimalParabolicCore T hP = ⊥) :
    ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ ∃ w : QuotientLift.Pair T (ChapterB.minimalParabolicMax T hP) V,
      ∃ a : ℕ, 0 < a ∧ Nonempty ((w.subgroup ⧸
        ((ChapterB.minimalParabolicMax T hP).subgroupOf w.subgroup).normalCore) ≃*
        DihedralGroup (p^a)) ∧
      ((ChapterB.minimalParabolicMax T hP).subgroupOf w.subgroup).normalCore = ⊥ := by
  have hO : pCore 2 H = ⊥ := bot_unique (hJ ▸ ChapterB.minimalParabolicTwoCore_le_core T hP)
  have hout : ¬ V ≤ pCore 2 H := by
    intro h
    have he : V = ⊥ := bot_unique (hO ▸ h)
    have hc := Subgroup.card_eq_one.mpr he
    omega
  obtain ⟨p,hp,hp2,w,a,ha,he,hm⟩ := exists_pair_of_card_two T _ V hVT hcore hcard hout
  have hquot : 1 < Nat.card (w.subgroup ⧸
      ((ChapterB.minimalParabolicMax T hP).subgroupOf w.subgroup).normalCore) := by
    obtain ⟨e⟩ := he
    rw [Nat.card_congr e.toEquiv,DihedralGroup.nat_card]
    have hpos := pow_pos hp.pos a
    omega
  exact ⟨p,hp,hp2,w,a,ha,he,pair_core_eq_bot w hcard hm hquot⟩
end CFSG.Quasithin.ChapterE.Witnesses.Involution
