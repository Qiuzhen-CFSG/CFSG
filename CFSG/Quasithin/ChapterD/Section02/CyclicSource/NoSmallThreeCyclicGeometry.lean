module
public import CFSG.Quasithin.ChapterD.Section02.CyclicSource.NoSmallThreeFamily
/-!
# The original commutator action in the moving nine-group branch

The cubic factors used in D.2.26 may be chosen inside [O₃,G], since they
arise as commutators with the minimum involutions. The original generating
family therefore makes this normal subgroup fixed-point-free and fully
moved on the original binary module. This is the source input to the
four-line decomposition in D.2.28–29, printed pp.191–192.
-/
@[expose] public section
open Subgroup Representation Representation.BinaryOffender
open scoped commutatorElement
namespace CFSG.Quasithin.ChapterD.CyclicSource
variable {G V : Type*} [Group G] [Finite G]
  [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  {ρ : Representation (ZMod 2) G V}

/-- The four-space cubic factors contained in a specified ambient subgroup. -/
def fourSpaceThreeFactorsIn (ρ : Representation (ZMod 2) G V) (E : Subgroup G) :
    Set (Subgroup G) := {D | D ≤ E ∧ Nat.card D = 3 ∧
      Module.finrank (ZMod 2) (subspaceCommutator ρ ⊤ D) = 4}

private theorem exists_inverted_in_commutator
    {G : Type*} [Group G] (P : Subgroup G) [P.Normal]
    (t : G) (ht : IsInvolution t) (hm : ⁅P, zpowers t⁆ ≠ ⊥) :
    ∃ x ∈ ⁅P,zpowers t⁆, x ≠ 1 ∧ t * x * t⁻¹ = x⁻¹ := by
  have hex : ∃ y ∈ P, ⁅y, t⁆ ≠ 1 := by
    by_contra! h
    apply hm
    rw [commutator_eq_bot_iff_le_centralizer]
    intro y hy
    rw [mem_centralizer_iff]
    intro a ha
    obtain ⟨n, rfl⟩ := ha
    exact ((commutatorElement_eq_one_iff_commute.mp (h y hy)).symm.zpow_left n).eq
  obtain ⟨y, hy, hn⟩ := hex
  refine ⟨⁅y,t⁆, commutator_mem_commutator hy (mem_zpowers t), hn, ?_⟩
  have htt : t * t = 1 := by simpa only [pow_two] using ht.2
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right htt
  simp only [commutatorElement_def, mul_inv_rev, inv_inv, hti, mul_assoc, htt, mul_one]

theorem Hypotheses.threeCore_commutator_fixed_eq_bot (h : Hypotheses ρ)
    (hq : cubicRatio ρ = 2)
    (hfive : ∀ A ∈ QhatStar ρ, ⁅pCore 5 G,A⁆ = ⊥)
    (hNo : ∀ X : Subgroup G, X ≤ pCore 3 G → Nat.card X = 3 →
      Module.finrank (ZMod 2) (subspaceCommutator ρ ⊤ X) ≠ 2) :
    fixedSpace ρ (⁅pCore 3 G,⊤⁆ : Subgroup G) = ⊥ := by
  have hfix : fixedSpace ρ (⁅pCore 3 G,⊤⁆ : Subgroup G) ≤ fixedSpace ρ (Jhat ρ) := by
    change fixedSpace ρ (⁅pCore 3 G,⊤⁆ : Subgroup G) ≤ fixedSpace ρ (sSup (QhatStar ρ))
    rw [sSup_eq_iSup',fixedSpace_iSup_family]
    apply le_iInf
    intro A
    obtain ⟨t,ht,he⟩ := starred_generator ρ A.property (h.rank_one A A.property)
    have hsmall : t ∈ smallSupportInvolutions ρ := by
      refine ⟨ht,?_⟩
      change Module.finrank (ZMod 2) (ρ t - LinearMap.id).range ≤ 2
      rw [← fixedCodim_zpowers_eq_displacement_rank,he]
      have hh := (starred_codimension ρ A.property (h.rank_one A A.property)).trans_le h.ratio_le
      exact_mod_cast hh
    have hm : ⁅pCore 3 G,zpowers t⁆ ≠ ⊥ := by
      intro heq
      exact h.toCoreHypotheses.involution_not_centralizes_three hfive t ht
        ((commutator_eq_bot_iff_le_centralizer.mp
          ((commutator_comm (pCore 3 G) (zpowers t)).symm.trans heq)) (mem_zpowers t))
    obtain ⟨x,hx,hne,hinv⟩ := exists_inverted_in_commutator (pCore 3 G) t
      ⟨fun heq => by simp [heq] at ht,ht ▸ pow_orderOf_eq_one t⟩ hm
    have hxR := commutator_le_left (pCore 3 G) (zpowers t) hx
    have hxE := commutator_mono (le_rfl : pCore 3 G ≤ pCore 3 G)
      (le_top : zpowers t ≤ (⊤ : Subgroup G)) hx
    have hi := h.toCoreHypotheses.inverted_threeCore_support hq hNo hsmall hxR hne hinv
    exact (fixedSpace_antitone ρ (zpowers_le.mpr hxE)).trans (he ▸ hi.2.2.1)
  rw [h.generated,h.fixedSpace_eq_bot] at hfix
  exact le_bot_iff.mp hfix

theorem Hypotheses.threeCore_commutator_moved_eq_top (h : Hypotheses ρ)
    (hq : cubicRatio ρ = 2)
    (hfive : ∀ A ∈ QhatStar ρ, ⁅pCore 5 G,A⁆ = ⊥)
    (hNo : ∀ X : Subgroup G, X ≤ pCore 3 G → Nat.card X = 3 →
      Module.finrank (ZMod 2) (subspaceCommutator ρ ⊤ X) ≠ 2) :
    subspaceCommutator ρ ⊤ (⁅pCore 3 G,⊤⁆ : Subgroup G) = ⊤ := by
  obtain ⟨n,hn⟩ := ((pCore_isPGroup (p := 3) (G := G)).to_le
    (commutator_le_left (pCore 3 G) (⊤ : Subgroup G))).exists_card_eq
  have ho : Odd (Nat.card (⁅pCore 3 G,⊤⁆ : Subgroup G)) := by
    rw [hn]
    exact (by decide : Odd 3).pow
  have hc : IsCompl (fixedSpace ρ (⁅pCore 3 G,⊤⁆ : Subgroup G)) (subspaceCommutator ρ ⊤ (⁅pCore 3 G,⊤⁆ : Subgroup G)) := by
    simpa only [RegularCyclicNormalClosure.displacementSpan, subspaceCommutator, eq_comm] using
      (GoldschmidtONan.isCompl_fixed_moved_of_odd (ρ := ρ) ho)
  simpa only [h.threeCore_commutator_fixed_eq_bot hq hfive hNo,bot_sup_eq] using hc.sup_eq_top

end CFSG.Quasithin.ChapterD.CyclicSource
