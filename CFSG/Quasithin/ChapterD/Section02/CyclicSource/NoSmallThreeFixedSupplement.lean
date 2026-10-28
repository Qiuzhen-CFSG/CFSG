module
public import CFSG.Quasithin.ChapterD.Section02.CyclicSource.NoSmallThreeSource
public import CFSG.Quasithin.ChapterD.Section02.RatioDecomposition.FixedComplement

/-!
# The no-small-three fixed supplement without full movement

Every original starred involution fixes the fixed space of an inverted cubic
subgroup. Thus it fixes C_V(O₃), and starred generation makes this space
globally fixed. Coprime splitting supplies a fixed supplement to [V,O₃].
The literal action on that support therefore has the same cubic minimum
and starred actors. Full Fitting movement and indecomposability are unnecessary.

Source: Aschbacher–Smith D.2.26–29, pp.191–192, used before the D.2.17
applications in 15.1.2, p.1084.
-/

public section
open Subgroup Representation Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterD.CyclicSource
variable {G V : Type*} [Group G] [Finite G]
  [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  {ρ : Representation (ZMod 2) G V}

theorem CoreHypotheses.threeCore_fixed_le_global (h : CoreHypotheses ρ)
    (hq : cubicRatio ρ = 2)
    (hfive : ∀ A ∈ QhatStar ρ, ⁅pCore 5 G,A⁆ = ⊥)
    (hNo : ∀ X : Subgroup G, X ≤ pCore 3 G → Nat.card X = 3 →
      Module.finrank (ZMod 2) (subspaceCommutator ρ ⊤ X) ≠ 2) :
    fixedSpace ρ (pCore 3 G) ≤ fixedSpace ρ ⊤ := by
  rw [← h.generated]
  change fixedSpace ρ (pCore 3 G) ≤ fixedSpace ρ (sSup (QhatStar ρ))
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
  obtain ⟨x,hx,hne,hinv⟩ := h.exists_inverted_threeCore hfive t ht
  have hi := h.inverted_threeCore_support hq hNo hsmall hx hne hinv
  exact (fixedSpace_antitone ρ (zpowers_le.mpr hx)).trans (he ▸ hi.2.2.1)

/-- The actual odd three-core support has a globally fixed supplement. -/
theorem CoreHypotheses.threeCore_fixed_supplement (h : CoreHypotheses ρ)
    (hq : cubicRatio ρ = 2)
    (hfive : ∀ A ∈ QhatStar ρ, ⁅pCore 5 G,A⁆ = ⊥)
    (hNo : ∀ X : Subgroup G, X ≤ pCore 3 G → Nat.card X = 3 →
      Module.finrank (ZMod 2) (subspaceCommutator ρ ⊤ X) ≠ 2) :
    subspaceCommutator ρ ⊤ (pCore 3 G) ⊔ fixedSpace ρ ⊤ = ⊤ := by
  obtain ⟨n,hn⟩ := (pCore_isPGroup (p := 3) (G := G)).exists_card_eq
  have ho : Odd (Nat.card (pCore 3 G)) := by
    rw [hn]
    exact (by decide : Odd 3).pow
  have hc : IsCompl (fixedSpace ρ (pCore 3 G)) (subspaceCommutator ρ ⊤ (pCore 3 G)) := by
    simpa only [RegularCyclicNormalClosure.displacementSpan, subspaceCommutator, eq_comm] using
      (GoldschmidtONan.isCompl_fixed_moved_of_odd (ρ := ρ) ho)
  apply top_unique
  exact hc.symm.sup_eq_top.symm.le.trans
    (sup_le_sup_left (h.threeCore_fixed_le_global hq hfive hNo) _)

/-- Restriction to the literal three-core support preserves the original actors. -/
theorem CoreHypotheses.threeCore_fixed_transport (h : CoreHypotheses ρ)
    (hq : cubicRatio ρ = 2)
    (hfive : ∀ A ∈ QhatStar ρ, ⁅pCore 5 G,A⁆ = ⊥)
    (hNo : ∀ X : Subgroup G, X ≤ pCore 3 G → Nat.card X = 3 →
      Module.finrank (ZMod 2) (subspaceCommutator ρ ⊤ X) ≠ 2)
    (W : Subrepresentation ρ) (hW : W.toSubmodule = subspaceCommutator ρ ⊤ (pCore 3 G)) :
    cubicRatio W.toRepresentation = cubicRatio ρ ∧
      ∀ A : Subgroup G, A ∈ QhatStar W.toRepresentation ↔ A ∈ QhatStar ρ := by
  apply RatioDecomposition.fixed_complement_transport ρ W
  rw [hW]
  exact h.threeCore_fixed_supplement hq hfive hNo

end CFSG.Quasithin.ChapterD.CyclicSource
