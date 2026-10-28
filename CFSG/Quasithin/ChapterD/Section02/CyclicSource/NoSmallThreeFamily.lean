module
public import CFSG.Quasithin.ChapterD.Section02.CyclicSource.NoSmallThreeSource
/-!
# The family of four-dimensional cubic supports

The source family Y consists of order-three subgroups of O₃ with
four-dimensional moved space. It is invariant under the original group,
and its join acts without fixed vectors and moves the whole source module.
Each minimum involution inverts a member of Y and fixes its complementary
fixed space, so generation and odd-order splitting give the result.
Source: Aschbacher–Smith D.2.26(3), p.191.
-/
@[expose] public section
open Subgroup Representation Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterD.CyclicSource
variable {G V : Type*} [Group G] [Finite G]
  [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V)

/-- The literal family Y in the no-small-three branch. -/
def fourSpaceThreeFactors : Set (Subgroup G) := {X | X ≤ pCore 3 G ∧
  Nat.card X = 3 ∧ Module.finrank (ZMod 2) (subspaceCommutator ρ ⊤ X) = 4}

omit [Finite G] [FiniteDimensional (ZMod 2) V] in
theorem fourSpaceThreeFactors_conjugate {X : Subgroup G}
    (hX : X ∈ fourSpaceThreeFactors ρ) (g : G) :
    X.map (MulAut.conj g).toMonoidHom ∈ fourSpaceThreeFactors ρ := by
  refine ⟨?_,?_,?_⟩
  · exact (map_mono hX.1).trans_eq (Normal.map_conj_eq _ _)
  · rw [card_map_of_injective (MulAut.conj g).injective]
    exact hX.2.1
  · rw [← moved_map_conjugate]
    exact (LinearEquiv.finrank_map_eq
      (LinearEquiv.ofBijective (ρ g) (ρ.apply_bijective g)) _).trans hX.2.2

omit [Finite G] [FiniteDimensional (ZMod 2) V] in
theorem fourSpaceThreeFactors_join_normal : (sSup (fourSpaceThreeFactors ρ)).Normal := by
  constructor
  intro x hx g
  have hm : (sSup (fourSpaceThreeFactors ρ)).map (MulAut.conj g).toMonoidHom ≤
      sSup (fourSpaceThreeFactors ρ) := by
    rw [show sSup (fourSpaceThreeFactors ρ) = ⨆ X : fourSpaceThreeFactors ρ,
      (X : Subgroup G) from sSup_eq_iSup' _,Subgroup.map_iSup]
    apply iSup_le
    intro X
    exact le_iSup_of_le ⟨_,fourSpaceThreeFactors_conjugate ρ X.property g⟩ le_rfl
  exact hm (mem_map.mpr ⟨x,hx,rfl⟩)

variable {ρ}
theorem Hypotheses.fourSpaceThreeFactors_fixed_eq_bot (h : Hypotheses ρ)
    (hq : cubicRatio ρ = 2)
    (hfive : ∀ A ∈ QhatStar ρ, ⁅pCore 5 G,A⁆ = ⊥)
    (hNo : ∀ X : Subgroup G, X ≤ pCore 3 G → Nat.card X = 3 →
      Module.finrank (ZMod 2) (subspaceCommutator ρ ⊤ X) ≠ 2) :
    fixedSpace ρ (sSup (fourSpaceThreeFactors ρ)) = ⊥ := by
  have hfix : fixedSpace ρ (sSup (fourSpaceThreeFactors ρ)) ≤ fixedSpace ρ (Jhat ρ) := by
    change fixedSpace ρ (sSup (fourSpaceThreeFactors ρ)) ≤ fixedSpace ρ (sSup (QhatStar ρ))
    rw [show sSup (QhatStar ρ) = ⨆ A : QhatStar ρ, (A : Subgroup G) from sSup_eq_iSup' _,
      fixedSpace_iSup_family]
    apply le_iInf
    intro A
    obtain ⟨t,ht,he⟩ := starred_generator ρ A.property (h.rank_one A A.property)
    have hsmall : t ∈ smallSupportInvolutions ρ := by
      refine ⟨ht,?_⟩
      change Module.finrank (ZMod 2) (ρ t - LinearMap.id).range ≤ 2
      rw [← fixedCodim_zpowers_eq_displacement_rank,he]
      have hh := (starred_codimension ρ A.property (h.rank_one A A.property)).trans_le h.ratio_le
      exact_mod_cast hh
    obtain ⟨x,hx,hne,hinv⟩ := h.toCoreHypotheses.exists_inverted_threeCore hfive t ht
    have hi := h.toCoreHypotheses.inverted_threeCore_support hq hNo hsmall hx hne hinv
    have hX : zpowers x ∈ fourSpaceThreeFactors ρ :=
      ⟨zpowers_le.mpr hx,by rw [Nat.card_zpowers,hi.1],hi.2.1⟩
    exact (fixedSpace_antitone ρ (le_sSup hX)).trans (he ▸ hi.2.2.1)
  rw [h.generated,h.fixedSpace_eq_bot] at hfix
  exact le_bot_iff.mp hfix

/-- D.2.26(3), on the original module and the actual join of the source family. -/
theorem Hypotheses.fourSpaceThreeFactors_moved_eq_top (h : Hypotheses ρ)
    (hq : cubicRatio ρ = 2)
    (hfive : ∀ A ∈ QhatStar ρ, ⁅pCore 5 G,A⁆ = ⊥)
    (hNo : ∀ X : Subgroup G, X ≤ pCore 3 G → Nat.card X = 3 →
      Module.finrank (ZMod 2) (subspaceCommutator ρ ⊤ X) ≠ 2) :
    subspaceCommutator ρ ⊤ (sSup (fourSpaceThreeFactors ρ)) = ⊤ := by
  have hle : sSup (fourSpaceThreeFactors ρ) ≤ pCore 3 G := sSup_le fun X hX => hX.1
  obtain ⟨n,hn⟩ := (pCore_isPGroup.to_le hle).exists_card_eq
  have ho : Odd (Nat.card (sSup (fourSpaceThreeFactors ρ) : Subgroup G)) := by
    rw [hn]
    exact (by decide : Odd 3).pow
  have hc : IsCompl (fixedSpace ρ (sSup (fourSpaceThreeFactors ρ)))
      (subspaceCommutator ρ ⊤ (sSup (fourSpaceThreeFactors ρ))) := by
    simpa only [RegularCyclicNormalClosure.displacementSpan, subspaceCommutator, eq_comm] using
      (GoldschmidtONan.isCompl_fixed_moved_of_odd (ρ := ρ) ho)
  simpa only [h.fourSpaceThreeFactors_fixed_eq_bot hq hfive hNo,bot_sup_eq] using hc.sup_eq_top

end CFSG.Quasithin.ChapterD.CyclicSource
