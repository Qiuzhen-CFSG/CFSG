module

public import CFSG.Quasithin.Chapter12.Section08.Terminal.Centers
public import CFSG.Quasithin.Chapter12.Section08.Terminal.Quotients
public import CFSG.Quasithin.Chapter12.Section08.Terminal.ThreeRank

/-!
# Terminal deductions for the marked parabolic

The rank-two case of Lemma 12.8.13(3) follows from the earlier center and
kernel calculations: a normalized center missing Ω₁(Z(T)) is trivial,
and the actual dotted quotient of Z(U)^g is Z(U)/V₁. Its nontriviality
when Z(U) > V₁ gives the rank-two part of (4). The literal centralizer
of the tilded plane has three-rank at most one, proving (8).

The explicit premises are the preceding setup and clauses 12.8.8(3),
12.8.9(1),(7), and 12.8.10(2),(6). Their sibling owners and the Section08
assembly must discharge them. Clauses (4) in higher rank and (5–7) remain
separate source obligations; no conclusion-bearing record replaces them.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*,
combined manuscript of 1 March 2004, printed pp.855–857.
-/

open Subgroup
namespace CFSG.Quasithin.Chapter12.Section08.InvariantFlag
variable {G : Type*} [Group G] {T : Sylow 2 G} {V : Subgroup G} {n : ℕ}

/-- The conjugate center lies in the actual point normalizer. -/
public theorem conjugate_center_le_H (F : InvariantFlag T V n)
    (g : G) (hg : g ∈ normalizer (V : Set G)) : conjugate F.ZU g ≤ F.H :=
  (F.conjugate_center_centralizes_seed g hg).trans
    ((centralizer_le (F.le_seed 1)).trans (centralizer_le_normalizer _))

/-- All assertions of 12.8.13(3), with only preceding source clauses explicit.
The isomorphism uses the actual dotted quotient of H. -/
public theorem lemma_12_8_13_three [Finite G] (F : InvariantFlag T V 2)
    (L : Subgroup G) (hL : L ≤ normalizer (V : Set G))
    (g : G) (hg : g ∈ F.P L)
    (hZ : sylowOmega T = F.Vi 1) (hUT : F.U ≤ (T : Subgroup G))
    (hI : (T : Subgroup G) ≤ normalizer (F.I₂ L : Set G))
    (hVC : V ⊓ F.ZU = F.Vi 1)
    (hdis : conjugate (F.Vi 1) g ⊓ F.ZU = ⊥)
    (hmeet : F.ZU ⊓ conjugate F.ZU g = centerIn (F.I₂ L))
    (hkernel : conjugate F.ZU g ⊓ F.terminalHatAction.ker.map F.H.subtype =
      centerIn (F.I₂ L) ⊔ conjugate (F.Vi 1) g) :
    centerIn (F.I₂ L) = ⊥ ∧ F.ZU ⊓ conjugate F.ZU g = ⊥ ∧
      Nonempty (F.terminalDot (conjugate F.ZU g) ≃*
        (F.ZU ⧸ (F.Vi 1).subgroupOf F.ZU)) ∧
      Nonempty (F.terminalDot (conjugate F.ZU g) ≃* F.tilde F.ZU) ∧
      ⁅F.ZU, conjugate F.ZU g⁆ = ⊥ := by
  have hgn := F.P_le_seed_normalizer L hL hg
  obtain ⟨hc, hi, hm⟩ := F.rankTwo_centers L g hgn hZ hUT hI hVC hdis hmeet
  have hk : conjugate F.ZU g ⊓ F.terminalHatAction.ker.map F.H.subtype =
      conjugate (F.Vi 1) g := by simpa only [hc, bot_sup_eq] using hkernel
  have hZH : F.ZU ≤ F.H := by
    intro z hz
    apply F.conjugate_center_le_H 1 (one_mem _)
    exact ⟨z, hz, by simp⟩
  let e := (F.terminalCenterQuotientEquiv g (F.conjugate_center_le_H g hgn) hk).symm
  exact ⟨hc, hi, ⟨e⟩, ⟨e.trans (F.terminalCenterTildeEquiv hZH)⟩, hm⟩

/-- The rank-two branch of 12.8.13(4). The higher-rank normal-closure
argument is not a premise of this specialization. -/
public theorem lemma_12_8_13_four_rankTwo [Finite G] (F : InvariantFlag T V 2)
    (L : Subgroup G) (hL : L ≤ normalizer (V : Set G))
    (g : G) (hg : g ∈ F.P L)
    (hZ : sylowOmega T = F.Vi 1) (hUT : F.U ≤ (T : Subgroup G))
    (hI : (T : Subgroup G) ≤ normalizer (F.I₂ L : Set G))
    (hVC : V ⊓ F.ZU = F.Vi 1)
    (hdis : conjugate (F.Vi 1) g ⊓ F.ZU = ⊥)
    (hmeet : F.ZU ⊓ conjugate F.ZU g = centerIn (F.I₂ L))
    (hkernel : conjugate F.ZU g ⊓ F.terminalHatAction.ker.map F.H.subtype =
      centerIn (F.I₂ L) ⊔ conjugate (F.Vi 1) g)
    (hproper : F.Vi 1 < F.ZU) : F.terminalDot (conjugate F.ZU g) ≠ ⊥ := by
  have hgn := F.P_le_seed_normalizer L hL hg
  have hc := (F.rankTwo_centers L g hgn hZ hUT hI hVC hdis hmeet).1
  apply F.terminalDot_center_ne_bot g (F.conjugate_center_le_H g hgn) _ hproper
  simpa only [hc, bot_sup_eq] using hkernel

end CFSG.Quasithin.Chapter12.Section08.InvariantFlag
