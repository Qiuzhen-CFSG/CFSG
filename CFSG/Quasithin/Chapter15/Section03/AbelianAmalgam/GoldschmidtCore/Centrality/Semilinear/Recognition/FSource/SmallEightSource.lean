module

public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.Recognition.FSource.ProperDihedralSource
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.Recognition.FSource.EightReduction
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.Recognition.FSource.SmallSylowSource

/-!
# Complete adequate F.6.18 at common Sylow order at most eight

All noncyclic, order-four and component-product cases are already source
results. At order eight the original overlap is dihedral, and the completed
quasisimple source family determines the actual ambient model and every needed
local marking. The PSL₂ case keeps the adequate ambient model in place of the
false assertion that every original pair has two symmetric-four vertices.
No rigidity, cover, local recognition or classification-output premise remains.

The inputs are the genuine A/C theorems, original SQTK quotient, Goldschmidt
triple and small-Sylow source branch. The unrestricted theorem still requires
the larger-Sylow source families.
Source: Aschbacher–Smith, F.6.16–18, printed pp.308–310.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.Recognition.FSource
universe u
variable {κ : GroupClass.{u}} {G : Type u} [Group G] [Finite G] {G₁ G₂ : Subgroup G}

theorem eight_source
    (hA : ∀ (H : Type u) [Group H] [Finite H], ChapterA.Section02.TheoremA κ H)
    (hC : ∀ (H : Type u) [Group H] [Finite H], ChapterA.Section02.TheoremC κ H)
    (q : ThreePrimeSQTKQuotient κ G) (h : ChapterF.IsGoldschmidtTriple G₁ G₂)
    (S : Sylow 2 G) (hS : G₁ ⊓ G₂ = (S : Subgroup G)) (hcard : Nat.card S = 8) :
    AdequateAlternative G₁ G₂ S ∨ AdequateAlternative G₂ G₁ S := by
  rcases eight_source_reduction hA hC q h S hS hcard with ha | hq
  · exact ha.elim (fun ha => Or.inl (Or.inl ha)) (fun ha => Or.inr (Or.inl ha))
  obtain ⟨hF,hq⟩ := hq
  let := q.coverGroup
  let := q.coverFinite
  have hcore : pCore 2 G = ⊥ := le_bot_iff.mp
    (ChapterF.twoCore_le_primeToThreeCore.trans
      (ChapterF.Noncyclic.primeToThreeCore_eq_bot_of_quotient q.equiv.symm).le)
  obtain ⟨eT⟩ := ChapterF.SourceAssembly.dihedral_intersection_of_card_eight h hcore (hS ▸ hcard)
  by_cases ht : pResidual 2 G = ⊤
  · exact top_dihedral_source hA hC q h S hS eT hF hq ht
  · have ha := proper_dihedral_source hA hC q h S hS eT hF hq ht
    exact ha.elim (fun ha => Or.inl (Or.inl ha)) (fun ha => Or.inr (Or.inl ha))

/-- The complete small-Sylow classification on the original quotient and
both original local generators, with the adequate PSL₂ conclusion. -/
theorem small_sylow_eight_source
    (hA : ∀ (H : Type u) [Group H] [Finite H], ChapterA.Section02.TheoremA κ H)
    (hC : ∀ (H : Type u) [Group H] [Finite H], ChapterA.Section02.TheoremC κ H)
    (q : ThreePrimeSQTKQuotient κ G) (h : ChapterF.IsGoldschmidtTriple G₁ G₂)
    (S : Sylow 2 G) (hS : G₁ ⊓ G₂ = (S : Subgroup G)) (hcard : Nat.card S ≤ 8) :
    AdequateAlternative G₁ G₂ S ∨ AdequateAlternative G₂ G₁ S := by
  by_cases hsmall : Nat.card S ≤ 4
  · exact Or.inl (Or.inl (small_sylow_source hA hC q h S hS hsmall))
  have hlarge : 4 < Nat.card S := by omega
  have h8 : Nat.card S = 8 := by
    obtain ⟨n,hn⟩ := S.isPGroup'.exists_card_eq
    have hn3 : n ≤ 3 := by
      apply (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp
      exact hn ▸ hcard
    interval_cases n
    · rw [hn] at hlarge; norm_num at hlarge
    · rw [hn] at hlarge; norm_num at hlarge
    · rw [hn] at hlarge; norm_num at hlarge
    · exact hn
  exact eight_source hA hC q h S hS h8

end CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.Recognition.FSource
