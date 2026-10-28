module

public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.Recognition.FSource.SplitSixteenSource

/-!
# Source reduction to two characteristic-two vertices

The genuine exceptional-vertex bound and mixed-amalgam theorem put every
exceptional source pair in the completed small-Sylow or split-sixteen family.
Together with the complete F.6.13–17 reduction this leaves exactly the large
quasisimple branch with two characteristic-two vertices and common Sylow
different from C₂ × D₈. This is the branch requiring the remaining marked
F.1.12 families; no local classification output is assumed in this reduction.

Source: Aschbacher–Smith F.6.5(2)(i–v), F.6.17–18, pp.305 and 309–310.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open Theory.GroupTheory.RankTwoAmalgam
namespace CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.Recognition.FSource
universe u
variable {κ : GroupClass.{u}} {G : Type u} [Group G] [Finite G]
    {G₁ G₂ : Subgroup G}

/-- Every original source pair with an exceptional first vertex is classified. -/
theorem exceptional_left_source
    (hA : ∀ (H : Type u) [Group H] [Finite H], ChapterA.Section02.TheoremA κ H)
    (hC : ∀ (H : Type u) [Group H] [Finite H], ChapterA.Section02.TheoremC κ H)
    (q : ThreePrimeSQTKQuotient κ G) (h : ChapterF.IsGoldschmidtTriple G₁ G₂)
    (S : Sylow 2 G) (hS : G₁ ⊓ G₂ = (S : Subgroup G))
    (hbad : generalizedFitting G₁ ≠ pCore 2 G₁) :
    SourceAlternative G₁ G₂ S ∨ SourceAlternative G₂ G₁ S := by
  by_cases hsmall : Nat.card S ≤ 8
  · exact (small_sylow_eight_source hA hC q h S hS hsmall).elim
      (fun ha => Or.inl (Or.inl ha)) (fun ha => Or.inr (Or.inl ha))
  let := q.coverGroup
  let := q.coverFinite
  have hcore := ChapterF.Noncyclic.twoCore_eq_bot_of_cover q.equiv.symm
  have hgood : generalizedFitting G₂ = pCore 2 G₂ := by
    by_contra hbad₂
    have hc := h.intersection_card_of_neither_characteristic_two hcore hbad hbad₂
    rw [hS] at hc
    omega
  have hT : Nat.card (G₂ ⊓ G₁ : Subgroup G) = 16 := by
    rcases h.symm.intersection_card_eight_or_sixteen_of_mixed hcore hgood hbad with hc | hc
    · rw [inf_comm G₂ G₁, hS] at hc
      omega
    · exact hc
  obtain ⟨j⟩ := h.symm.mixed_sixteen_case hcore hgood hbad hT
  let eZ : ℤˣ ≃* C 2 := mulEquivOfPrimeCardEq (p := 2)
    (by rw [Nat.card_eq_fintype_card]; decide) (by simp [Nat.card_eq_fintype_card])
  let eS : S ≃* (C 2 × DihedralGroup 4) :=
    ((MulEquiv.subgroupCongr ((inf_comm G₂ G₁).trans hS).symm).trans j.middle).trans
      (eZ.prodCongr (MulEquiv.refl _))
  exact split_sixteen_source hA hC q h S hS eS

/-- Both orientations of the original exceptional-vertex source family. -/
theorem exceptional_vertex_source
    (hA : ∀ (H : Type u) [Group H] [Finite H], ChapterA.Section02.TheoremA κ H)
    (hC : ∀ (H : Type u) [Group H] [Finite H], ChapterA.Section02.TheoremC κ H)
    (q : ThreePrimeSQTKQuotient κ G) (h : ChapterF.IsGoldschmidtTriple G₁ G₂)
    (S : Sylow 2 G) (hS : G₁ ⊓ G₂ = (S : Subgroup G))
    (hbad : generalizedFitting G₁ ≠ pCore 2 G₁ ∨
      generalizedFitting G₂ ≠ pCore 2 G₂) :
    SourceAlternative G₁ G₂ S ∨ SourceAlternative G₂ G₁ S := by
  rcases hbad with hb | hb
  · exact exceptional_left_source hA hC q h S hS hb
  · exact (exceptional_left_source hA hC q h.symm S ((inf_comm _ _).trans hS) hb).symm

/-- The exact remaining source branch has two characteristic-two vertices,
a large quasisimple residual and no split-sixteen Sylow marking. -/
theorem source_alternative_or_characteristic_two
    (hA : ∀ (H : Type u) [Group H] [Finite H], ChapterA.Section02.TheoremA κ H)
    (hC : ∀ (H : Type u) [Group H] [Finite H], ChapterA.Section02.TheoremC κ H)
    (q : ThreePrimeSQTKQuotient κ G) (h : ChapterF.IsGoldschmidtTriple G₁ G₂) :
    ∃ S : Sylow 2 G, G₁ ⊓ G₂ = (S : Subgroup G) ∧
      ((SourceAlternative G₁ G₂ S ∨ SourceAlternative G₂ G₁ S) ∨
        (8 < Nat.card S ∧ pResidual 2 G = generalizedFitting G ∧
          IsQuasisimple (pResidual 2 G) ∧
          generalizedFitting G₁ = pCore 2 G₁ ∧
          generalizedFitting G₂ = pCore 2 G₂ ∧
          ¬ Nonempty (S ≃* (C 2 × DihedralGroup 4)))) := by
  obtain ⟨S,hS,ha⟩ := source_alternative_or_large_quasisimple hA hC q h
  refine ⟨S,hS,?_⟩
  rcases ha with ha | ⟨hc,hF,hq⟩
  · exact Or.inl ha
  by_cases h₁ : generalizedFitting G₁ = pCore 2 G₁
  swap
  · exact Or.inl (exceptional_vertex_source hA hC q h S hS (Or.inl h₁))
  by_cases h₂ : generalizedFitting G₂ = pCore 2 G₂
  swap
  · exact Or.inl (exceptional_vertex_source hA hC q h S hS (Or.inr h₂))
  by_cases hsplit : Nonempty (S ≃* (C 2 × DihedralGroup 4))
  · exact Or.inl (split_sixteen_source hA hC q h S hS hsplit.some)
  · exact Or.inr ⟨hc,hF,hq,h₁,h₂,hsplit⟩

end CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.Recognition.FSource
