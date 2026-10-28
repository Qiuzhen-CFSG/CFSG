module

public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.QuasisimpleCases.DihedralEight.Cases
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.QuasisimpleCases.DihedralEight.AlternatingSixLocals
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.QuasisimpleCases.DihedralEight.AlternatingSevenLocals.RowSeven
public import Theory.GroupTheory.CentralizerResidualProducts

/-!
# The quasisimple ambient rows with common Sylow D8

The actual central-cover models supply their center and quotient maps.
The A6 local decoder gives both symmetric-four vertices in the hexacode
triple cover. The A7 decoder gives the compatible rotation-character
amalgam in both A7 and its triple cover. The PSL2 alternative retains the
ambient model and Sylow congruence needed by the chapter consumers.

Source: Aschbacher--Smith F.6.18(6)--(7), printed pp.309--310. The PSL2
alternative deliberately states ambient classification; a blanket claim
that every original vertex pair in that family is S4--S4 is not used.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Theory.GroupTheory.RankTwoAmalgam
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterF.SourceAssembly
variable {G : Type*} [Group G] [Finite G] {G₁ G₂ : Subgroup G}

/-- The genuine local marking in the actual triple-A6 carrier. -/
theorem hexEven_symmetricFour_vertices
    (h : IsGoldschmidtTriple G₁ G₂) (hcore : pCore 2 G = ⊥)
    (hT : Nat.card (G₁ ⊓ G₂ : Subgroup G) = 8)
    (eG : G ≃* Atlas.Codes.HexEvenAutomorphisms) :
    Nonempty (G₁ ≃* Equiv.Perm (Fin 4)) ∧ Nonempty (G₂ ≃* Equiv.Perm (Fin 4)) := by
  let eQ := (QuotientGroup.congr (center G) _ eG (map_center_equiv eG)).trans
    Representation.Hexacode.even_quotient_center_equiv
  have hZ : Odd (Nat.card (center G)) := by
    rw [Nat.card_congr (centerCongr eG).toEquiv, Representation.Hexacode.even_center_card]
    decide
  exact alternatingSix_central_quotient_symmetricFour_vertices h hcore hT eQ hZ

/-- The row-seven compatible marking from either concrete ambient carrier. -/
theorem alternatingSeven_model_row_seven_amalgam
    (h : IsGoldschmidtTriple G₁ G₂) (hcore : pCore 2 G = ⊥)
    (hT : Nat.card (G₁ ⊓ G₂ : Subgroup G) = 8)
    (hm : Nonempty (G ≃* alternatingGroup (Fin 7)) ∨
      Nonempty (G ≃* GLS3.Chapter5.OddCentralCovers.TripleSeven)) :
    let α := RankTwoAmalgam.ofSubgroups G₁ (G₁ ⊓ G₂) G₂ inf_le_left inf_le_right
    Nonempty (RankTwoAmalgam.Iso α (MixedEight.amalgam MixedEight.rotationCharacter)) ∨
      Nonempty (RankTwoAmalgam.Iso α.reverse
        (MixedEight.amalgam MixedEight.rotationCharacter)) := by
  rcases hm with hm | hm
  · obtain ⟨eG⟩ := hm
    have hZmodel : center (alternatingGroup (Fin 7)) = ⊥ :=
      alternatingGroup.center_eq_bot (by simp)
    let eQ := (QuotientGroup.congr (center G) _ eG (map_center_equiv eG)).trans
      ((QuotientGroup.quotientMulEquivOfEq hZmodel).trans QuotientGroup.quotientBot)
    have hZ : Odd (Nat.card (center G)) := by
      rw [Nat.card_congr (centerCongr eG).toEquiv, hZmodel]
      simp
    exact alternatingSeven_row_seven_amalgam h hcore hT eQ hZ
  · obtain ⟨eG⟩ := hm
    let eQ := (QuotientGroup.congr (center G) _ eG (map_center_equiv eG)).trans
      GLS3.Chapter5.OddCentralCovers.tripleSevenQuotientCenterEquiv
    have hZ : Odd (Nat.card (center G)) := by
      rw [Nat.card_congr (centerCongr eG).toEquiv,
        GLS3.Chapter5.OddCentralCovers.tripleSeven_center_card]
      decide
    exact alternatingSeven_row_seven_amalgam h hcore hT eQ hZ

universe u
variable {H : Type u} [Group H] [Finite H]

/-- The complete source alternatives when the quasisimple two-residual
is the entire original ambient group. Model and local premises are derived. -/
theorem source_top_dihedral_eight_rows
    {G : Type u} [Group G] [Finite G] {κ : GroupClass.{u}} {G₁ G₂ : Subgroup G}
    (hA : ChapterA.Section02.TheoremA κ H)
    (hC : ChapterA.Section02.TheoremC κ ((pResidual 2 G) ⧸ center (pResidual 2 G)))
    (hH : IsSQTK κ H) (e : G ≃* (H ⧸ pPrimeCore 3 H))
    (h : IsGoldschmidtTriple G₁ G₂)
    (hq : IsQuasisimple (pResidual 2 G))
    (eT : (G₁ ⊓ G₂ : Subgroup G) ≃* DihedralGroup 4)
    (htop : pResidual 2 G = ⊤) :
    (∃ p f : ℕ, p.Prime ∧ Odd p ∧ 1 ≤ f ∧ f ≤ 2 ∧
      (p ^ f % 16 = 7 ∨ p ^ f % 16 = 9) ∧ ClassicalGroup.IsPSL G 2 (p ^ f)) ∨
    (Nonempty (G ≃* Atlas.Codes.HexEvenAutomorphisms) ∧
      Nonempty (G₁ ≃* Equiv.Perm (Fin 4)) ∧ Nonempty (G₂ ≃* Equiv.Perm (Fin 4))) ∨
    ((Nonempty (G ≃* alternatingGroup (Fin 7)) ∨
      Nonempty (G ≃* GLS3.Chapter5.OddCentralCovers.TripleSeven)) ∧
      (let α := RankTwoAmalgam.ofSubgroups G₁ (G₁ ⊓ G₂) G₂ inf_le_left inf_le_right
       Nonempty (RankTwoAmalgam.Iso α (MixedEight.amalgam MixedEight.rotationCharacter)) ∨
       Nonempty (RankTwoAmalgam.Iso α.reverse
         (MixedEight.amalgam MixedEight.rotationCharacter)))) := by
  have hcore := Noncyclic.twoCore_eq_bot_of_cover e
  have hT : Nat.card (G₁ ⊓ G₂ : Subgroup G) = 8 := by
    rw [Nat.card_congr eT.toEquiv, DihedralGroup.nat_card]
  rcases source_dihedral_eight_residual_models hA hC hH e h hq eT with hm | hm | hm | hm
  · obtain ⟨p, f, hp, ho, hf, hf2, hm⟩ := hm
    obtain ⟨T, hTs⟩ := h.intersection_sylow
    have hT8 : Nat.card T = 8 := by
      rw [← hTs]
      exact hT
    have hmod : p ^ f % 16 = 7 ∨ p ^ f % 16 = 9 := by
      rcases psl_component_parameters_of_sylow_eight T hT8 (isPGroup_quotient_pResidual 2)
        hp ho hf hf2 hm with ⟨_, hc⟩ | ⟨hc, _⟩
      · exact hc
      · exact (hc htop).elim
    let j : G ≃* pResidual 2 G := topEquiv.symm.trans (MulEquiv.subgroupCongr htop).symm
    exact .inl ⟨p, f, hp, ho, hf, hf2, hmod, hm.of_mulEquiv j⟩
  · obtain ⟨j⟩ := hm
    exact .inr (.inl ⟨⟨j⟩, hexEven_symmetricFour_vertices h hcore hT j⟩)
  · exact .inr (.inr ⟨.inl hm,
      alternatingSeven_model_row_seven_amalgam h hcore hT (.inl hm)⟩)
  · exact .inr (.inr ⟨.inr hm,
      alternatingSeven_model_row_seven_amalgam h hcore hT (.inr hm)⟩)

end CFSG.Quasithin.ChapterF.SourceAssembly
