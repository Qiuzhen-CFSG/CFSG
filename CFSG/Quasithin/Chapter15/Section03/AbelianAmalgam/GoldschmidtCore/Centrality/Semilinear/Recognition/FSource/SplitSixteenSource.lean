module

public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.Recognition.FSource.CompleteReduction
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.Recognition.FSource.SquareFieldSource
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.Recognition.FSource.HexEvenSource
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.QuasisimpleCases.SplitSixteen.AlternatingSevenRow

/-!
# Complete source classification for the split Sylow group of order sixteen

The complete initial reduction disposes of the solvable and component-product
cases. The actual quasisimple component sieve leaves a quadratic PSL₂ field
extension, the triple alternating-six cover, or one of the alternating-seven
covers. Their proved ambient extensions, literal outer actions and original
local markings supply the corrected source alternatives. No component model,
local recognition or F-classification conclusion is assumed.

Source: Aschbacher–Smith F.6.17–18(8–9), printed pp.309–310. The square-field
alternative retains both actual defining-prime congruences and does not assert
the invalid arbitrary-pair local marking of the printed row (8).
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.Recognition.FSource
open ChapterF.SourceAssembly
open Theory.GroupTheory.RankTwoAmalgam
universe u
variable {κ : GroupClass.{u}} {G : Type u} [Group G] [Finite G]
    {G₁ G₂ : Subgroup G}

/-- Transport every literal field of the lower triple symmetric-seven extension. -/
def tripleSymmetricOfSevenExtension
    (r : Theory.AlternatingSevenExtension.TripleSymmetricExtension G) :
    TripleSymmetric G 7 where
  kernel := r.kernel
  normal := r.normal
  kernelEquiv := r.kernelEquiv
  quotientEquiv := r.quotientEquiv
  kernel_le := r.kernel_le
  derived := ⟨r.derived_perfect, r.derived_center, r.derived_quotient⟩
  center_eq := r.center_eq
  inverse_action := r.inverse_action

/-- The exact original row-nine vertices and common Sylow, with orientation
determined by the compatible marked amalgam. -/
theorem alternative_nine_of_alternating_seven
    (q : ThreePrimeSQTKQuotient κ G) (h : ChapterF.IsGoldschmidtTriple G₁ G₂)
    (S : Sylow 2 G) (hS : G₁ ⊓ G₂ = (S : Subgroup G))
    (eS : S ≃* (C 2 × DihedralGroup 4))
    (hF : pResidual 2 G = generalizedFitting G)
    (hq : IsQuasisimple (pResidual 2 G))
    (hm : Nonempty (pResidual 2 G ≃* alternatingGroup (Fin 7)) ∨
      Nonempty (pResidual 2 G ≃* GLS3.Chapter5.OddCentralCovers.TripleSeven)) :
    Alternative G₁ G₂ S ∨ Alternative G₂ G₁ S := by
  let := q.coverGroup
  let := q.coverFinite
  obtain ⟨hamb,hmark⟩ := source_alternating_seven_row_nine q.equiv.symm h hF hq
    ((MulEquiv.subgroupCongr hS).trans eS) hm
  have hmodel : Nonempty (G ≃* Equiv.Perm (Fin 7)) ∨
      Nonempty (TripleSymmetric G 7) := by
    rcases hamb with ha | hr
    · exact Or.inl ha
    · exact Or.inr ⟨tripleSymmetricOfSevenExtension hr.some⟩
  let : IsQuasisimple (pResidual 2 G) := hq
  have hqF : IsQuasisimple (generalizedFitting G) :=
    IsQuasisimple.of_mulEquiv (MulEquiv.subgroupCongr hF)
  let eZ : ℤˣ ≃* C 2 := mulEquivOfPrimeCardEq (p := 2)
    (by rw [Nat.card_eq_fintype_card]; decide) (by simp [Nat.card_eq_fintype_card])
  let eL : MixedSixteen.Left ≃* (C 2 × Equiv.Perm (Fin 4)) :=
    eZ.prodCongr (MulEquiv.refl _)
  rcases hmark with hj | hj
  · exact Or.inl (.nine hmodel hqF ⟨eS⟩ ⟨hj.some.left.trans eL⟩ ⟨hj.some.right⟩)
  · exact Or.inr (.nine hmodel hqF ⟨eS⟩ ⟨hj.some.left.trans eL⟩ ⟨hj.some.right⟩)

/-- Complete quasisimple split-sixteen branch, retaining the actual field
action and both original local vertices. -/
theorem quasisimple_split_sixteen_source
    (hA : ∀ (H : Type u) [Group H] [Finite H], ChapterA.Section02.TheoremA κ H)
    (hC : ∀ (H : Type u) [Group H] [Finite H], ChapterA.Section02.TheoremC κ H)
    (q : ThreePrimeSQTKQuotient κ G) (h : ChapterF.IsGoldschmidtTriple G₁ G₂)
    (S : Sylow 2 G) (hS : G₁ ⊓ G₂ = (S : Subgroup G))
    (eS : S ≃* (C 2 × DihedralGroup 4))
    (hF : pResidual 2 G = generalizedFitting G)
    (hq : IsQuasisimple (pResidual 2 G)) :
    SourceAlternative G₁ G₂ S ∨ SourceAlternative G₂ G₁ S := by
  rcases split_sixteen_source_reduction hA hC q h S hS eS hF hq with hr | hm | hm
  · exact Or.inl (Or.inr hr)
  · obtain ⟨T,hT,ha⟩ := alternative_eight_of_hex_even h hF
      ((MulEquiv.subgroupCongr hS).trans eS) hm
    have he : T = S := Sylow.ext (hT.symm.trans hS)
    subst T
    exact Or.inl (Or.inl (Or.inl ha))
  · exact (alternative_nine_of_alternating_seven q h S hS eS hF hq hm).elim
      (fun ha => Or.inl (Or.inl (Or.inl ha)))
      (fun ha => Or.inr (Or.inl (Or.inl ha)))

/-- The complete original-input F source theorem for the common Sylow
group C₂ × D₈. The residual and component conclusions are proved internally. -/
theorem split_sixteen_source
    (hA : ∀ (H : Type u) [Group H] [Finite H], ChapterA.Section02.TheoremA κ H)
    (hC : ∀ (H : Type u) [Group H] [Finite H], ChapterA.Section02.TheoremC κ H)
    (q : ThreePrimeSQTKQuotient κ G) (h : ChapterF.IsGoldschmidtTriple G₁ G₂)
    (S : Sylow 2 G) (hS : G₁ ⊓ G₂ = (S : Subgroup G))
    (eS : S ≃* (C 2 × DihedralGroup 4)) :
    SourceAlternative G₁ G₂ S ∨ SourceAlternative G₂ G₁ S := by
  obtain ⟨T,hT,ha⟩ := source_alternative_or_large_quasisimple hA hC q h
  have he : T = S := Sylow.ext (hT.symm.trans hS)
  subst T
  rcases ha with ha | ⟨_,hF,hq⟩
  · exact ha
  · exact quasisimple_split_sixteen_source hA hC q h S hS eS hF hq

end CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.Recognition.FSource
