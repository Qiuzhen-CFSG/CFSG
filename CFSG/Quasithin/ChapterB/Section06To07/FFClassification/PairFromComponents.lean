module
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.PairComponentAlignment
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.BinaryComponentRows
public import CFSG.Quasithin.ChapterB.Section06To07.FFClassification.PairNatural
/-!
# Common natural coordinates from exchanged binary components

Distinct ordinary components lie in opposite native B.5 factors. Moving
one component to the other exchanges those literal factors. Binary SL₂
component models select natural factor rows, and transport through the
same moving element gives their common model and original axis identities.
No minimal-parabolic hypothesis is used.

Source: Aschbacher–Smith B.5.6(3), p.105, and 13.6.14, p.929.
-/
public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterB.SourceInduction
variable {D V : Type*} [Group D] [Finite D] [AddCommGroup V] [Module (ZMod 2) V]
  {ρ : Representation (ZMod 2) D V}

theorem SourceTwoFactorCase.exchange_of_moving_component (d : SourceTwoFactorCase ρ)
    (hcore : pCore 2 D = ⊥) {A B : Subgroup D}
    (hA : IsComponent D A) (hB : IsComponent D B) (hne : A ≠ B)
    (a : MulAut D) (ha : A.map a.toMonoidHom = B) :
    d.first.map a.toMonoidHom = d.second ∧ d.second.map a.toMonoidHom = d.first := by
  rcases d.automorphism_permutation hcore a with hf | hs
  · have hnb := hB.isCComponent.ne_bot
    rcases d.component_alignment hA hB hne with ⟨hAf,hBs⟩ | ⟨hAs,hBf⟩
    · have hBf : B ≤ d.first := by rw [← ha,← hf.1]; exact map_mono hAf
      exact (hnb (bot_unique ((le_inf hBf hBs).trans d.product.disjoint.le_bot))).elim
    · have hBs : B ≤ d.second := by rw [← ha,← hf.2]; exact map_mono hAs
      exact (hnb (bot_unique ((le_inf hBf hBs).trans d.product.disjoint.le_bot))).elim
  · exact hs
end CFSG.Quasithin.ChapterB.SourceInduction
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterB
open QuasisimpleSource SourceInduction
variable {G V : Type*} [Group G] [Finite G] [AddCommGroup V] [Module (ZMod 2) V]

theorem source_pair_natural_of_binary_components
    (ρ : Representation (ZMod 2) G V) (Y : Subgroup G) [Y.Normal]
    (d : SourceTwoFactorCase (ρ.comp Y.subtype))
    (hcore : pCore 2 Y = ⊥) {A B : Subgroup Y}
    (hA : IsComponent Y A) (hB : IsComponent Y B) (hne : A ≠ B)
    (E : BinaryField) (eA : A ≃* SL(2,E.Carrier)) (eB : B ≃* SL(2,E.Carrier))
    (g : G) (hg : A.map (MulAut.conjNormal g).toMonoidHom = B)
    :
    ((∃ F : BinaryField, Nonempty (d.MarkedProduct (linearNatural F 2))) ∨
      Nonempty (d.MarkedProduct (BinaryPermutation.naturalRepresentation (Fin 5)))) := by
  have hexchange := (d.exchange_of_moving_component hcore hA hB hne (MulAut.conjNormal g) hg).1
  let : d.first.Normal := d.product.swap.second_normal
  let : d.second.Normal := d.product.second_normal
  have hrows :
      (d.firstSpace.toSubmodule = moved (ρ.comp Y.subtype) d.first ∧
        ((∃ F : BinaryField, IsLinearNatural
          (((fixed (ρ.comp Y.subtype)).quotientImage d.firstSpace).toRepresentation.comp d.first.subtype) F 2) ∨
        IsSymmetricNatural (((fixed (ρ.comp Y.subtype)).quotientImage d.firstSpace).toRepresentation.comp d.first.subtype) 5)) ∧
      d.secondSpace.toSubmodule = moved (ρ.comp Y.subtype) d.second := by
    rcases d.component_alignment hA hB hne with ⟨hAf,hBs⟩ | ⟨hAs,hBf⟩
    · exact ⟨d.firstCase.rankOne_of_binary_component hA hAf eA,
        (d.secondCase.rankOne_of_binary_component hB hBs eB).1⟩
    · exact ⟨d.firstCase.rankOne_of_binary_component hB hBf eB,
        (d.secondCase.rankOne_of_binary_component hA hAs eA).1⟩
  rcases hrows.1.2 with hlin | hsym
  · obtain ⟨F,⟨e⟩⟩ := hlin
    exact Or.inl ⟨F,⟨sourceTwoFactorSharedModel ρ Y d hrows.1.1 hrows.2 g hexchange _ e⟩⟩
  · obtain ⟨e⟩ := hsym
    exact Or.inr ⟨sourceTwoFactorSharedModel ρ Y d hrows.1.1 hrows.2 g hexchange _ e⟩
end CFSG.Quasithin.ChapterB
