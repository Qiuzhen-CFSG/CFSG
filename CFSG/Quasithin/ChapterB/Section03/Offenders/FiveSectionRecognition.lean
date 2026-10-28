module
public import CFSG.Quasithin.ChapterB.Section03.Offenders.Defs
public import Theory.Representation.BinaryAlternatingFiveExtension.TranspositionFourPreimage
import Mathlib.Tactic.FinCases

/-!
# Dihedral-square recognition for the exact source transposition four-group

The source subgroup D 5 consists of the two disjoint transpositions.
Its preimage in an extension with the exact natural kernel is D₈ × D₈.
The elementary supplement is constructed from the faithful-kernel section;
it is not an additional source assumption. Arbitrary conjugates retain
the same given quotient homomorphism.

Source: Aschbacher–Smith 10.2.1, pp.742–743. This applies to the
four-group image of a Baumann factor, rather than the order-eight
Sylow subgroup of S₅.
-/

public section
open Subgroup BinaryPermutation.AlternatingFiveExtension
namespace CFSG.Quasithin.ChapterB.Offenders
local notation "S5" => Equiv.Perm (Fin 5)

private theorem source_D_five_eq_pair_closure : D 5 =
    closure ({Equiv.swap 0 1,Equiv.swap 2 3} : Set S5) := by
  apply congrArg Subgroup.closure
  ext g
  constructor
  · rintro ⟨i,_,rfl⟩
    fin_cases i <;> simp [pairSwap]
  · intro hg
    rcases hg with rfl | hg
    · exact ⟨0,by decide,rfl⟩
    · have hg' : g = Equiv.swap 2 3 := hg
      subst g
      exact ⟨1,by decide,rfl⟩

/-- An existing source image section replaces the elementary-supplement
premise of dihedral-square recognition. -/
theorem dihedral_square_of_D_five_image_section
    {G : Type*} [Group G] (q : G →* S5) (hr : q.range = D 5)
    (e : q.ker ≃* V)
    (he : ∀ (g : G) (v : q.ker), e (MulAut.conjNormal g v) = coreAction (q g) (e v))
    (σ : q.range →* G) (hσ : q.comp σ = q.range.subtype) :
    Nonempty (G ≃* DihedralGroup 4 × DihedralGroup 4) :=
  dihedral_square_of_transposition_four_image_section q
    (hr.trans source_D_five_eq_pair_closure) e he σ hσ

/-- The actual transposition-four preimage is recognized with no externally
supplied supplement or section. -/
theorem D_five_preimage_dihedral_square
    {G : Type*} [Group G] [Finite G]
    (q : G →* S5) (hq : Function.Surjective q) (e : q.ker ≃* V)
    (he : ∀ (g : G) (v : q.ker), e (MulAut.conjNormal g v) = coreAction (q g) (e v)) :
    Nonempty ((D 5).comap q ≃* DihedralGroup 4 × DihedralGroup 4) := by
  rw [source_D_five_eq_pair_closure]
  exact transposition_four_preimage_dihedral_square q hq e he

/-- The conjugated source four-group has the same exact preimage model. -/
theorem conjugate_D_five_preimage_dihedral_square
    {G : Type*} [Group G] [Finite G]
    (q : G →* S5) (hq : Function.Surjective q) (e : q.ker ≃* V)
    (he : ∀ (g : G) (v : q.ker), e (MulAut.conjNormal g v) = coreAction (q g) (e v))
    (a : S5) :
    Nonempty (((D 5).map (MulAut.conj a).toMonoidHom).comap q ≃*
      DihedralGroup 4 × DihedralGroup 4) := by
  rw [source_D_five_eq_pair_closure]
  exact conjugate_transposition_four_preimage_dihedral_square q hq e he a

end CFSG.Quasithin.ChapterB.Offenders
