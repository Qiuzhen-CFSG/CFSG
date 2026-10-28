module
public import Theory.SpecificGroups.SymplecticFour.SourceFusionOrder.ClassSeparation
public import CFSG.Quasithin.ChapterF.Section04.SourceCompletion.SymplecticFour.Paths

/-!
# Three distinct involution classes in the full symplectic extension

Conjugation in the extension acts on its faithful inner copy by the literal
native automorphism. Diagram preservation and the pinned native class
separation therefore prevent fusion between the three representatives,
including all outer actors of the same extension.

Source: Aschbacher--Smith F.4.27,35,43, printed pp.288--296 of
refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Theory.SpecificGroups.SymplecticFour
open CFSG.Quasithin.ChapterF.SourceCompletion.SymplecticFour
open Theory.SpecificGroups.SymplecticFour.SourceFusionOrder
namespace CFSG.Quasithin.Chapter5.Section03SymplecticSource
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

/-- The three pinned inner images remain distinct in the whole extension. -/
theorem extension_centralRepresentative_irredundant
    {m : ℕ} (hm : 0<m) (hF : Nat.card F=2^m) (E : SourceExtension F)
    (i j : Fin 3) (hij : IsConj (E.innerMap (centralRepresentative i).val)
      (E.innerMap (centralRepresentative j).val)) : i=j := by
  obtain ⟨c,hc⟩ := isConj_iff.mp hij
  have he : c.val (centralRepresentative i).val=(centralRepresentative j).val := by
    apply SourceExtension.inner_injective
    have hh := congrArg Subtype.val hc
    change c.val*MulAut.conj (centralRepresentative i).val*c.val⁻¹=
      MulAut.conj (centralRepresentative j).val at hh
    rw [←hh]
    ext x
    simp
  apply centralRepresentative_irredundant hm hF i j
  rw [←he]
  exact centralRepresentative_automorphism_conjugate c.val (E.preserves_diagram c.val c.property) i
end CFSG.Quasithin.Chapter5.Section03SymplecticSource
