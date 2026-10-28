module

public import CFSG.Quasithin.ChapterJ.Section01To02.SourceCompletion.AfterNormalizer
public import CFSG.Quasithin.ChapterJ.Section01To02.Centralizers.NormalizerExtension.SourceCompletion.Nonsplit.TwoClasses

/-!
# The unconditional original-source cubic structure

The actual normalizer extension and its transposition fusion construct the
marked Aut(A₆) quotient. Substituting these genuine source producers into
the triple-cover argument gives the original central kernel B, the concrete
3.A₆ carrier, and an ambient extraspecial Sylow subgroup of order27 and
exponent3. The original quotient and kernel markings are retained.

Source: Aschbacher–Smith, J.2.7(1),(11), printed p.437.
-/

public section
namespace CFSG.Quasithin.ChapterJ.SourceCompletion
open Subgroup Centralizers
variable {G : Type*} [Group G] [Finite G] {d : LocalSetup G} (c : Choices d)

/-- The source marked triple cover and cubic Sylow, with all normalizer inputs discharged. -/
theorem cubic_source :
    ∃ (e : c.NormalizerQuotient ≃* MulAut (alternatingGroup (Fin 6)))
      (hM : c.centralizerImage.map e.toMonoidHom = AlternatingSix.M10.extension),
    c.B ≤ c.LB ∧
    (∃ a : c.LB ≃* Atlas.Codes.HexEvenAutomorphisms,
      Atlas.Codes.hexEvenCoordinate.comp a.toMonoidHom = c.residualA6Map e hM ∧
      (c.B.subgroupOf c.LB).map a.toMonoidHom = Atlas.Codes.hexEvenCoordinate.ker) ∧
    ∃ S : Sylow 3 G, Nat.card S = 27 ∧ IsExtraspecial 3 S ∧ Monoid.exponent S = 3 ∧
      (center S).map (S : Subgroup G).subtype = c.B ∧
      (_root_.commutator S).map (S : Subgroup G).subtype = c.B ∧
      ∀ x y : G, orderOf x = 3 → orderOf y = 3 → ∃ g : G, g*x*g⁻¹ = y := by
  obtain ⟨e,hM,h7⟩ := c.marked_normalizer_fusion_source
  exact ⟨e,hM,cubic_after_normalizer c e hM h7⟩

/-- The actual ambient cubic Sylow supplied to J.3 has order27, exponent3,
and its center and commutator are the original B. -/
theorem cubic_sylow_source :
    ∃ S : Sylow 3 G, Nat.card S = 27 ∧ IsExtraspecial 3 S ∧ Monoid.exponent S = 3 ∧
      (center S).map (S : Subgroup G).subtype = c.B ∧
      (_root_.commutator S).map (S : Subgroup G).subtype = c.B ∧
      ∀ x y : G, orderOf x = 3 → orderOf y = 3 → ∃ g : G, g*x*g⁻¹ = y := by
  obtain ⟨_,_,_,_,h⟩ := cubic_source c
  exact h

end CFSG.Quasithin.ChapterJ.SourceCompletion
