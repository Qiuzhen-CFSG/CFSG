module

public import CFSG.Quasithin.ChapterH.Section13To16.M22Local.ElementaryFour.Basic

/-!
# Partial assembly of H.15.5 on the native outer M22

The inner case follows from the two elementary subgroups in H.14.3(1), the
hexad fixed-space and fixed-span dimensions, and H.15.4(3) for the quintet.
The outer case has been reduced to two concrete quotient configurations in
`Basic`; their lifts and the exceptional centralizer geometry remain to be
proved. Thus this module does not yet assert the exhaustive H.15.5 theorem.

Source: Aschbacher--Smith, combined manuscript (1 March 2004), H.15.5,
printed pp.400--401.
-/

public section

open Representation.BinaryOffender
open MathieuCode MathieuCode.M22ElementaryFour

namespace CFSG.Quasithin.ChapterH.Section13To16.M22ElementaryFour

/-- The whole inner case combines H.14.3(1) with the earlier hexad and
quintet module calculations. Its input is the earlier inner classification,
not the desired outer four-alternative statement. -/
theorem inner_case (T : Sylow 2 Ambient)
    (hinner : ∀ A : Subgroup Ambient, IsElementaryAbelian 2 A → Nat.card A = 16 →
      A ≤ (T : Subgroup Ambient) → A ≤ MathieuCode.M22ElementaryFour.Inner →
      A = HexadKernel ∨ A = QuintetKernel ⊓ MathieuCode.M22ElementaryFour.Inner)
    (hKfixed : Module.finrank (ZMod 2)
      (fixedSpace m22OuterCocodeRepresentation HexadKernel) = 5)
    (hKspan : Module.finrank (ZMod 2)
      (M22Cocode ⧸ fixedSpaceSpan m22OuterCocodeRepresentation HexadKernel) = 1)
    (hQ : ∀ B : Subgroup Ambient, B ≤ QuintetKernel → Nat.card B = 16 →
      Module.finrank (ZMod 2) (fixedSpace m22OuterCocodeRepresentation B) = 2 ∧
      fixedSpaceSpan m22OuterCocodeRepresentation B = ⊤)
    (A : Subgroup Ambient) (hA : IsElementaryAbelian 2 A) (hcard : Nat.card A = 16)
    (hAT : A ≤ (T : Subgroup Ambient)) (hAL : A ≤ MathieuCode.M22ElementaryFour.Inner) :
    FourAlternatives A := by
  rcases hinner A hA hcard hAT hAL with rfl | he
  · exact Or.inl ⟨rfl, hKfixed, hKspan⟩
  · have hAQ : A ≤ QuintetKernel := he ▸ inf_le_left
    have hfused : FusedIntoQuintet A := ⟨1, by
      change A.map (MonoidHom.id Ambient) ≤ QuintetKernel
      simpa using hAQ⟩
    exact Or.inr (Or.inl ⟨hfused, quintet_module_case hQ A hcard hfused⟩)

end CFSG.Quasithin.ChapterH.Section13To16.M22ElementaryFour
