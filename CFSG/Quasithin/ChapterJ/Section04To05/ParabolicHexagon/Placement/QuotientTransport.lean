module
public import CFSG.Quasithin.ChapterJ.Section04To05.FiveHexagon.ParabolicFamily.Inverted
/-!
# Equivariance of the original quotient-pentagon labels

The canonical H/Q pentagon associated to an H-conjugate of F1 moves by
literal quotient conjugation. This follows directly from the already proved
F1Q normalizer correspondence and preserves every original inclusion.
Source: Aschbacher--Smith J.4.7 and J.4.10, printed pp.443--445.
-/

public section
noncomputable section
open Subgroup
namespace CFSG.Quasithin.ChapterJ.RuSubgroup.FiveHexagon.ParabolicFamily.Placement
open Centralizers Centralizers.Choices MarkedInverter MarkedNormalizer
open Tits.ExceptionalParabolics.FullRee
variable {G:Type*} [Group G] [Finite G] {d:LocalSetup G}
  (p:Plane d) (s:SourceChoice p) (B5:Sylow 5 d.toTypeRuSetup.H)
  (hi:∀a∈B5Image B5,s.v*a*s.v⁻¹=a⁻¹)
include s hi

/-- Conjugating an original parabolic transports its canonical quotient
pentagon by the same literal H-action. This is the quotient-map form of the
original F₁Q normalizer theorem; no ambient K-normalization is used. -/
theorem parabolicFor_conj (h:d.toTypeRuSetup.H) (P:Sylow 5 S5) :
    parabolicFor p B5 ((d.ru2.quotientMap h) • P) =
      (parabolicFor p B5 P).conjBy (h:G) := by
  obtain ⟨k,hk⟩ := exists_conjugator B5 P
  rw [←hk,←mul_smul,←map_mul,parabolicFor_eq_conjugate p s B5 hi,
    parabolicFor_eq_conjugate p s B5 hi,coe_mul,conjBy_mul]

/-- The canonical pentagon equivalence is equivariant for literal H
conjugation. -/
theorem conjugateEquiv_conj (h:d.toTypeRuSetup.H) (P:Sylow 5 S5) :
    (conjugateEquiv p s B5 hi ((d.ru2.quotientMap h) • P):Subgroup G) =
      (conjugateEquiv p s B5 hi P:Subgroup G).conjBy (h:G) :=
  parabolicFor_conj p s B5 hi h P

end CFSG.Quasithin.ChapterJ.RuSubgroup.FiveHexagon.ParabolicFamily.Placement
