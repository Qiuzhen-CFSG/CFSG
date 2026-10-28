module

public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.G2FourModule.Embedding.InnerRealization.PresentationExact.Core
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.G2FourModule.Embedding.InnerRealization.PresentationExact.DihedralCover.Tables
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.G2FourModule.Embedding.InnerRealization.PresentationExact.DihedralCover.Output
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.G2FourModule.Embedding.InnerRealization.PresentationExact.DihedralCover.Deductions
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.G2FourModule.Embedding.InnerRealization.PresentationExact.DihedralCover.Shape

/-!
# Assembling the Hall--Janko dihedral coset certificate

The representatives are actual words in the original five-relator presentation.
A deduction asserts a subgroup-witness equation; an output shape identifies its
literal source, signed generator, and destination among the 25200 representatives.
Together these give a `GeneratorCosetCover` for the original two generators.

All 672983 retained deductions and 100800 output shapes have been kernel checked.
`dihedralCover` discharges both premises of the conditional assembly below,
giving an unconditional cover in the abstract group. The presentation-exactness
consumer combines this cover with the subgroup bound and literal-carrier order.

Source: ATLAS J2G1-P2. The application is Aschbacher--Smith K.4.5, printed
p.460/PDF p.471. See `DihedralCover/source/README.md` for the certificate format.
-/

namespace Sporadic.LeechRelated.J2.G2FourModule.Embedding.InnerRealization.PresentationExact
open Subgroup.CosetWordCertificate DihedralCertificate

private theorem transitions_of_certificate
    (deductions : ∀ n, n < 672983 →
      Holds dihedral generator (definitions.repr generator) (facts n))
    (shapes : ∀ n, n < 100800 → shapeAt n = true)
    (i : Fin 25200) (a : Fin 4) :
    Holds dihedral generator (definitions.repr generator)
      ⟨i.val, [decodeLetter a.val], (destination (4*i.val+a.val)).val⟩ := by
  have hs := (factBEq_eq_true_iff _ _).mp (shapes (4*i.val+a.val) (by omega))
  have hd : (4*i.val+a.val) / 4 = i.val := by omega
  have hm : (4*i.val+a.val) % 4 = a.val := by omega
  change facts (output (4*i.val+a.val)) = _ at hs
  rw [hd, hm] at hs
  rw [← hs]
  exact deductions _ (output_lt _)

/-- Assembly for the fixed certificate, with its finite checks still explicit. -/
public def dihedralCover_of_certificate
    (deductions : ∀ n, n < 672983 →
      Holds dihedral generator (definitions.repr generator) (facts n))
    (shapes : ∀ n, n < 100800 → shapeAt n = true) :
    Subgroup.GeneratorCosetCover dihedral
      (PresentedGroup.of : Fin 2 → Presentation.UniversalGroup) (Fin 25200) where
  repr i := definitions.repr generator i.val
  initial := 0
  initial_eq := definitions.repr_zero generator
  step i x := by
    fin_cases x
    · obtain ⟨h, hh⟩ := transitions_of_certificate deductions shapes i 0
      refine ⟨h, destination (4*i.val+0), ?_⟩
      simpa [decodeLetter, generator] using hh
    · obtain ⟨h, hh⟩ := transitions_of_certificate deductions shapes i 2
      refine ⟨h, destination (4*i.val+2), ?_⟩
      simpa [decodeLetter, generator] using hh
  inv_step i x := by
    fin_cases x
    · obtain ⟨h, hh⟩ := transitions_of_certificate deductions shapes i 1
      refine ⟨h, destination (4*i.val+1), ?_⟩
      simpa [decodeLetter, generator] using hh
    · obtain ⟨h, hh⟩ := transitions_of_certificate deductions shapes i 3
      refine ⟨h, destination (4*i.val+3), ?_⟩
      simpa [decodeLetter, generator] using hh

/-- A certified cover by 25200 representatives for the original two generators. -/
public def dihedralCover :
    Subgroup.GeneratorCosetCover dihedral
      (PresentedGroup.of : Fin 2 → Presentation.UniversalGroup) (Fin 25200) :=
  dihedralCover_of_certificate all_deductions all_shapes

end Sporadic.LeechRelated.J2.G2FourModule.Embedding.InnerRealization.PresentationExact
