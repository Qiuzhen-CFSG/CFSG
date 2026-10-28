module

public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.SixAutomorphisms.ModelIdentification.QuotientRecognition.RankTwo.Sp4Four.FieldCoverGeometry.Inputs
public import Theory.SpecificGroups.SymplecticFour.Binary.DerivedSylowCentralizer

/-!
# The binary field-fixed Sylow centralizer in Sp₄(4)

The field-fixed matrix descends to the literal half field, of order two.
The same coefficient inclusion identifies the embedded component with the
commutator subgroup of this binary symplectic group. Transporting the given
Sylow subgroup along that equivalence preserves its pointwise centralizer.
The binary centralizer calculation then extends its central root coordinates
to an ambient Sylow subgroup, carrying along the actual conjugating matrix.

This proves `FixedGroupSylowGeometry` without additional premises. Central-cover
rigidity and automorphism classification belong to the separate parent assembly.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, E.6.8(2),
printed pp.247–248, and the Sp₄(4) branch of E.6.23, p.254 (PDF p.265).
The field-fixed embedding and derived convention are those of 16.1.4(4),
printed p.1171.
-/

public section

open Subgroup Theory.GroupTheory
open Theory.SpecificGroups.SymplecticFour
open DiagramAutomorphisms.FieldFixedResidual
namespace CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.SixAutomorphisms.ModelIdentification.QuotientScreen.RankTwo.Sp4Four

/-- Binary field-fixed centralizers extend to pointwise fixers of ambient Sylow subgroups. -/
theorem fixedGroupSylowGeometry : FixedGroupSylowGeometry := by
  intro F _ _ _ hF P g hfixed hP
  let K := halfField (F := F) 1
  have hK : Nat.card K = 2 := by
    exact card_halfField (F := F) (m := 1) (by decide) (by simpa using hF)
  let c := coefficientInclusion K
  let d : commutator (Sp K) ≃* FieldComponent.embedded (F := F) 1 :=
    (commutator (Sp K)).equivMapOfInjective c (coefficientInclusion_injective K)
  have hd (x : commutator (Sp K)) : (d x : Sp F) = c (x : Sp K) := rfl
  let P' := P.mapSurjective (f := d.symm.toMonoidHom) d.symm.surjective
  let g' : Sp K := fixedEquiv ((frobeniusEquiv F 2) ^ 1)
    ⟨g, (MulAut.mem_fixedSubgroup _ _).mpr hfixed⟩
  have hg' : c g' = g := fixedEquiv_inclusion _ _
  have hcomm : ∀ x ∈ (P' : Subgroup (commutator (Sp K))),
      (x : Sp K) * g' = g' * (x : Sp K) := by
    rintro _ ⟨y, hy, rfl⟩
    apply coefficientInclusion_injective K
    change c (((d.symm y : commutator (Sp K)) : Sp K) * g') =
      c (g' * ((d.symm y : commutator (Sp K)) : Sp K))
    rw [map_mul, map_mul]
    have hdy : c ((d.symm y : commutator (Sp K)) : Sp K) = (y : Sp F) := by
      rw [← hd, d.apply_symm_apply]
    rw [hg', hdy]
    have hh := hP y hy
    change g * (y : Sp F) * g⁻¹ = (y : Sp F) at hh
    exact (mul_inv_eq_iff_eq_mul.mp hh).symm
  obtain ⟨Q, hQ⟩ := Binary.exists_sylow_fixed_by_inclusion
    (by simpa using hF : Nat.card F = 2 ^ 2) (by decide) K hK P' g' hcomm
  exact ⟨Q, by simpa only [← hg'] using hQ⟩

end CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.SixAutomorphisms.ModelIdentification.QuotientScreen.RankTwo.Sp4Four
