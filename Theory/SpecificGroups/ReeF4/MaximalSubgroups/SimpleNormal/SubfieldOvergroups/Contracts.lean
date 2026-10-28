module

public import Theory.SpecificGroups.ReeF4.MaximalSubgroups.SimpleNormal
public import Theory.SpecificGroups.ReeF4.MaximalSubgroups.SimpleNormal.SubfieldOvergroups.FieldMaps

/-!
# Concrete obligations for the subfield overgroup calculation

The objects in these contracts are actual exceptional fixed-point subgroups,
not abstract family labels. Field descent identifies the full fixed group;
strict inclusion detects intermediate subfields. The remaining group geometry
places the supplied simple subgroup and bounds its normalizer. The assembly
in the parent module derives both the whole maximal overgroup and the prime
extension degree from these separate results.

Source: Malle, J. Algebra 139 (1991), 52–69, subfield case; the unconditional
list is reproduced in arXiv:0910.4758, proof of Theorem 5, case 10.
-/

@[expose] public section

namespace ReeF4.MaximalSubgroups.SimpleNormal

open Subgroup ReeF4.Subfield

/-- Descent to the smaller coefficient field, for the full fixed group,
including `k = 0`. The embedding and its injectivity are already constructed. -/
def SubfieldDescent : Prop :=
  ∀ (m k : ℕ) (hdiv : (2 * k + 1) ∣ (2 * m + 1))
    (f : CoefficientField k →+* CoefficientField m),
    (reeMap hdiv f).range = fixedSubfield m k

/-- Proper inclusions for nested subfield fixed groups. The upper endpoint
`l = m` is included and gives properness in the ambient Ree group. -/
def StrictSubfieldInclusions : Prop :=
  ∀ (m k l : ℕ), k < l → l ≤ m →
    (2 * k + 1) ∣ (2 * l + 1) → (2 * l + 1) ∣ (2 * m + 1) →
    fixedSubfield m k < fixedSubfield m l

/-- The difficult inclusion in the normalizer calculation. The reverse
inclusion is `fixedSubfield_le_normalizer_derived`. -/
def DerivedSubfieldNormalizer : Prop :=
  ∀ m, 1 ≤ m → ∀ k, k < m → (2 * k + 1) ∣ (2 * m + 1) →
    normalizer (derivedSubfield m k : Set (Model m)) ≤ fixedSubfield m k

/-- The matrix calculation needed for every subfield normalizer: the
standard binary derived subgroup has trivial centralizer in split F4.
Containment in every derived subfield group gives the other parameters. -/
def BinaryDerivedSplitCentralizer : Prop :=
  ∀ m, 1 ≤ m →
    centralizer ((derivedSubfield m 0).map (toSplitGroup m) : Set (SplitGroup m)) = ⊥

/-- Intrinsic placement of the supplied simple subgroup in the concrete
standard subfield. This retains the original local hypotheses and asserts
neither maximal-overgroup identification nor an extension-degree restriction. -/
def DerivedSubfieldPlacement : Prop :=
  ∀ m, 1 ≤ m → ∀ M : Subgroup (Model m), IsCoatom M →
    ¬ Group.IsSolvable M → solvableRadical M = ⊥ → ∀ S : Subgroup M,
      S.Normal → IsSimpleGroup S → ¬ IsMulCommutative S →
      centralizer (S : Set M) = ⊥ →
      ∀ k, k < m → (2 * k + 1) ∣ (2 * m + 1) →
        (S ≃* _root_.commutator (Model k)) →
        ∃ g : Model m, (S.map M.subtype).map (MulAut.conj g).toMonoidHom =
          derivedSubfield m k

/-- Descent identifies the full standard fixed group using the already
constructed injective homomorphism of the concrete Ree models. -/
theorem nonempty_fixedSubfield_equiv_of_descent (hdesc : SubfieldDescent)
    {m k : ℕ} (hdiv : (2 * k + 1) ∣ (2 * m + 1)) :
    Nonempty (fixedSubfield m k ≃* Model k) := by
  obtain ⟨f⟩ := nonempty_coefficientHom hdiv
  exact ⟨(MulEquiv.subgroupCongr (hdesc m k hdiv f).symm).trans
    (MonoidHom.ofInjective (reeMap_injective hdiv f)).symm⟩

end ReeF4.MaximalSubgroups.SimpleNormal
