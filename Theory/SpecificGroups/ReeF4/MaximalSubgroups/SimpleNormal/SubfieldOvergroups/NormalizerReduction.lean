module

public import Theory.SpecificGroups.ReeF4.MaximalSubgroups.SimpleNormal.SubfieldOvergroups.Contracts

/-!
# The subfield normalizer bound from a split-group centralizer

If an endomorphism fixes a subgroup pointwise and an element normalizes that
subgroup, the element's displacement under the endomorphism centralizes it.
A trivial centralizer therefore forces the normalizing element to be fixed.
Apply this to the smaller exceptional power and the derived subfield group.
The binary derived subgroup is contained in every such subgroup, so only
its split-group centralizer needs to be calculated.
This isolates a concrete centralizer calculation in the split F4 carrier;
neither ambient simplicity nor a classification of normalizers is used.

Source context: the subfield case in Malle, J. Algebra 139 (1991), 52–69.
-/

namespace ReeF4.MaximalSubgroups.SimpleNormal

open Subgroup ReeF4.Subfield

private theorem fixed_of_normalizes_of_centralizer_eq_bot {G : Type*} [Group G]
    (f : G →* G) (H : Subgroup G) (hfix : ∀ x ∈ H, f x = x)
    (hC : centralizer (H : Set G) = ⊥) {g : G}
    (hg : g ∈ normalizer (H : Set G)) : f g = g := by
  have hc : g⁻¹ * f g ∈ centralizer (H : Set G) := by
    apply mem_centralizer_iff.mpr
    intro x hx
    have hconj := hfix (g * x * g⁻¹) ((mem_normalizer_iff.mp hg x).mp hx)
    simp only [map_mul, map_inv, hfix x hx] at hconj
    have h := congrArg (fun z => g⁻¹ * z * f g) hconj
    simpa [mul_assoc] using h.symm
  have he : g⁻¹ * f g = 1 := by simpa only [hC, mem_bot] using hc
  have h := congrArg (fun z => g * z) he
  simpa [mul_assoc] using h

/-- Triviality of the centralizer in the split carrier supplies the hard
inclusion in the normalizer calculation inside the Ree fixed group. -/
public theorem derivedSubfieldNormalizer_of_binarySplitCentralizer
    (hC : BinaryDerivedSplitCentralizer) : DerivedSubfieldNormalizer := by
  intro m hm k _ _ g hg
  have hfix : ∀ x ∈ (derivedSubfield m k).map (toSplitGroup m),
      (exceptionalEndomorphism m ^ (2 * k + 1)) x = x := by
    rintro _ ⟨x, hx, rfl⟩
    exact derivedSubfield_le m k hx
  have hgn : toSplitGroup m g ∈
      normalizer ((derivedSubfield m k).map (toSplitGroup m) : Set (SplitGroup m)) :=
    (derivedSubfield m k).le_normalizer_map (toSplitGroup m) ⟨g, hg, rfl⟩
  have hbinary : derivedSubfield m 0 ≤ derivedSubfield m k := by
    have hle : fixedSubfield m 0 ≤ fixedSubfield m k :=
      fixedSubfield_mono m (by simp)
    exact commutator_mono hle hle
  have hCk : centralizer ((derivedSubfield m k).map (toSplitGroup m) :
      Set (SplitGroup m)) = ⊥ := by
    apply le_bot_iff.mp
    rw [← hC m hm]
    exact centralizer_le (Subgroup.map_mono hbinary)
  exact fixed_of_normalizes_of_centralizer_eq_bot _ _ hfix hCk hgn

end ReeF4.MaximalSubgroups.SimpleNormal
