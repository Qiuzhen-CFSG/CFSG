module

public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionNaturalEscape

/-!
# Assembly of the two source branches of 6.1.27

The escaping branch is contradicted on the actual U/Z_S by its geometric
order bound and marked PSL₂ prime action. The contained branch then supplies
n = 2 and the weak-closure alternative. Centralizer symmetry translates
the C₁ formulation into the literal W₁ conclusion, preserving the normalizer
of W₀ in the other alternative.

The initial natural-module theorem 6.1.6, the contained-centralizer case of
6.1.15, and the escaping geometry of 6.1.17--25 are still explicit source
inputs. This module proves their conditional assembly, not those inputs.

Source: Aschbacher--Smith, 6.1.6, 6.1.15 and 6.1.27, pp.669, 672, 679.
-/

@[expose] public section
open Subgroup
namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition
variable {G : Type*} [Group G]

/-- The output of 6.1.15 when C_G(Z_S) is contained in M. The C₁
formulation is the one used in the final paragraph of its proof. -/
def ContainedAlternative (T L M V : Subgroup G) (n : ℕ) : Prop :=
  n = 2 ∧ (¬ normalizer (W (layer L V) T 0 : Set G) ≤ M ∨
    ¬ ZS T L V ≤ C (layer L V) T 1)

/-- Exactly the escaping-branch inputs consumed by the terminal contradiction.
These are earlier-source obligations, not consequences of this definition. -/
def EscapingAlternative (T L V : Subgroup G) (n : ℕ)
    [((ZS T L V).subgroupOf (Escape.U T L V)).Normal] : Prop :=
  n = 2 ∧ Nonempty (NaturalEscape.Geometry T L V) ∧
    NaturalEscape.PrimeComponent T L V

universe u
variable {G : Type u} [Group G] [Finite G] {κ : GroupClass.{u}}
  {T : Sylow 2 G} {L M V : Subgroup G} {n : ℕ}

/-- Assemble 6.1.27 after its three independent earlier source branches
are proved. The final escape exclusion and C₁/W₁ conversion are proved here;
none of the earlier source inputs is asserted unconditionally. -/
theorem conclusion6127_of_source_branches
    (h611 : Hypothesis611 κ T L M V n)
    (hnatural : IsNaturalModule L (layer L V) n)
    (hCT : (T : Subgroup G) ⊓ centralizer (L : Set G) = ⊥)
    (hcontained : centralizer (ZS (T : Subgroup G) L V : Set G) ≤ M →
      ContainedAlternative (T : Subgroup G) L M V n)
    (hescape : letI := h611.ZS_normal_in_escape_U
      ¬ centralizer (ZS (T : Subgroup G) L V : Set G) ≤ M →
        EscapingAlternative (T : Subgroup G) L V n) :
    Conclusion6127 (T : Subgroup G) L M V n := by
  let := h611.ZS_normal_in_escape_U
  have hI : centralizer (ZS (T : Subgroup G) L V : Set G) ≤ M := by
    by_contra hI
    obtain ⟨hn, ⟨d⟩, hcomponent⟩ := hescape hI
    exact NaturalEscape.false_of_geometry d (hn ▸ hnatural) hCT h611.layer_elementary hcomponent
  obtain ⟨hn, hweak⟩ := hcontained hI
  refine ⟨hn, hn ▸ hnatural, hCT, hI, ?_⟩
  rcases hweak with hzero | hone
  · exact Or.inl hzero
  · exact Or.inr fun hw => hone ((le_C_iff h611.ZS_le_T 1).mpr hw)

end CFSG.Quasithin.Chapter6.Source.RankOneRecognition
