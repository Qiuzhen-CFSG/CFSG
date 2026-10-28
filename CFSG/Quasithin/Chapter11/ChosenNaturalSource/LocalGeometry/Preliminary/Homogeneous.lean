module

public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Preliminary.Homogeneous.Stable
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Preliminary.Homogeneous.G2
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Preliminary.Homogeneous.Sp4
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Preliminary.Homogeneous.SL3

/-!
# Homogeneity of the full chosen-natural quotient

The original central quotient embeds in and generates the full quotient.
For G₂ every automorphism preserves its natural binary type. For Sp₄ and
SL₃ there are at most two types, and the chosen Sylow subgroup preserves
the seed; the type stabilizer therefore has odd index at most two. Thus
the literal full quotient is one isotypic component in all three rows.
The nonzero-central-part branch is additionally irreducible.

Source: Aschbacher--Smith, 11.0.3(2), printed p.760.
-/

public noncomputable section
open scoped IsMulCommutative
open Subgroup Theory.GroupTheory Representation
open CFSG.Quasithin.Chapter12.Section02
open Representation.BinaryOffender.Homogeneous
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Preliminary
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)

/-- Source 11.0.3(2): the literal full quotient is a single isotypic component
for L in every chosen-natural row. The formula records its original normalizer
conjugation action, and no extra classification or twist premise remains. -/
theorem fullModule_homogeneous :
    letI := fullModule_elementary D S
    let M := normalizer (L : Set G)
    let U := componentOrbit V M
    ∃ σ : Representation (ZMod 2) M
        (Additive (U ⧸ (centralizer (L : Set G)).subgroupOf U)),
      (∃ I : Subrepresentation (σ.comp (L.subgroupOf M).subtype),
        IsIrreducible I.toRepresentation ∧ homogeneousPart I ⊤ = ⊤) ∧
      (∀ (g : M) (v : U),
        σ g (Additive.ofMul (QuotientGroup.mk'
          ((centralizer (L : Set G)).subgroupOf U) v)) =
          Additive.ofMul (QuotientGroup.mk' ((centralizer (L : Set G)).subgroupOf U)
            ⟨(g : G) * (v : G) * (g : G)⁻¹,
              (mem_normalizer_iff.mp (le_normalizer_componentOrbit V M g.property) v).mp
                v.property⟩)) := by
  cases S.natural with
  | sl3 h => obtain ⟨m⟩ := h; exact fullModule_sl3_homogeneous D S m
  | sp4 h => obtain ⟨m⟩ := h; exact fullModule_sp4_homogeneous D S m
  | g2 h => obtain ⟨m⟩ := h; exact fullModule_g2_homogeneous D S m

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Preliminary
