module
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.ChiefFactors.Alignment.SourceInputs
public import CFSG.Quasithin.Chapter13.Section07.ModelExclusions.SeedTransitivity
public import CFSG.Quasithin.Chapter13.Section08.SourceCompletion.LocalModels.Chosen

/-!
# The original generating two-space in the strict L₄ argument

The standing flag has |V₁|=2 and |V₃|=8, so its literal quotient has index
four. The original point-residual orbit theorem is transitive on its three
nonzero vectors. Pulling the orbit equality back through U_H→U_H/V₁ proves
that every point-residual-invariant subgroup between V₁ and V₃ is an endpoint.

These statements construct the `GeneratingSeed` consumed by the maximal-head
argument, with the literal source quotient, L₁T marking and given conjugation
action. No head classification or irreducibility premise is assumed here.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), proof of
13.7.6(3), printed p.939, and the seed in 13.8.25, printed pp.960–961.
-/

public section
open Subgroup Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.OriginalSource
open ChiefFactors ChiefFactors.Alignment
open TransvectionRecognition
open TransvectionRecognition.Component.ModelExtension SourceCompletion
open TransvectionParabolic.Marking
open TransvectionParabolic.Marking.CompatibleFlags
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ H : Subgroup G}

/-- The original flag gives the index of the seed modulo the line. -/
theorem seed_index_source (d : LocalSetup T L V V₁ V₂ V₃ M G₁) :
    V₁.relIndex V₃ = 4 := by
  have hi := Subgroup.card_mul_index (V₁.subgroupOf V₃)
  rw [Nat.card_congr (subgroupOfEquivOfLe
    (d.line_le_plane.trans d.plane_le_seed)).toEquiv, d.line_card, d.seed_card] at hi
  change 2 * V₁.relIndex V₃ = 8 at hi
  omega

variable [(V₁.subgroupOf (Source.UH H V₃)).Normal]
  [IsElementaryAbelian 2 (Source.Utilde H V₃ V₁)]

/-- Transitivity on the original nonzero seed vectors excludes every
intermediate invariant subgroup. -/
theorem seed_irreducible_source (d : LocalSetup T L V V₁ V₂ V₃ M G₁)
    (hL₁H : sourceOne L T V₁ ≤ H)
    (ρ : Representation (ZMod 2) (Source.Hstar H) (SourceSpace H V₃ V₁))
    (hρ : IsSourceAction H V₃ V₁ ρ)
    (X : Subgroup G) (hVX : V₁ ≤ X) (hXV : X ≤ V₃)
    (hN : sourceOne L T V₁ ≤ normalizer (X : Set G)) : X = V₁ ∨ X = V₃ := by
  classical
  by_cases he : X = V₁
  · exact Or.inl he
  right
  apply le_antisymm hXV
  have hn : ¬ X ≤ V₁ := fun h => he (le_antisymm h hVX)
  obtain ⟨x, hx, hx₁⟩ := SetLike.not_le_iff_exists.mp hn
  let u : Source.UH H V₃ := ⟨x, le_conjugateSpanBy V₃ H (hXV hx)⟩
  have hu0 : vector H V₃ V₁ u ≠ 0 := by
    intro h
    exact hx₁ ((QuotientGroup.eq_one_iff (N := V₁.subgroupOf (Source.UH H V₃)) u).mp h)
  have horbit := Section07.ModelExclusions.seed_section_nonzero_orbit
    (localNaturalSetup d) hL₁H ρ (fun h u => hρ h u)
    (vector H V₃ V₁ u) ⟨u, hXV hx, rfl⟩ hu0
  intro y hy
  by_cases hy₁ : y ∈ V₁
  · exact hVX hy₁
  let w : Source.UH H V₃ := ⟨y, le_conjugateSpanBy V₃ H hy⟩
  have hw0 : vector H V₃ V₁ w ≠ 0 := by
    intro h
    exact hy₁ ((QuotientGroup.eq_one_iff (N := V₁.subgroupOf (Source.UH H V₃)) w).mp h)
  obtain ⟨l, hl⟩ := horbit (vector H V₃ V₁ w) ⟨w, hy, rfl⟩ hw0
  let a : H := inclusion hL₁H l
  let c := sourceConjugate H V₃ a u
  have hc : (c : G) ∈ X :=
    (mem_normalizer_iff.mp (hN l.property) x).mp hx
  have hq : sourceProjection H V₃ V₁ c = sourceProjection H V₃ V₁ w := by
    change Additive.ofMul (sourceProjection H V₃ V₁ c) = vector H V₃ V₁ w
    exact (hρ a u).symm.trans hl
  have hk : (c / w : Source.UH H V₃) ∈ V₁.subgroupOf (Source.UH H V₃) :=
    QuotientGroup.eq_iff_div_mem.mp hq
  have hc' : (c : G) / y ∈ X := hVX hk
  have heq : ((c : G) / y)⁻¹ * c = y := by
    rw [div_eq_mul_inv, mul_inv_rev, inv_inv, mul_assoc, inv_mul_cancel, mul_one]
  exact heq ▸ X.mul_mem (X.inv_mem hc') hc

/-- The literal source seed satisfies the maximal-head argument’s
generation, dimension, Sylow and irreducibility requirements. -/
noncomputable def generatingSeed_source (d : LocalSetup T L V V₁ V₂ V₃ M G₁)
    (hL₁H : sourceOne L T V₁ ≤ H) (hTH : (T : Subgroup G) ≤ H)
    (ρ : Representation (ZMod 2) (Source.Hstar H) (SourceSpace H V₃ V₁))
    (hρ : IsSourceAction H V₃ V₁ ρ) : GeneratingSeed ρ :=
  sourceSeedOfEarlier H V₃ V₁ ρ hρ (sourceOne L T V₁ ⊔ (T : Subgroup G))
    T (sup_le hL₁H hTH) le_sup_right T.isPGroup'
    (sup_le (Section07.ModelExclusions.point_residual_normalizes_seed (localNaturalSetup d))
      d.seed_stable)
    (lt_of_le_of_ne (d.line_le_plane.trans d.plane_le_seed) (by
      intro he
      have hc := congrArg (fun X : Subgroup G => Nat.card X) he
      rw [d.line_card, d.seed_card] at hc
      omega))
    (fun X hx hy hn => seed_irreducible_source d hL₁H ρ hρ X hx hy (le_sup_left.trans hn))
    (seed_index_source d)

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.OriginalSource
