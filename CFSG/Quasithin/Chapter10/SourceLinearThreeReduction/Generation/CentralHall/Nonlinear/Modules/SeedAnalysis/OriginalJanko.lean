module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.CentralHall.Nonlinear.Modules.SeedAnalysis.SeedCubic
public import CFSG.Quasithin.ChapterD.Section03.JankoTensor

/-!
# J₁ separation on the original central Hall seed

Failure of separation makes the unchanged seed a faithful irreducible
module for the marked J₁ square. The original Sylow-orbit bound gives its
full normalizer cubic ratio at most two. The checked J₁ tensor exclusion
contradicts this, proving separation in both original orientations.

The full original moved factors consequently centralize one another.
Combining the resulting geometry with moved minimality eliminates the
J₁ row outright and applies to the literal Hall exponent. Moved minimality
and the remaining linear separation branches stay with the source assembly
owner qt-d-10-nona5-central-hall-orders; the final SeedAnalysisAt and
SourceNonnormalCentralHallAt are not asserted here.

Source: Aschbacher--Smith D.3.7, 3.2.6 and10.1.1,
printed pp.197--199,581 and741.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter10.CentralHall.Nonlinear.Modules
open Chapter3.Section02
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
local instance : IsElementaryAbelian 2 D.seed := D.seed_elementary

/-- A small cubic actor on the unchanged seed excludes its J₁ tensor support. -/
theorem original_seed_separated_of_janko
    {H : Subgroup G} {B : Subgroup H} (c : Context D H B)
    (e : (L ⧸ pCore 2 L) ≃* Janko1.Model)
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G))
    :
    D.seed ≤ centralizer (L.map (MulAut.conj t).toMonoidHom : Set G) ∨
      D.seed ≤ centralizer (L : Set G) := by
  by_contra hsep
  have hsmall := original_seed_normalizer_cubic_of_not_separated D c ht htn hsep
  let : FiniteDimensional (ZMod 2) (Additive D.seed) := Module.Finite.of_finite
  obtain ⟨q,hq,_,hl,hr,σ,hi,hσ⟩ := original_seed_product_action D c e ht htn
  have hf := original_seed_product_faithful_of_not_separated D e ht hsep q hl hr σ hσ
  have himage : actionImage (originalSeedAction D) = actionImage σ := by
    rw [←hσ]
    ext x
    constructor
    · rintro ⟨l,rfl⟩
      exact ⟨q l,Units.ext rfl⟩
    · rintro ⟨g,rfl⟩
      obtain ⟨l,rfl⟩ := hq g
      exact ⟨l,Units.ext rfl⟩
  have hsmallσ : cubicRatio (normalizerRepresentation σ) ≤ 2 := by
    unfold normalizerRepresentation linearNormalizer at hsmall ⊢
    rwa [himage] at hsmall
  exact (not_le_of_gt (ChapterD.janko_square_normalizer_cubicRatio_gt
    (IsSQTK.knownSimple_of_equiv e (original_component_quotient_sqtk D)) σ hi hf)) hsmallσ


/-- The actual J₁ moved factor centralizes its opposite, in both seed orientations. -/
theorem original_janko_crossed
    {H : Subgroup G} {B : Subgroup H} (c : Context D H B)
    (e : (L ⧸ pCore 2 L) ≃* Janko1.Model)
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G)) :
    ⁅D.fullModule,L⁆ ≤ centralizer (L.map (MulAut.conj t).toMonoidHom : Set G) :=
  full_moved_centralizes_opposite_of_seed_separated D ht htn
    (original_seed_separated_of_janko D c e ht htn)

/-- The J₁ branch requires only the remaining moved-minimality proof; its
 separation and original cubic bounds are discharged here. -/
theorem not_janko_of_moved_minimal
    {H : Subgroup G} {B : Subgroup H} (c : Context D H B)
    (e : (L ⧸ pCore 2 L) ≃* Janko1.Model)
    (hmin : MovedMinimal D) : False := by
  obtain ⟨t,ht,htn⟩ := Set.not_subset.mp c.nonnormal
  have hs := separatedSeed_of_separated_and_movedMinimal D hmin ht htn
    (original_seed_separated_of_janko D c e ht htn)
  have hg := (geometry_and_minimality_of_separatedSeed D ht htn hs).1
  exact not_janko_model D c hg hmin (cubic_bounds D c).1 e

/-- The J₁ separation and exclusion feed the literal Hall exponent. The
 remaining moved-minimality premise is owned by this task's final assembly. -/
theorem hall_exponent_of_janko_and_moved_minimal
    {H : Subgroup G} {B : Subgroup H} (c : Context D H B)
    (e : (L ⧸ pCore 2 L) ≃* Janko1.Model)
    (hmin : MovedMinimal D) :
    ∃ n : ℕ, 1 < n ∧ Monoid.exponent B ∣ 2 ^ n + 1 :=
  (not_janko_of_moved_minimal D c e hmin).elim

end CFSG.Quasithin.Chapter10.CentralHall.Nonlinear.Modules
