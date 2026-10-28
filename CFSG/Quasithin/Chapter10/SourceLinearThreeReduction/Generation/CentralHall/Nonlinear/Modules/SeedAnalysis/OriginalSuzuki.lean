module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.CentralHall.Nonlinear.Modules.SeedAnalysis.OriginalTensor
public import CFSG.Quasithin.ChapterD.Section03.SuzukiTensor
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.CentralHall.Nonlinear.Modules.SeedAnalysis.Source

/-!
# Suzuki tensor exclusion on the original central Hall seed

The actual component quotient inherits SQTK through its two-core quotient.
If the original seed is not separated, its marked product action is faithful
and irreducible. Its linear normalizer is literally the normalizer of that
Suzuki square, whose cubic ratio is strictly greater than two. A cubic bound
on the original seed therefore forces separation, in either orientation.

The final application transports this separation to crossed movement on
[D.fullModule,L] and then to the existing Hall exponent consumer. The original
seed cubic bound and L-minimality are explicit remaining source obligations
of qt-d-10-nona5-central-hall-orders. In particular this does not infer a seed
bound merely from the available bound on its larger Sylow orbit, and does not
yet assert SeedAnalysisAt or SourceNonnormalCentralHallAt.

Source: Aschbacher--Smith D.3.5--8, 3.2.6 and10.1.1--2,
printed pp.195--199,581 and741--742.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative MonoidAlgebra
namespace CFSG.Quasithin.Chapter10.CentralHall.Nonlinear.Modules
open Chapter3.Section02
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
local instance : IsElementaryAbelian 2 D.seed := by
  let := D.module_elementary
  exact IsElementaryAbelian.of_injective
    (inclusion (show D.seed ≤ D.moduleSubgroup from le_componentOrbit D.seed T))
    (inclusion_injective _)

include D in
/-- The literal quotient inherits odd ranks and the full K-group hypothesis. -/
theorem original_component_quotient_sqtk :
    IsSQTK KnownSimple.IsKnownSimple (L ⧸ pCore 2 L) := by
  have hJ := (D.local_internal_module (source_module_nonsolvable_uniqueness D)).sqtk
  have hL : IsSQTK KnownSimple.IsKnownSimple L :=
    (IsSQTK.equiv (subgroupOfEquivOfLe
      ((le_componentOrbit L T).trans le_sup_left))).mp
      (hJ.subgroup (L.subgroupOf (localJoin T L)))
  refine ⟨?_,hL.isKGroup.quotient _⟩
  intro p hp ho
  let : Fact p.Prime := ⟨hp⟩
  exact (primeRank_quotient_le_of_isTwoGroup p ho _ pCore_isPGroup).trans
    (hL.stronglyQuasithin p hp ho)

/-- A small cubic actor on the unchanged seed excludes its Suzuki tensor support. -/
theorem original_seed_separated_of_suzuki_cubic
    {H : Subgroup G} {B : Subgroup H} (c : Context D H B)
    (m : ℕ) (hm : 0 < m)
    (e : (L ⧸ pCore 2 L) ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m)
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G))
    (hsmall : cubicRatio (normalizerRepresentation (originalSeedAction D)) ≤ 2) :
    D.seed ≤ centralizer (L.map (MulAut.conj t).toMonoidHom : Set G) ∨
      D.seed ≤ centralizer (L : Set G) := by
  by_contra hsep
  let : Fact (0 < m) := ⟨hm⟩
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
  exact (not_le_of_gt (ChapterD.suzuki_square_normalizer_cubicRatio_gt m hm
    (IsSQTK.knownSimple_of_equiv e (original_component_quotient_sqtk D)) σ hi hf)) hsmallσ

/-- The resulting crossed action is on the original full moved subgroup. -/
theorem original_suzuki_crossed_of_seed_cubic
    {H : Subgroup G} {B : Subgroup H} (c : Context D H B)
    (m : ℕ) (hm : 0 < m)
    (e : (L ⧸ pCore 2 L) ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m)
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G))
    (hsmall : cubicRatio (normalizerRepresentation (originalSeedAction D)) ≤ 2) :
    ⁅D.fullModule,L⁆ ≤ centralizer (L.map (MulAut.conj t).toMonoidHom : Set G) :=
  full_moved_centralizes_opposite_of_seed_separated D ht htn
    (original_seed_separated_of_suzuki_cubic D c m hm e ht htn hsmall)

/-- The actual Hall exponent consumer, with crossed movement discharged by
 the Suzuki tensor exclusion. The original seed bound and L-minimality remain
 with the central Hall source assembly owner. -/
theorem hall_exponent_of_suzuki_seed_cubic_and_minimal
    {H : Subgroup G} {B : Subgroup H} (c : Context D H B)
    (hnot : ¬ Nonempty ((L ⧸ pCore 2 L) ≃*
      Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)))
    (m : ℕ) (hm : 0 < m)
    (e : (L ⧸ pCore 2 L) ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m)
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G))
    (hsmall : cubicRatio (normalizerRepresentation (originalSeedAction D)) ≤ 2)
    (hmin : MovedMinimal D) :
    ∃ n : ℕ, 1 < n ∧ Monoid.exponent B ∣ 2 ^ n + 1 :=
  hall_exponent_of_moved_minimal_and_crossed T D c hnot ht htn hmin
    (original_suzuki_crossed_of_seed_cubic D c m hm e ht htn hsmall)

end CFSG.Quasithin.Chapter10.CentralHall.Nonlinear.Modules
