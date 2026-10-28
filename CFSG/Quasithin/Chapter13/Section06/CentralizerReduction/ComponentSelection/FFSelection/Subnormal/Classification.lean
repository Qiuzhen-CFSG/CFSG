module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.FFSelection.Subnormal.Classification.SymmetricThree
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.FFSelection.Subnormal.Classification.Quasisimple
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.FFSelection.Subnormal.Classification.OuterSixThree
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.FFSelection.Subnormal.Classification.Products

/-!
# Assembly of the cubic deductions from the full B.5.6 alternatives

The full alternatives imply moved-space rank two and ambient normalizer
index at most two for the subnormal cubic. The trivial and quasisimple
cases are excluded. The S₃ and outer A₆ × C₃ cases identify a characteristic
cubic in the offender subgroup. In the product and hyperplane cases, the
actual normalizing Sylow selects an S₃ factor, coprime averaging lifts its
section dimension, and the two normal cubic directions bound the ambient
orbit. No factor placement or splitting of the original module is assumed.

The literal Chapter 13 application constructs the cubic input from the
marked A₅ seed and applies the full universal classification using the
actual SQTK cover G_v. All branch deductions are discharged. The universal
classification input remains an explicit hypothesis: this proves the
conditional deduction from `SourceAlternative`, not B.5.6 itself. The
earlier local data and final source 13.6.10 assembly remain with the parent.
The older conditional assembly interfaces are preserved.

The separately named source-classification route uses the corrected
projective-line convention in B.4.2(8). Its only changed branch is the
quasisimple exclusion; every nonquasisimple alternative is retained.

Source: Aschbacher–Smith, B.5.3–6, printed pp.104–105, and
Lemma 13.6.10, printed p.928.
-/

@[expose] public section
open scoped IsMulCommutative
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.Subnormal.Classification
open CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison.FFAlternatives
open CFSG.Quasithin.Chapter13.Section08.Components.Swapped.LinearTwo.ModuleAlternatives.FFFactors
universe u w
variable {D : Type u} [Group D] {W : Type w} [AddCommGroup W] [Module (ZMod 2) W]
    [FiniteDimensional (ZMod 2) W] (ρ : Representation (ZMod 2) D W)

/-- Exhaustive conditional assembly, retained for compatibility. The four
branch implications are discharged in `bounds_of_source_alternative`. -/
theorem bounds_of_remaining_cases {A : Subgroup D} {S : Sylow 2 D} {C : Subgroup D}
    (h : CubicHypothesis ρ A S C)
    (hc : SourceAlternative (offenderRepresentation ρ))
    (hq : IsQuasisimple (generalizedFitting (offenderSubgroup ρ)) →
      QuasisimpleSourceConclusion (offenderRepresentation ρ)
        (generalizedFitting (offenderSubgroup ρ)) → False)
    (hp : SourceTwoFactorCase (offenderRepresentation ρ) → CubicBounds ρ A)
    (ho : OuterSixThreeCase (offenderRepresentation ρ) → CubicBounds ρ A)
    (hh : HyperplaneCase (offenderRepresentation ρ) → CubicBounds ρ A) :
    CubicBounds ρ A := by
  cases hc with
  | trivial ht => exact (h.not_trivial ht).elim
  | quasisimple hF ha => exact (hq hF ha).elim
  | symmetricThree hs => exact symmetricThree_bounds ρ h hs
  | twoFactors hs => exact hp hs
  | outerSixThree hs => exact ho hs
  | hyperplane hs => exact hh hs

/-- The complete alternatives give both bounds for the actual subnormal
cubic in the original ambient group. Every branch implication is proved;
the source classification itself is the explicit hypothesis `hc`. -/
theorem bounds_of_source_alternative [Finite D]
    {A : Subgroup D} {S : Sylow 2 D} {C : Subgroup D}
    (h : CubicHypothesis ρ A S C)
    (hc : SourceAlternative (offenderRepresentation ρ)) : CubicBounds ρ A :=
  bounds_of_remaining_cases ρ h hc
    (quasisimple_excluded ρ h) (twoFactors_bounds ρ h)
    (outerSixThree_bounds h) (hyperplane_bounds ρ h)

/-- Both bounds from the complete alternatives with B.4.2(8)'s corrected
projective-line convention. No legacy offender clause is required. -/
theorem bounds_of_projectiveLine_source_alternative [Finite D]
    {A : Subgroup D} {S : Sylow 2 D} {C : Subgroup D}
    (h : CubicHypothesis ρ A S C)
    (hc : ProjectiveLine.SourceAlternative (offenderRepresentation ρ)) : CubicBounds ρ A := by
  cases hc with
  | trivial ht => exact (h.not_trivial ht).elim
  | quasisimple hF ha => exact (quasisimple_excluded_of_source ρ h hF ha).elim
  | symmetricThree hs => exact symmetricThree_bounds ρ h hs
  | twoFactors hs => exact twoFactors_bounds ρ h hs
  | outerSixThree hs => exact outerSixThree_bounds h hs
  | hyperplane hs => exact hyperplane_bounds ρ h hs

section Application
variable {G : Type u} [Group G] [Finite G] {L V : Subgroup G}
    (s : A5Module.Marking L V)
    [IsElementaryAbelian 2 (internalUv (A5Module.markedZ s) (A5Module.markedV s))]
local notation "z₀" => A5Module.markedZ s
local notation "v₀" => A5Module.markedV s
local notation "ρ₀" => uvRepresentation z₀ v₀ (A5Module.markedZ_mem_Gv s)
local notation "A₀" => starImage z₀ v₀ (Lv L v₀)
local notation "J₀" => offenderSubgroup ρ₀

/-- Conditional application retained for compatibility. The branch
implications are discharged in `marked_bounds_of_classification`. -/
theorem marked_bounds_of_remaining_cases (T : Subgroup G)
    (S : Sylow 2 (Gv v₀))
    (hS : (S : Subgroup (Gv v₀)).map (Gv v₀).subtype = Tv T v₀)
    (hT : Tv T v₀ ≤ normalizer (Lv L v₀ : Set G))
    (hcore : pCore 2 (Gstar z₀ v₀) = ⊥)
    (hcard : Nat.card (Lv L v₀ ⧸ pCore 2 (Lv L v₀)) = 3)
    (hfull : A₀ = ⁅A₀, starImage z₀ v₀ (Stellmacher.elementaryAbelianMaxJ (Tv T v₀))⁆)
    (hs : (A₀).IsSubnormal)
    {𝒦 : GroupClass.{u}} (classification : GeneralClassificationInput.{u,u} 𝒦)
    (hSQ : IsSQTK 𝒦 (Gv v₀))
    (hq : IsQuasisimple (generalizedFitting J₀) →
      QuasisimpleSourceConclusion (offenderRepresentation ρ₀) (generalizedFitting J₀) → False)
    (hp : SourceTwoFactorCase (offenderRepresentation ρ₀) → CubicBounds ρ₀ A₀)
    (ho : OuterSixThreeCase (offenderRepresentation ρ₀) → CubicBounds ρ₀ A₀)
    (hh : HyperplaneCase (offenderRepresentation ρ₀) → CubicBounds ρ₀ A₀) :
    CubicBounds ρ₀ A₀ :=
  bounds_of_remaining_cases ρ₀ (marked_cubic_hypothesis s T S hS hT hcore hcard hfull hs)
    (uv_offender_classification z₀ v₀ (A5Module.markedZ_mem_Gv s) classification hSQ hcore)
    hq hp ho hh

/-- The two B.5.6 deductions for the literal Chapter 13 action, star image
and image of the supplied Sylow. The universal classification and genuine
earlier local data suffice; no branch, factor-placement or bound premise
remains. These are exactly the two outputs consumed by
`contradiction_of_linear_classification_bounds`. -/
theorem marked_bounds_of_classification (T : Subgroup G)
    (S : Sylow 2 (Gv v₀))
    (hS : (S : Subgroup (Gv v₀)).map (Gv v₀).subtype = Tv T v₀)
    (hT : Tv T v₀ ≤ normalizer (Lv L v₀ : Set G))
    (hcore : pCore 2 (Gstar z₀ v₀) = ⊥)
    (hcard : Nat.card (Lv L v₀ ⧸ pCore 2 (Lv L v₀)) = 3)
    (hfull : A₀ = ⁅A₀, starImage z₀ v₀ (Stellmacher.elementaryAbelianMaxJ (Tv T v₀))⁆)
    (hs : (A₀).IsSubnormal)
    {𝒦 : GroupClass.{u}} (classification : GeneralClassificationInput.{u,u} 𝒦)
    (hSQ : IsSQTK 𝒦 (Gv v₀)) : CubicBounds ρ₀ A₀ :=
  bounds_of_source_alternative ρ₀
    (marked_cubic_hypothesis s T S hS hT hcore hcard hfull hs)
    (uv_offender_classification z₀ v₀ (A5Module.markedZ_mem_Gv s) classification hSQ hcore)

/-- Literal Chapter 13 application of the complete corrected contract.
The actual inverse image in G_v supplies the SQTK cover in B.5.3. -/
theorem marked_bounds_of_source_classification (T : Subgroup G)
    (S : Sylow 2 (Gv v₀))
    (hS : (S : Subgroup (Gv v₀)).map (Gv v₀).subtype = Tv T v₀)
    (hT : Tv T v₀ ≤ normalizer (Lv L v₀ : Set G))
    (hcore : pCore 2 (Gstar z₀ v₀) = ⊥)
    (hcard : Nat.card (Lv L v₀ ⧸ pCore 2 (Lv L v₀)) = 3)
    (hfull : A₀ = ⁅A₀, starImage z₀ v₀ (Stellmacher.elementaryAbelianMaxJ (Tv T v₀))⁆)
    (hs : (A₀).IsSubnormal)
    {𝒦 : GroupClass.{u}} (classification : ProjectiveLine.GeneralClassificationInput.{u,u} 𝒦)
    (hSQ : IsSQTK 𝒦 (Gv v₀)) : CubicBounds ρ₀ A₀ :=
  bounds_of_projectiveLine_source_alternative ρ₀
    (marked_cubic_hypothesis s T S hS hT hcore hcard hfull hs)
    (classification _ _ _
      (uv_offender_hypothesis z₀ v₀ (A5Module.markedZ_mem_Gv s) hSQ hcore))

/-- The proved S₃ branch already gives both literal Chapter 13 bounds. -/
theorem marked_symmetricThree_bounds (T : Subgroup G)
    (S : Sylow 2 (Gv v₀))
    (hS : (S : Subgroup (Gv v₀)).map (Gv v₀).subtype = Tv T v₀)
    (hT : Tv T v₀ ≤ normalizer (Lv L v₀ : Set G))
    (hcore : pCore 2 (Gstar z₀ v₀) = ⊥)
    (hcard : Nat.card (Lv L v₀ ⧸ pCore 2 (Lv L v₀)) = 3)
    (hfull : A₀ = ⁅A₀, starImage z₀ v₀ (Stellmacher.elementaryAbelianMaxJ (Tv T v₀))⁆)
    (hs : (A₀).IsSubnormal)
    (hc : SymmetricThreeCase (offenderRepresentation ρ₀)) : CubicBounds ρ₀ A₀ :=
  symmetricThree_bounds ρ₀ (marked_cubic_hypothesis s T S hS hT hcore hcard hfull hs) hc

end Application
end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.Subnormal.Classification
