module

public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.TransvectionModules.Quotients.Sections
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.TransvectionModules.Quotients.Irreducible
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.TransvectionModules.Quotients.FourLocalFactors.Bar
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.TransvectionModules.Quotients.FourLocalFactors.Generation
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.TransvectionModules.Quotients.FourLocalFactors.Restrictions

/-!
# The two generating local sections for 13.8.6(4)

We construct U_H V/V and U₂/V as actual subgroup images in U_L/V,
under the images of L₁T and L₂T. The conjugate-span calculation proves
that both generate the full module, and hence both survive in a common
irreducible quotient. In particular, the second survival assertion is
proved from the first local irreducibility, V ∩ U_H = V₃, and the
interchange of K₂- and L₂-conjugates; dimension six alone is not used
as a substitute for generation.

The final conditional assembly derives the dimensions, irreducibility and
natural equivalences from the two original marked modules, the commutator
identities and the specified local S₃ quotients. Source construction of
U_H=[U_H,L₁] and of those local group quotients remains necessary. The
bar-action construction is provided separately by SectionStructure.Assembly.
This module does not assert completed 13.8.6(4) or a Steinberg identification.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*,
combined manuscript of 1 March 2004, printed p.948.
-/

@[expose] public section

open Subgroup Representation
open scoped IsMulCommutative

namespace CFSG.Quasithin.Chapter13.Section08.TransvectionQuotients.FourLocalFactors

variable {G A : Type*} [Group G] [Group A]
  (L H T L₁ L₂ V V₂ V₃ : Subgroup G)
  [(V.subgroupOf (Source.UL L H V₃)).Normal]
  [IsElementaryAbelian 2 (Source.ULsection L H V₃ V)]
  (π : (L ⊔ T : Subgroup G) →* A)
  (hULnorm : L ⊔ T ≤ normalizer (Source.UL L H V₃ : Set G))
  (ρ : Representation (ZMod 2) A (Additive (Source.ULsection L H V₃ V)))
  (hρ : SectionConjugationAlong (L ⊔ T) (Source.UL L H V₃) V π hULnorm ρ)
  (h₁norm : L₁ ⊔ T ≤ normalizer (Source.UH H V₃ : Set G))
  (h₂norm : L₂ ⊔ T ≤ normalizer (Source.U2 H V V₂ : Set G))

local notation "P₁" => Subgroup.map π (Subgroup.subgroupOf (L₁ ⊔ T) (L ⊔ T))
local notation "P₂" => Subgroup.map π (Subgroup.subgroupOf (L₂ ⊔ T) (L ⊔ T))
local notation "S₁" => localImage (Source.UL L H V₃) V (L ⊔ T) π hULnorm ρ hρ
  (L₁ ⊔ T) (Source.UH H V₃) h₁norm
local notation "S₂" => localImage (Source.UL L H V₃) V (L ⊔ T) π hULnorm ρ hρ
  (L₂ ⊔ T) (Source.U2 H V V₂) h₂norm

/-- The U_H image generates U_L/V by its literal defining conjugate span. -/
theorem UH_image_spans :
    Submodule.span (ZMod 2) {x | ∃ a : A, ∃ s : S₁, x = ρ a (s : _)} = ⊤ :=
  localImage_spans_of_conjugateSpan (Source.UL L H V₃) V (L ⊔ T) π hULnorm ρ hρ
    (Source.UH H V₃) L (L₁ ⊔ T) h₁norm le_sup_left rfl

/-- The U₂ image also generates U_L/V. Its proof uses the actual first
local action; it is valid before choosing any irreducible quotient. -/
theorem U2_image_spans [IsIrreducible (S₁).toRepresentation]
    (hgen : V = conjugateSpanBy V₃ L₂)
    (hKL : Source.K2 H V₂ ≤ normalizer (L₂ : Set G))
    (hinter : V ⊓ Source.UH H V₃ = V₃)
    (hU₂ : Source.U2 H V V₂ ≤ Source.UL L H V₃)
    (hne : Source.U2 H V V₂ ≠ V) :
    Submodule.span (ZMod 2) {x | ∃ a : A, ∃ s : S₂, x = ρ a (s : _)} = ⊤ := by
  let W := fullOrbit ρ P₂ S₂
  by_contra hn
  have hW : W ≠ ⊤ := fun he => hn (congrArg Subrepresentation.toSubmodule he)
  have hinter' := intersection_le_denominator (Source.UL L H V₃) V (L ⊔ T)
    π hULnorm ρ hρ (Source.UH H V₃) (L₁ ⊔ T) (le_conjugateSpanBy _ _) h₁norm
    (UH_image_spans L H T L₁ V V₃ π hULnorm ρ hρ h₁norm) W hW
  have hkill : Source.U2 H V V₂ ≤ sectionPreimage (Source.UL L H V₃) V W.toSubmodule :=
    (sectionImage_le_iff (Source.UL L H V₃) V (Source.U2 H V V₂) hU₂ W.toSubmodule).mp
      (le_fullOrbit ρ P₂ S₂)
  exact U2_not_le_of_intersection H L₂ V V₂ V₃ _ hgen hKL hinter hinter' hne hkill

/-- A literal proper section is nontrivial; relative normality suffices. -/
theorem section_nontrivial_of_lt {B Z : Subgroup G} [(Z.subgroupOf B).Normal]
    (hZB : Z < B) : Nontrivial (B ⧸ Z.subgroupOf B) := by
  apply QuotientGroup.nontrivial_iff.mpr
  intro he
  apply (not_le_of_gt hZB)
  intro b hb
  have hm : (⟨b, hb⟩ : B) ∈ Z.subgroupOf B := he.symm ▸ mem_top _
  exact hm

/-- Once the two genuine local plane actions are supplied, both survive
with their actions and dimensions in one irreducible quotient. -/
theorem exists_quotient_with_source_images [Finite G]
    [IsIrreducible (S₁).toRepresentation] [IsIrreducible (S₂).toRepresentation]
    (hgen : V = conjugateSpanBy V₃ L₂)
    (hKL : Source.K2 H V₂ ≤ normalizer (L₂ : Set G))
    (hinter : V ⊓ Source.UH H V₃ = V₃)
    (hU₂ : Source.U2 H V V₂ ≤ Source.UL L H V₃)
    (hne : Source.U2 H V V₂ ≠ V) (hproper : V < Source.UL L H V₃)
    (hdim₁ : Module.finrank (ZMod 2) (S₁).toSubmodule = 2)
    (hdim₂ : Module.finrank (ZMod 2) (S₂).toSubmodule = 2) :
    ∃ W : Subrepresentation ρ, W ≠ ⊤ ∧ W.quotientRepresentation.IsIrreducible ∧
      Nonempty ((S₁).toRepresentation.Equiv (localQuotientMap ρ P₁ S₁ W).range.toRepresentation) ∧
      Nonempty ((S₂).toRepresentation.Equiv (localQuotientMap ρ P₂ S₂ W).range.toRepresentation) ∧
      Module.finrank (ZMod 2) (localQuotientMap ρ P₁ S₁ W).range.toSubmodule = 2 ∧
      Module.finrank (ZMod 2) (localQuotientMap ρ P₂ S₂ W).range.toSubmodule = 2 := by
  let : Nontrivial (Source.ULsection L H V₃ V) := section_nontrivial_of_lt hproper
  exact exists_irreducible_quotient_with_local_planes ρ P₁ P₂ S₁ S₂
    (UH_image_spans L H T L₁ V V₃ π hULnorm ρ hρ h₁norm)
    (U2_image_spans L H T L₁ L₂ V V₂ V₃ π hULnorm ρ hρ h₁norm h₂norm
      hgen hKL hinter hU₂ hne) hdim₁ hdim₂

end CFSG.Quasithin.Chapter13.Section08.TransvectionQuotients.FourLocalFactors

open Subgroup Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section08.TransvectionQuotients.FourLocalFactors
open ComponentSieve.AlternatingAndLinear.FourStructure.CriticalTransfer
open ComponentSieve.AlternatingAndLinear.LinearReduction.Parabolics.OrdinarySource
open Theory.SpecificGroups.SymmetricSix.BinaryFlags.NaturalGeometry
variable {G A U : Type*} [Group G] [Group A] [AddCommGroup U] [Module (ZMod 2) U]
  (L H T L₁ L₂ V V₁ V₂ V₃ : Subgroup G)
  [(V.subgroupOf (Source.UL L H V₃)).Normal]
  [IsElementaryAbelian 2 (Source.ULsection L H V₃ V)]
  (π : (L ⊔ T : Subgroup G) →* A)
  (hULnorm : L ⊔ T ≤ normalizer (Source.UL L H V₃ : Set G))
  (ρ : Representation (ZMod 2) A (Additive (Source.ULsection L H V₃ V)))
  (hρ : SectionConjugationAlong (L ⊔ T) (Source.UL L H V₃) V π hULnorm ρ)
  (h₁norm : L₁ ⊔ T ≤ normalizer (Source.UH H V₃ : Set G))
  (h₂norm : L₂ ⊔ T ≤ normalizer (Source.U2 H V V₂ : Set G))
local notation "P₁" => Subgroup.map π (Subgroup.subgroupOf (L₁ ⊔ T) (L ⊔ T))
local notation "P₂" => Subgroup.map π (Subgroup.subgroupOf (L₂ ⊔ T) (L ⊔ T))
local notation "S₁" => localImage (Source.UL L H V₃) V (L ⊔ T) π hULnorm ρ hρ
  (L₁ ⊔ T) (Source.UH H V₃) h₁norm
local notation "S₂" => localImage (Source.UL L H V₃) V (L ⊔ T) π hULnorm ρ hρ
  (L₂ ⊔ T) (Source.U2 H V V₂) h₂norm

/-- Conditional source assembly: calculate both literal image dimensions,
recognize their natural actions and prove both generate the full module.
The commutator identities and actual local S₃ quotients are explicit;
no local irreducibility, local natural equivalence or plane dimension is
assumed. Both planes survive with their actions in a common irreducible
quotient. This is not the final source applicability theorem. -/
theorem local_planes_of_source_commutators [Finite G]
    [IsElementaryAbelian 2 V] [IsMulCommutative (Source.VH H V)]
    (n : NaturalSetup L T V V₁) (hfixed : V ⊓ centralizer (L : Set G) = ⊥)
    (hL₁ : L₁ ≤ L) (hL₂ : L₂ ≤ L)
    (η : Representation (ZMod 2) (Source.Hstar H) U)
    (s : ConjugationSection H (Source.UH H V₃) V₁ η)
    (h13 : V₁ ≤ V₃)
    (E : U ≃ₗ[ZMod 2] BinaryPermutation.natural (Fin 6))
    (hmark : (s.image V₃).map E.toLinearMap = canonicalPlane)
    (hinter : V ⊓ Source.UH H V₃ = V₃)
    (hU : Source.U2 H V V₂ ≤ Source.UL L H V₃)
    (hrank : Module.finrank (ZMod 2) (Additive (Source.U2 H V V₂)) = 6)
    (hcomm₁ : Source.UH H V₃ = ⁅Source.UH H V₃, L₁⁆)
    (hcomm₂ : Source.U2 H V V₂ = ⁅Source.U2 H V V₂, L₂⁆)
    (e₁ : (P₁ ⧸ pCore 2 P₁) ≃* Equiv.Perm (Fin 3))
    (e₂ : (P₂ ⧸ pCore 2 P₂) ≃* Equiv.Perm (Fin 3))
    (hgen : V = conjugateSpanBy V₃ L₂)
    (hKL : Source.K2 H V₂ ≤ normalizer (L₂ : Set G)) :
    NaturalPlane (S₁).toRepresentation e₁ ∧ NaturalPlane (S₂).toRepresentation e₂ ∧
      Submodule.span (ZMod 2) {x | ∃ a : A, ∃ t : S₁, x = ρ a (t : _)} = ⊤ ∧
      Submodule.span (ZMod 2) {x | ∃ a : A, ∃ t : S₂, x = ρ a (t : _)} = ⊤ ∧
      ∃ W : Subrepresentation ρ, W ≠ ⊤ ∧ W.quotientRepresentation.IsIrreducible ∧
        Nonempty ((S₁).toRepresentation.Equiv (localQuotientMap ρ P₁ S₁ W).range.toRepresentation) ∧
        Nonempty ((S₂).toRepresentation.Equiv (localQuotientMap ρ P₂ S₂ W).range.toRepresentation) ∧
        Module.finrank (ZMod 2) (localQuotientMap ρ P₁ S₁ W).range.toSubmodule = 2 ∧
        Module.finrank (ZMod 2) (localQuotientMap ρ P₂ S₂ W).range.toSubmodule = 2 := by
  have hd₁ := UH_image_finrank L H V V₁ V₃ η s h13 E hmark hinter
  obtain ⟨hd₂, hne⟩ := U2_image_finrank L H T V V₁ V₂ V₃ n hfixed hU hrank
  have hp₁ := localImage_natural (Source.UL L H V₃) V (L ⊔ T) π hULnorm ρ hρ
    (L₁ ⊔ T) (Source.UH H V₃) L₁ h₁norm le_sup_left (sup_le_sup hL₁ le_rfl)
    (le_conjugateSpanBy _ _) hcomm₁ hd₁ e₁
  have hp₂ := localImage_natural (Source.UL L H V₃) V (L ⊔ T) π hULnorm ρ hρ
    (L₂ ⊔ T) (Source.U2 H V V₂) L₂ h₂norm le_sup_left (sup_le_sup hL₂ le_rfl)
    hU hcomm₂ hd₂ e₂
  let : (S₁).toRepresentation.IsIrreducible := hp₁.2.1
  let : (S₂).toRepresentation.IsIrreducible := hp₂.2.1
  have hproper : V < Source.UL L H V₃ := by
    apply lt_of_le_of_ne ((Source.seed_le_U2 H V V₂).trans hU)
    intro he
    apply hne
    exact le_antisymm (hU.trans he.symm.le) (Source.seed_le_U2 H V V₂)
  exact ⟨hp₁, hp₂,
    UH_image_spans L H T L₁ V V₃ π hULnorm ρ hρ h₁norm,
    U2_image_spans L H T L₁ L₂ V V₂ V₃ π hULnorm ρ hρ h₁norm h₂norm hgen hKL hinter hU hne,
    exists_quotient_with_source_images L H T L₁ L₂ V V₂ V₃ π hULnorm ρ hρ h₁norm h₂norm
      hgen hKL hinter hU hne hproper hd₁ hd₂⟩
end CFSG.Quasithin.Chapter13.Section08.TransvectionQuotients.FourLocalFactors

end
