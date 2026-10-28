module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Parameters.RootGeometry.FieldKernel
public import Theory.Representation.SymplecticNaturalNormalizer.FixedLineInner
public import Theory.Representation.BinaryOffender.ComponentPermutationObstruction

/-!
# Inner A₂ actors for the original symplectic natural module

The coefficient kernel has index at most two. Exact fixed-vector lifting
through the original orthogonal cover makes the A₂ equality descend to the
natural quotient, where it removes the field action. A field-linear
involution fixes a nonzero field line; the symplectic normalizer calculation
then makes it inner. Faithfulness and the literal Sylow intersection lift
the conclusion to L O₂(LT), without splitting the central attachment.

Source: Aschbacher--Smith I.2.3 and 11.2.2(4), printed pp.413,768.
The Source endpoint applies the result to the actual indexed weak closure.
-/

public noncomputable section
open scoped IsMulCommutative
open Subgroup Representation Representation.BinaryOffender
open CFSG.Quasithin.ChapterE
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Parameters.RootActors
open Theory.SpecificGroups.SymplecticFour
open SymplecticConjugatePair.Ambient SymplecticConjugatePair.Ambient.Normalizer
open SemilinearCoefficients
variable {H F : Type*} [Group H] [Field F] [Finite F] [CharP F 2] [Algebra (ZMod 2) F]

/-- A field-linear square-one actor in the faithful natural symplectic
normalizer belongs to the actual marked component. -/
theorem symplectic_field_linear_square_one_mem
    (K : Subgroup H) [K.Normal] (e : K ≃* Sp F)
    (ρ : Representation (ZMod 2) H (Vector F)) (hρ : Function.Injective ρ)
    (hK : ∀ (g : K) v, ρ (g : H) v = symplecticNatural 2 (e g) v)
    (hq : 2 < Nat.card F) (a : H) (ha : a ^ 2 = 1)
    (hlin : ∀ (c : F) v, ρ a (c • v) = c • ρ a v) : a ∈ K := by
  obtain ⟨v,hv⟩ := exists_ne (0 : Vector F)
  have hfixed : ∃ w : Vector F, w ≠ 0 ∧ ρ a w = w := by
    by_cases hh : ρ a v = v
    · exact ⟨v,hv,hh⟩
    · exact ⟨ρ a v - v, sub_ne_zero.mpr hh,
        involution_fixes_displacement ρ (by simpa only [pow_two] using ha) v⟩
  obtain ⟨w,hw,hfix⟩ := hfixed
  let s : naturalNormalizer (F := F) := ⟨linearAction ρ a,
    SymplecticNaturalNormalizer.operator_mem_naturalNormalizer K hq e ρ hK a⟩
  have hs : s ^ 2 = 1 := Subtype.ext (by
    change linearAction ρ a ^ 2 = 1
    rw [← map_pow,ha,map_one])
  obtain ⟨g,hg⟩ := SymplecticNaturalNormalizer.conjugation_inner_of_fixes_field_line
    hq s w hw (fun c => by change ρ a (c • w) = c • w; rw [hlin,hfix])
  have hin : s.val ∈ naturalDerivedImage := by
    by_contra hout
    exact SymplecticNaturalNormalizer.conjugation_not_inner hq s hs hout ⟨g,hg.symm⟩
  obtain ⟨b,hb⟩ := hin
  have heq : a = e.symm b.val := hρ (by
    apply LinearMap.ext
    intro v
    rw [hK,e.apply_symm_apply]
    exact (congrArg (fun t : Vector F ≃ₗ[ZMod 2] Vector F => t v) hb).symm)
  rw [heq]
  exact (e.symm b.val).property

open CFSG.Quasithin.Chapter12.Section02 CFSG.Quasithin.ChapterB.QuasisimpleSource
open FullAutomizer
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)

/-- Every A₂ actor of the literal symplectic automizer is inner, including
nonsplit central covers and even coefficient degrees. -/
theorem sp4_original_two_family_inner
    (m : ActionEquiv D.centralQuotientAction
      (restrictScalars (k := ZMod 2) (symplecticNatural (k := S.field.Carrier) 2))) :
    letI := D.elementary
    ∀ A : Subgroup (Automizer V),
      A ∈ fixedSpaceFamily (automizerRepresentation V) 2 → A ≤ inducedAutomizer V L := by
  let := D.elementary
  intro A hA
  let c := Coordinates.sp4 m
  let : Finite c.Space := Finite.of_surjective c.projection c.projection_surjective
  let : Nontrivial c.Space := inferInstanceAs (Nontrivial (Vector S.field.Carrier))
  obtain ⟨ρ,hρ,he,hres⟩ := exists_faithful_quotient_action D S c
  let := layer_normal D S
  have hq : 2 < Nat.card S.field.Carrier := by
    rw [S.field.card_eq]
    exact Nat.pow_lt_pow_right (by decide : 1 < 2) S.nonbinary
  have hsemi : ∀ a : Automizer V, ∃ σ : S.field.Carrier ≃+* S.field.Carrier,
      ∀ (r : S.field.Carrier) v, ρ a (r • v) = σ r • ρ a v := by
    intro a
    exact SymplecticNaturalNormalizer.exists_field_twist ⟨linearAction ρ a,
      SymplecticNaturalNormalizer.operator_mem_naturalNormalizer
        (inducedAutomizer V L) hq (layerEquiv D S c) ρ hres a⟩
  let π := coefficientHom ρ hsemi
  have hπ := coefficientHom_smul ρ hsemi
  apply two_family_inner_of_fixed_lifting (inducedAutomizer V L)
    (automizerRepresentation V) ρ (projectionLinear D S c)
    (projectionLinear_surjective D S c) he π hπ _
    (original_layer_fixed_lifts D S c ρ hres) hA
  intro a ha hk
  exact symplectic_field_linear_square_one_mem (inducedAutomizer V L)
    (layerEquiv D S c) ρ hρ hres hq a ha
    ((coefficient_eq_one_iff ρ π hπ a).mp hk)

/-- The source inner-actor containment in the literal original Sylow group. -/
theorem sp4_two_family
    (m : ActionEquiv D.centralQuotientAction
      (restrictScalars (k := ZMod 2) (symplecticNatural (k := S.field.Carrier) 2))) :
    letI := D.elementary
    ∀ A : Subgroup G, A ≤ (T : Subgroup G) →
      inducedAutomizer V A ∈ fixedSpaceFamily (automizerRepresentation V) 2 →
      A ≤ L ⊔ (L ⊔ (T : Subgroup G)).pCoreIn 2 := by
  let := D.elementary
  intro A hAT hA
  exact le_component_join_core_of_image D S hAT
    (sp4_original_two_family_inner D S m _ hA)
end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Parameters.RootActors
