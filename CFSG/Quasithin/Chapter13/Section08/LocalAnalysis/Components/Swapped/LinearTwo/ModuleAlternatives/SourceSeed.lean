module

public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.Swapped.LinearTwo.ModuleAlternatives.SourceAction
public import Theory.Representation.BinaryOffender.IrreducibleSection

/-!
# Marked seed properties in the literal source quotient

Subspaces of U_H/V₁ are pulled back through the quotient into the ambient
group. The earlier invariant-subgroup criterion between V₁ and V₃ then
proves irreducibility of the marked seed action. Normalization gives
invariance, a commutator bound modulo V₁ gives fixation, and generation
modulo V₁ gives full linear commutator generation. No splitting of V₃
above V₁, or module classification, is assumed.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
standing setup on printed pp.946–947 and proof of 13.8.16(1), p.952.
-/

@[expose] public noncomputable section
open Subgroup Representation
open scoped IsMulCommutative commutatorElement

namespace CFSG.Quasithin.Chapter13.Section08.Components.Swapped.LinearTwo.ModuleAlternatives
open Representation.BinaryOffender ComponentSieve.AlternatingAndLinear.FourStructure
variable {G : Type*} [Group G] (H V₃ V₁ : Subgroup G)
  [(V₁.subgroupOf (Source.UH H V₃)).Normal]
  [IsElementaryAbelian 2 (Source.Utilde H V₃ V₁)]

/-- The literal image of a subgroup in the source quotient. -/
def image (X : Subgroup G) : Submodule (ZMod 2) (ChiefFactors.SourceSpace H V₃ V₁) :=
  AddSubgroup.toZModSubmodule 2
    (((X.subgroupOf (Source.UH H V₃)).map (ChiefFactors.sourceProjection H V₃ V₁)).toAddSubgroup)

@[simp] theorem image_seed : image H V₃ V₁ V₃ = ChiefFactors.sourceSeedSpace H V₃ V₁ := rfl

/-- Pull a subspace back through the literal quotient and into the ambient group. -/
def preimage (W : Submodule (ZMod 2) (ChiefFactors.SourceSpace H V₃ V₁)) : Subgroup G :=
  ((Subgroup.toAddSubgroup.symm W.toAddSubgroup).comap
    (ChiefFactors.sourceProjection H V₃ V₁)).map (Source.UH H V₃).subtype

theorem mem_preimage (W : Submodule (ZMod 2) (ChiefFactors.SourceSpace H V₃ V₁))
    (u : Source.UH H V₃) :
    (u : G) ∈ preimage H V₃ V₁ W ↔
      Additive.ofMul (ChiefFactors.sourceProjection H V₃ V₁ u) ∈ W := by
  constructor
  · rintro ⟨w, hw, he⟩
    exact (Subtype.ext he : w = u) ▸ hw
  · intro hu
    exact ⟨u, hu, rfl⟩

theorem line_le_preimage (hV₁ : V₁ ≤ Source.UH H V₃)
    (W : Submodule (ZMod 2) (ChiefFactors.SourceSpace H V₃ V₁)) :
    V₁ ≤ preimage H V₃ V₁ W := by
  intro v hv
  apply (mem_preimage H V₃ V₁ W ⟨v, hV₁ hv⟩).mpr
  have hz : ChiefFactors.sourceProjection H V₃ V₁ ⟨v, hV₁ hv⟩ = 1 :=
    (QuotientGroup.eq_one_iff _).mpr hv
  rw [hz]
  exact W.zero_mem

theorem preimage_le_UH (W : Submodule (ZMod 2) (ChiefFactors.SourceSpace H V₃ V₁)) :
    preimage H V₃ V₁ W ≤ Source.UH H V₃ := map_subtype_le _

theorem image_le_iff (X : Subgroup G) (hX : X ≤ Source.UH H V₃)
    (W : Submodule (ZMod 2) (ChiefFactors.SourceSpace H V₃ V₁)) :
    image H V₃ V₁ X ≤ W ↔ X ≤ preimage H V₃ V₁ W := by
  constructor
  · intro he x hx
    exact (mem_preimage H V₃ V₁ W ⟨x, hX hx⟩).mpr (he ⟨⟨x, hX hx⟩, hx, rfl⟩)
  · rintro he _ ⟨u, hu, rfl⟩
    exact (mem_preimage H V₃ V₁ W u).mp (he hu)

/-- A seed properly above V₁ has nonzero image, independently of classification. -/
theorem seed_ne_bot (hne : ¬ V₃ ≤ V₁) : ChiefFactors.sourceSeedSpace H V₃ V₁ ≠ ⊥ := by
  intro hz
  apply hne
  intro v hv
  let u : Source.UH H V₃ := ⟨v, le_conjugateSpanBy V₃ H hv⟩
  have hu : Additive.ofMul (ChiefFactors.sourceProjection H V₃ V₁ u) ∈
      ChiefFactors.sourceSeedSpace H V₃ V₁ := ⟨u, hv, rfl⟩
  rw [hz] at hu
  exact (QuotientGroup.eq_one_iff u).mp hu

variable (ρ : Representation (ZMod 2) (Source.Hstar H) (ChiefFactors.SourceSpace H V₃ V₁))
  (hρ : ChiefFactors.IsSourceAction H V₃ V₁ ρ)

include hρ

/-- Ambient normalization gives invariance under the actual marked actor image. -/
theorem image_stable (A X : Subgroup G) (hAX : A ≤ normalizer (X : Set G)) :
    Source.starImage H A ≤ subspaceStabilizer ρ (image H V₃ V₁ X) := by
  apply le_subspaceStabilizer
  rintro _ ⟨a, ha, rfl⟩ _ ⟨u, hu, rfl⟩
  change ρ (QuotientGroup.mk' (pCore 2 H) a)
    (Additive.ofMul (ChiefFactors.sourceProjection H V₃ V₁ u)) ∈ image H V₃ V₁ X
  rw [hρ]
  exact ⟨ChiefFactors.sourceConjugate H V₃ a u,
    (mem_normalizer_iff.mp (hAX ha) u).mp hu, rfl⟩

/-- The marked seed subrepresentation has exactly the source seed as its carrier. -/
def markedSeed (L : Subgroup G) (hL : L ≤ normalizer (V₃ : Set G)) :
    Subrepresentation (ρ.comp (Source.starImage H L).subtype) :=
  invariantSubspace ρ (Source.starImage H L) (ChiefFactors.sourceSeedSpace H V₃ V₁)
    (image_stable H V₃ V₁ ρ hρ L V₃ hL)

/-- Linear displacements are the images of the actual group commutators. -/
theorem displacement (a : H) (u : Source.UH H V₃) :
    ρ (QuotientGroup.mk' (pCore 2 H) a) (Additive.ofMul (ChiefFactors.sourceProjection H V₃ V₁ u)) -
      Additive.ofMul (ChiefFactors.sourceProjection H V₃ V₁ u) =
      Additive.ofMul (ChiefFactors.sourceProjection H V₃ V₁
        (ChiefFactors.sourceConjugate H V₃ a u * u⁻¹)) := by
  rw [hρ, map_mul, map_inv]
  exact sub_eq_add_neg _ _

/-- A source commutator bound modulo V₁ gives fixation of the literal seed image. -/
theorem image_fixed (A X : Subgroup G) (hc : ⁅A, X⁆ ≤ V₁) :
    image H V₃ V₁ X ≤ fixedSpace ρ (Source.starImage H A) := by
  rintro _ ⟨u, hu, rfl⟩ ⟨_, a, ha, rfl⟩
  change ρ (QuotientGroup.mk' (pCore 2 H) a)
    (Additive.ofMul (ChiefFactors.sourceProjection H V₃ V₁ u)) =
      Additive.ofMul (ChiefFactors.sourceProjection H V₃ V₁ u)
  apply sub_eq_zero.mp
  rw [displacement H V₃ V₁ ρ hρ]
  change ChiefFactors.sourceProjection H V₃ V₁ (ChiefFactors.sourceConjugate H V₃ a u * u⁻¹) = 1
  exact (QuotientGroup.eq_one_iff _).mpr (hc (commutator_mem_commutator ha hu))

/-- Commutator generation modulo the actual line descends to the seed.
The line is allowed as a supplement; equality [V₃,L]=V₃ is not imposed. -/
theorem image_commutator_eq (A X : Subgroup G) (hAH : A ≤ H)
    (hXU : X ≤ Source.UH H V₃) (hAX : A ≤ normalizer (X : Set G))
    (hV₁U : V₁ ≤ Source.UH H V₃) (hgen : X ≤ ⁅A, X⁆ ⊔ V₁) :
    subspaceCommutator ρ (image H V₃ V₁ X) (Source.starImage H A) = image H V₃ V₁ X := by
  let C := subspaceCommutator ρ (image H V₃ V₁ X) (Source.starImage H A)
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨a, ha, u, hu, rfl⟩
    exact (image H V₃ V₁ X).sub_mem
      ((image_stable H V₃ V₁ ρ hρ A X hAX ha u).mpr hu) hu
  · apply (image_le_iff H V₃ V₁ X hXU C).mpr
    apply hgen.trans
    apply sup_le _ (line_le_preimage H V₃ V₁ hV₁U C)
    apply commutator_le.mpr
    intro a ha x hx
    let aH : H := ⟨a, hAH ha⟩
    let u : Source.UH H V₃ := ⟨x, hXU hx⟩
    have hd := Submodule.subset_span (R := ZMod 2)
      (s := {v | ∃ a ∈ Source.starImage H A, ∃ w ∈ image H V₃ V₁ X, v = ρ a w - w})
      ⟨QuotientGroup.mk' (pCore 2 H) aH, ⟨aH, ha, rfl⟩,
        Additive.ofMul (ChiefFactors.sourceProjection H V₃ V₁ u), ⟨u, hx, rfl⟩, rfl⟩
    rw [displacement H V₃ V₁ ρ hρ] at hd
    exact (mem_preimage H V₃ V₁ C (ChiefFactors.sourceConjugate H V₃ aH u * u⁻¹)).mpr hd

/-- A subspace invariant under a marked image pulls back to a normalized
ambient subgroup. This is relative normalization, not ambient normality. -/
theorem preimage_normalized (A : Subgroup G) (hAH : A ≤ H)
    (W : Subrepresentation (ρ.comp (Source.starImage H A).subtype)) :
    A ≤ normalizer (preimage H V₃ V₁ W.toSubmodule : Set G) := by
  apply le_normalizer_iff.mpr
  rintro a ha x ⟨u, hu, rfl⟩
  refine ⟨ChiefFactors.sourceConjugate H V₃ ⟨a, hAH ha⟩ u, ?_, rfl⟩
  change Additive.ofMul (ChiefFactors.sourceProjection H V₃ V₁
    (ChiefFactors.sourceConjugate H V₃ ⟨a, hAH ha⟩ u)) ∈ W
  rw [← hρ]
  exact W.apply_mem_toSubmodule
    ⟨QuotientGroup.mk' (pCore 2 H) ⟨a, hAH ha⟩, ⟨⟨a, hAH ha⟩, ha, rfl⟩⟩ hu

/-- The earlier source irreducibility of V₃/V₁ is transported from its
literal invariant-subgroup criterion; it is not an assumption on a new module. -/
theorem markedSeed_irreducible (L : Subgroup G) (hLH : L ≤ H)
    (hL : L ≤ normalizer (V₃ : Set G)) (hline : V₁ < V₃)
    (hirr : ∀ X : Subgroup G, V₁ ≤ X → X ≤ V₃ →
      L ≤ normalizer (X : Set G) → X = V₁ ∨ X = V₃) :
    IsIrreducible (markedSeed H V₃ V₁ ρ hρ L hL).toRepresentation := by
  apply (Subrepresentation.irreducible_iff_isAtom _).mpr
  refine ⟨?_, ?_⟩
  · intro hz
    exact seed_ne_bot H V₃ V₁ (not_le_of_gt hline)
      (congrArg Subrepresentation.toSubmodule hz)
  · intro W hW
    have hle : W.toSubmodule ≤ image H V₃ V₁ V₃ := hW.le
    let X := preimage H V₃ V₁ W.toSubmodule
    have hlineU : V₁ ≤ Source.UH H V₃ := hline.le.trans (le_conjugateSpanBy V₃ H)
    have hXV : X ≤ V₃ := by
      rintro x ⟨u, hu, rfl⟩
      obtain ⟨v, hv, he⟩ := hle hu
      have hd : v / u ∈ V₁.subgroupOf (Source.UH H V₃) :=
        QuotientGroup.eq_iff_div_mem.mp he
      have hm := V₃.mul_mem (V₃.inv_mem (hline.le hd)) hv
      change ((v : G) / (u : G))⁻¹ * (v : G) ∈ V₃ at hm
      change (u : G) ∈ V₃
      simpa only [inv_div, div_mul_cancel] using hm
    rcases hirr X (line_le_preimage H V₃ V₁ hlineU W.toSubmodule) hXV
      (preimage_normalized H V₃ V₁ ρ hρ L hLH W) with he | he
    · apply Subrepresentation.toSubmodule_injective
      apply le_antisymm _ bot_le
      intro w hw
      obtain ⟨u, rfl⟩ := QuotientGroup.mk'_surjective
        (V₁.subgroupOf (Source.UH H V₃)) w.toMul
      have hu : (u : G) ∈ X := (mem_preimage H V₃ V₁ W.toSubmodule u).mpr hw
      rw [he] at hu
      exact (QuotientGroup.eq_one_iff u).mpr hu
    · exfalso
      apply hW.ne
      apply le_antisymm hW.le
      rintro _ ⟨u, hu, rfl⟩
      apply (mem_preimage H V₃ V₁ W.toSubmodule u).mp
      change (u : G) ∈ X
      rw [he]
      exact hu

end CFSG.Quasithin.Chapter13.Section08.Components.Swapped.LinearTwo.ModuleAlternatives
