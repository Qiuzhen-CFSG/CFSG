module

public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.Suzuki.NaturalSections.SourceAction
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.Suzuki.NaturalSections.MovedSpace
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.Swapped.LinearTwo.ModuleAlternatives.SourceSeed

/-!
# Comparing the group seed with its binary image

The literal image of V₃ in U_H/V₁ has cardinality |V₃:V₃∩V₁|,
by the kernel of the actual quotient map. The source index four gives
its binary dimension two. Pulling invariant subspaces back to ambient
subgroups transports the earlier irreducibility criterion. Thus the
seed equals its L₁*-commutator, and its spanning H*-orbit gives the
full commutator identity when relative normality is supplied.

The group irreducibility and index statements are earlier source inputs;
no new module irreducibility assumption or splitting is used.

Source: Aschbacher–Smith, combined manuscript (1 March 2004),
13.7.3(6), printed p.936, the setup on pp.946–947, and the seed
identity in the proof of 13.8.16, p.953.
-/

@[expose] public noncomputable section

open Subgroup Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section08.Components.Suzuki.NaturalSections
open ComponentSieve.AlternatingAndLinear.FourStructure.ChiefFactors
variable {G : Type*} [Group G] [Finite G] (H V₃ V₁ : Subgroup G)
  [(V₁.subgroupOf (Source.UH H V₃)).Normal]
  [IsElementaryAbelian 2 (Source.Utilde H V₃ V₁)]

omit [Finite G] in
/-- The source seed has the order of the literal quotient V₃/V₁. -/
theorem sourceSeed_card_eq_index :
    Nat.card (sourceSeedSpace H V₃ V₁) = (V₁.subgroupOf V₃).index := by
  let f : V₃ →* Source.Utilde H V₃ V₁ :=
    (sourceProjection H V₃ V₁).comp (inclusion (le_conjugateSpanBy V₃ H))
  have hf : f.ker = V₁.subgroupOf V₃ := by
    ext v
    exact QuotientGroup.eq_one_iff _
  let e : f.range ≃ sourceSeedSpace H V₃ V₁ :=
    { toFun := fun x => ⟨Additive.ofMul x, by
        obtain ⟨v, hv⟩ := x.property
        exact ⟨inclusion (le_conjugateSpanBy V₃ H) v, v.property, hv⟩⟩
      invFun := fun x => ⟨x.val.toMul, by
        obtain ⟨v, hv, he⟩ := x.property
        exact ⟨⟨v, hv⟩, he⟩⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [← Nat.card_congr e, ← index_ker, hf]

/-- The source index four gives the binary plane on the actual carrier. -/
theorem sourceSeed_finrank_two (hindex : (V₁.subgroupOf V₃).index = 4) :
    Module.finrank (ZMod 2) (sourceSeedSpace H V₃ V₁) = 2 := by
  have hc := sourceSeed_card_eq_index H V₃ V₁
  rw [hindex, Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod] at hc
  exact Nat.pow_right_injective (by decide : 1 < 2) hc

variable (ρ : Representation (ZMod 2) (Source.Hstar H) (SourceSpace H V₃ V₁))
  (hρ : IsSourceAction H V₃ V₁ ρ)

include hρ

/-- The invariant-subgroup formulation of the earlier source irreducibility
and its index four imply the exact seed commutator identity. -/
theorem sourceSeed_generated_of_group_irreducible
    (L : Subgroup G) (hLH : L ≤ H) (hn : L ≤ normalizer (V₃ : Set G))
    (hline : V₁ < V₃) (hindex : (V₁.subgroupOf V₃).index = 4)
    (hirr : ∀ X : Subgroup G, V₁ ≤ X → X ≤ V₃ →
      L ≤ normalizer (X : Set G) → X = V₁ ∨ X = V₃) :
    subspaceCommutator ρ (sourceSeedSpace H V₃ V₁) (Source.starImage H L) =
      sourceSeedSpace H V₃ V₁ := by
  have hi := Swapped.LinearTwo.ModuleAlternatives.markedSeed_irreducible
    H V₃ V₁ ρ hρ L hLH hn hline hirr
  have ha := (Subrepresentation.irreducible_iff_isAtom _).mp hi
  exact irreducible_seed_generated ρ _ _ (sourceSeed_stable H V₃ V₁ ρ hρ L hn) ha
    (by rw [sourceSeed_finrank_two H V₃ V₁ hindex]; decide)

/-- Relative normality propagates the established seed identity through
its actual spanning H*-orbit. -/
theorem source_generated_of_group_irreducible
    (L : Subgroup G) (hLH : L ≤ H) (hn : L ≤ normalizer (V₃ : Set G))
    (hline : V₁ < V₃) (hindex : (V₁.subgroupOf V₃).index = 4)
    (hirr : ∀ X : Subgroup G, V₁ ≤ X → X ≤ V₃ →
      L ≤ normalizer (X : Set G) → X = V₁ ∨ X = V₃)
    (hLn : (Source.starImage H L).Normal) :
    subspaceCommutator ρ ⊤ (Source.starImage H L) = ⊤ := by
  let := hLn
  apply commutator_top_of_orbit_seed ρ ⊤ (Source.starImage H L)
    (sourceSeedSpace H V₃ V₁) le_normalizer_of_normal
  · exact sourceSeed_generated_of_group_irreducible H V₃ V₁ ρ hρ L hLH hn hline hindex hirr
  · simpa using sourceSeed_orbit_span H V₃ V₁ ρ hρ

end CFSG.Quasithin.Chapter13.Section08.Components.Suzuki.NaturalSections

end
