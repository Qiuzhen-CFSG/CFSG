module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.FFSections.SourceOrbit.Selection
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.SeedAction
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.Basic

/-!
# The complete earlier F.9.18(4) implication

This is an input contract, not a proof of F.9.18. It retains the standing
F.9.1 and F.9.8 hypotheses, the SQTK and C-component hypotheses of F.9.18,
the actual T-conjugate span K₀, and K = K₀. Its conclusion retains the full
component list and all three module alternatives, for every homogeneous
constituent. No external cubic subgroup or selected constituent occurs in
the universal implication.

The irreducibility clause is expressed by the lattice of invariant
subgroups between V₁ and V₊; these are exactly the binary subspaces because
V is elementary abelian. The R₂ clause uses the intrinsic centralizer
quotient in LT. All other centralizers modulo V₁ use commutatorPreimage,
with local normalization supplied by the standing hypotheses. The source
line is represented by its order-two subgroup, so centralizing that subgroup
is precisely centralizing its unique nonidentity element z.

F.9.2(3),(4), the conjugation representation, its faithful quotient and its
Sylow marking remain explicit earlier outputs. They identify the source's
H/C_H(Ũ_H) with the literal H/O₂(H) used by this development.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, F.9.1,
pp.317–318; F.9.8, p.321; F.9.18(4), pp.325–326.
-/

@[expose] public section

open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative

namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.FFSections.SourceOrbit

universe u
variable {G : Type u} [Group G]

/-- Right conjugation, as in the source notation V^g. -/
def sourceConjugate (A : Subgroup G) (g : G) : Subgroup G :=
  A.map (MulAut.conj g⁻¹).toMonoidHom

/-- All standing group hypotheses F.9.1 and F.9.8, without any conclusion
of F.9.18. The ambient group is finite at each use of this contract. -/
structure F9Setup (H L L₁ T V V₃ V₁ : Subgroup G) : Prop where
  sylow : ∃ S : Sylow 2 G, (S : Subgroup G) = T
  elementary : IsElementaryAbelian 2 V
  residual : IsPPerfect 2 L
  normalized : T ≤ normalizer L
  characteristicTwo : generalizedFitting L = pCore 2 L
  module_le : V ≤ L ⊔ T
  reduced : ∃ h : (V.subgroupOf (L ⊔ T)).Normal,
    letI := h
    pCore 2 ((L ⊔ T : Subgroup G) ⧸
      centralizer (V.subgroupOf (L ⊔ T) : Set ↥(L ⊔ T))) = ⊥
  centralizer : T ⊓ Subgroup.centralizer (V : Set G) = (L ⊔ T).pCoreIn 2
  line_order : Nat.card V₁ = 2
  line_normalized : T ≤ normalizer V₁
  line_lt : V₁ < V₃
  seed_le : V₃ ≤ V
  localResidual : L₁ = (pResidual 2 ↥(L ⊓ Subgroup.centralizer (V₁ : Set G))).map
    (L ⊓ Subgroup.centralizer (V₁ : Set G)).subtype
  local_le : L₁ ⊔ T ≤ H
  fixes_line : H ≤ Subgroup.centralizer (V₁ : Set G)
  localCharacteristicTwo : generalizedFitting H = pCore 2 H
  core_bound : ((commutatorPreimage H V₃ V₁).subgroupOf H).normalCore ≤ pCore 2 H
  seed_normalized : L₁ ⊔ T ≤ normalizer V₃
  seed_irreducible : ∀ W : Subgroup G, V₁ ≤ W → W ≤ V₃ →
    L₁ ⊔ T ≤ normalizer W → W = V₁ ∨ W = V₃
  seed_normalizer : H ⊓ normalizer V₃ ≤ normalizer V
  generated_core : pCore 2 (L ⊔ T ⊔ H : Subgroup G) = ⊥
  commuting_lifts : ∀ g ∈ H,
    ⁅V, sourceConjugate V g⁆ ≤ V ⊓ sourceConjugate V g →
    ⁅V₃, sourceConjugate V g⁆ ≤ V₁ →
    ⁅sourceConjugate V₃ g, V⁆ ≤ V₁ →
    ⁅V₃, sourceConjugate V g⁆ = ⊥ ∧ ⁅sourceConjugate V₃ g, V⁆ = ⊥
  commuting_conjugates : ∀ g : G, V₁ ≤ sourceConjugate V g →
    ⁅V, sourceConjugate V g⁆ = ⊥
  seed_centralizer :
    ⁅V, H ⊓ Subgroup.centralizer (V₃ : Set G)⁆ ≤ V₁ ∨
    (∀ x ∈ H ⊓ Subgroup.centralizer (V₃ : Set G), ⁅V, zpowers x⁆ ≠ ⊥ →
      ∀ g : G, sourceConjugate V g ≤ normalizer (⁅V, zpowers x⁆ : Subgroup G) →
        sourceConjugate V g ≤ Subgroup.centralizer (V : Set G))

variable (H K L L₁ T V V₃ V₁ : Subgroup G)
  [(V₁.subgroupOf (Source.UH H V₃)).Normal]
  [IsElementaryAbelian 2 (Source.Utilde H V₃ V₁)]
  (ρ : Representation (ZMod 2) (Source.Hstar H) (SeedAction.Space H V₃ V₁))
  (P : Sylow 2 (Source.Hstar H))

/-- The genuine F.9.18 hypotheses for clause (4), together with the exact
earlier quotient and overlap identifications used to express it here. -/
structure F918Hypotheses (𝒦 : GroupClass.{u}) : Prop where
  setup : F9Setup H L L₁ T V V₃ V₁
  sqtk : IsSQTK 𝒦 H
  component_le : K ≤ H
  component : (K.subgroupOf H).IsCComponent
  quasisimple_quotient : IsQuasisimple (K ⧸ pCore 2 K)
  generation : H = conjugateSpanBy K T ⊔ ((L ⊔ T) ⊓ H)
  single_component : conjugateSpanBy K T = K
  overlap : (L ⊔ T) ⊓ H = L₁ ⊔ T
  kernel : commutatorPreimage H (Source.UH H V₃) V₁ = Source.QH H
  conjugation : SeedAction.IsConjugation H V₃ V₁ ρ
  faithful : Function.Injective ρ
  sylow_image : (P : Subgroup (Source.Hstar H)) = Source.starImage H T

/-- The complete universal earlier implication F.9.18(4). The parent must
supply this source theorem; none of its alternatives is selected in the input. -/
def FullF918Four (𝒦 : GroupClass.{u}) : Prop :=
  ∀ (G : Type u) [Group G] [Finite G]
    (H K L L₁ T V V₃ V₁ : Subgroup G)
    [(V₁.subgroupOf (Source.UH H V₃)).Normal]
    [IsElementaryAbelian 2 (Source.Utilde H V₃ V₁)]
    [(Source.starImage H K).Normal]
    (ρ : Representation (ZMod 2) (Source.Hstar H) (SeedAction.Space H V₃ V₁))
    (P : Sylow 2 (Source.Hstar H)),
    F918Hypotheses H K L L₁ T V V₃ V₁ ρ P 𝒦 →
      FourConclusion ρ (Source.starImage H K) P

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.FFSections.SourceOrbit
