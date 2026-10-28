module
public import CFSG.Quasithin.Chapter2.Section04.CoreSource
public import CFSG.Quasithin.Chapter2.Section04.DoubleA3.SourceCoordinates

/-!
# The correlated source geometry in the paired cubic branch

The source component is normal in the literal centralizer C_G(z₂). The
Thompson subgroup is the original J(S), and all action markings use its
actual conjugation on that component. The later factor and fusion data
refer to the same component, involution and conjugator. Their consumer
applies the proved terminal counting contradiction without an additional
quotient-coordinate or surjectivity premise.

These records separate the source constructions in 2.4.32–35 and 2.4.36–37;
they do not assert either construction. Source: Aschbacher–Smith §2.4,
printed pp.547–550 (combined manuscript, 1 March 2004).
-/

@[expose] public section
open Subgroup Stellmacher
namespace CFSG.Quasithin.Chapter2.DoubleA3
open AlternatingSix.ShadowLocal
variable {G : Type*} [Group G] [Finite G] {M : Subgroup G}

/-- The actual Thompson subgroup denoted R in the final paired-cubic proof. -/
noncomputable abbrev sourceR (d : MinimalBlockSetup M) : Subgroup G :=
  elementaryAbelianMaxJ ((d.S : Subgroup d.H).map d.H.subtype)

/-- The normal A₆ and the two outer actions selected by source 2.4.32–35.
The component, its action, and the original Thompson subgroup are correlated. -/
structure SourceComponentGeometry (d : MinimalBlockSetup M) where
  z : G
  involution : z ^ 2 = 1
  nonidentity : z ≠ 1
  K : Subgroup (involutionCentralizer z)
  normal : K.Normal
  componentEquiv : K ≃* A6
  thompson_le : sourceR d ≤ involutionCentralizer z
  S₁ : Sylow 2 (involutionCentralizer z)
  thompson_sylow : (sourceR d).subgroupOf (involutionCentralizer z) ≤ (S₁ : Subgroup _)
  u : involutionCentralizer z
  x : involutionCentralizer z
  σ : Equiv.Perm (Fin 6)
  swap : σ.IsSwap
  transposition : letI := normal
    conjugationAction K componentEquiv u = permutationAction σ
  outside_natural : letI := normal
    conjugationAction K componentEquiv x ∉ natural
  natural_thompson : letI := normal
    ((sourceR d).subgroupOf (involutionCentralizer z)).map
      (conjugationAction K componentEquiv) ≤ natural
  s : G
  z₁ : involutionCentralizer z
  first_in_thompson : z₁ ∈ (sourceR d).subgroupOf (involutionCentralizer z)
  first_in_component : z₁ ∈ K
  exchange : s⁻¹ * (z₁ : G) * s = z

attribute [instance] SourceComponentGeometry.normal

/-- Source 2.4.36–37 on the same component, involution and conjugator.
The second factor is the actual right conjugate of the component Sylow. -/
structure SourceFactorGeometry {d : MinimalBlockSetup M} (c : SourceComponentGeometry d) where
  centralizer_le : centralizer (c.K : Set (involutionCentralizer c.z)) ≤
    (sourceR d).subgroupOf (involutionCentralizer c.z)
  centralizerEquiv : centralizer (c.K : Set (involutionCentralizer c.z)) ≃*
    Multiplicative (ZMod 4)
  P : Sylow 2 c.K
  component_sylow : (P : Subgroup c.K).map c.K.subtype =
    (sourceR d).subgroupOf (involutionCentralizer c.z) ⊓ c.K
  E : Subgroup (involutionCentralizer c.z)
  second_factor : E.map (involutionCentralizer c.z).subtype =
    (((sourceR d).subgroupOf (involutionCentralizer c.z) ⊓ c.K).map
      (involutionCentralizer c.z).subtype).map (MulAut.conj c.s⁻¹).toMonoidHom
  generate : ((sourceR d).subgroupOf (involutionCentralizer c.z) ⊓ c.K) ⊔ E =
    (sourceR d).subgroupOf (involutionCentralizer c.z)
  disjoint : Disjoint ((sourceR d).subgroupOf (involutionCentralizer c.z) ⊓ c.K) E
  commute : ((sourceR d).subgroupOf (involutionCentralizer c.z) ⊓ c.K) ≤
    centralizer (E : Set (involutionCentralizer c.z))
  pure_fusion : ∀ a : involutionCentralizer c.z, IsConj c.z (a : G) →
    a ∈ (sourceR d).subgroupOf (involutionCentralizer c.z) → a ∈ c.K ∨ a ∈ E

/-- The terminal consumer uses both correlated source constructions. -/
theorem SourceComponentGeometry.false_of_source_factors
    {d : MinimalBlockSetup M} (c : SourceComponentGeometry d) (f : SourceFactorGeometry c) :
    False :=
  false_of_source_pair_geometry c.z c.involution c.nonidentity c.K c.componentEquiv
    ((sourceR d).subgroupOf (involutionCentralizer c.z)) f.E c.S₁ c.thompson_sylow
    f.centralizer_le f.centralizerEquiv c.u c.x c.σ c.swap c.transposition
    c.outside_natural c.natural_thompson f.P f.component_sylow c.s f.second_factor
    f.generate f.disjoint f.commute c.z₁ ⟨c.first_in_thompson, c.first_in_component⟩
    c.exchange f.pure_fusion

end CFSG.Quasithin.Chapter2.DoubleA3
