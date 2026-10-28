module
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Configuration
public import Theory.SpecificGroups.SymplecticFour.LocalFactors
public import Theory.SpecificGroups.SymplecticFour.RootSubgroup

/-!
# The marked symplectic survivor of original 4.3.6

This is a contract for the missing C.3.1/automorphism reduction, not a theorem
asserting that reduction. It marks the actual ordinary component, the original
L, its full source module, and the actual Sylow intersection in one matrix
carrier. In the source orientation the fixed root of L is short and the second
root is long. The root, its ambient normalizer, its residual inside K and its
normalizer-span module below use literal inclusions. The chosen Chapter 12
module does not occur in their definitions.

Source: Aschbacher--Smith 4.3.6, printed pp.614--615.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness
open Theory.SpecificGroups.SymplecticFour
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}

/-- The full module denoted V in the source proof, distinct from the chosen V. -/
noncomputable abbrev SourceConfiguration.ordinaryModule (_c : SourceConfiguration T L) :
    Subgroup G := Section02.Unitary.fullModule L ((L ⊔ (T : Subgroup G)).pCoreIn 2)

/-- Concrete simultaneous coordinates for the source symplectic survivor.
Existence must be proved from the ordinary source hypotheses. -/
structure OrdinarySymplecticMarking (c : SourceConfiguration T L) (n : ℕ) where
  Field : Type
  [field : _root_.Field Field]
  [finite : Finite Field]
  [charTwo : CharP Field 2]
  card : Nat.card Field = 2 ^ n
  componentEquiv : c.K ≃* Sp Field
  original_local : ((L.subgroupOf c.H).subgroupOf c.K).map
    componentEquiv.toMonoidHom = planeLocal
  sylow : ((((T : Subgroup G) ⊓ c.H).subgroupOf c.H).subgroupOf c.K).map
    componentEquiv.toMonoidHom = unipotent
  full_module : c.ordinaryModule = L.pCoreIn 2

attribute [instance] OrdinarySymplecticMarking.field OrdinarySymplecticMarking.finite
  OrdinarySymplecticMarking.charTwo

namespace OrdinarySymplecticMarking
variable {c : SourceConfiguration T L} {n : ℕ}

/-- The long root in the same actual ordinary component. -/
@[expose] noncomputable def rootInComponent (m : OrdinarySymplecticMarking c n) : Subgroup c.K :=
  (RootSubgroup.group (F := m.Field) 0).comap m.componentEquiv.toMonoidHom

/-- The source Z, embedded through K ≤ H ≤ G. -/
@[expose] noncomputable def root (m : OrdinarySymplecticMarking c n) : Subgroup G :=
  (m.rootInComponent.map c.K.subtype).map c.H.subtype

/-- The actual G_Z, without replacing it by a model normalizer. -/
@[expose] noncomputable def rootNormalizer (m : OrdinarySymplecticMarking c n) : Subgroup G :=
  normalizer (m.root : Set G)

/-- The actual K₂ = N_K(Z)^∞, using the embedded relative normalizer. -/
@[expose] noncomputable def second (m : OrdinarySymplecticMarking c n) : Subgroup G :=
  (solvableResidual (c.K.map c.H.subtype ⊓ m.rootNormalizer : Subgroup G)).map
    (c.K.map c.H.subtype ⊓ m.rootNormalizer).subtype

/-- The full normalizer two-core Q_Z. -/
@[expose] noncomputable def rootCore (m : OrdinarySymplecticMarking c n) : Subgroup G :=
  m.rootNormalizer.pCoreIn 2

/-- The source U = ⟨C_W(L)^{G_Z}⟩, retaining the entire source module W. -/
@[expose] noncomputable def rootSpan (m : OrdinarySymplecticMarking c n) : Subgroup G :=
  conjugateSpanBy (c.ordinaryModule ⊓ centralizer (L : Set G)) m.rootNormalizer

end OrdinarySymplecticMarking
end CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness
