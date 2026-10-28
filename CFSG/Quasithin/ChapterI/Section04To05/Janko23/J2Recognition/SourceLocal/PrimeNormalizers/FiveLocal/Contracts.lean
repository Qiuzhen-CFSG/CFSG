module

public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.PrimeNormalizers.FiveLocal.Basic
public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.InvolutionGeometry.TrivialIntersection
public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.PrimeNormalizers.FiveTypes
public import Mathlib.GroupTheory.Complement

/-!
# Exact remaining branches of the five-local source calculation

These are output contracts for the three remaining parts of Aschbacher,
*Sporadic Groups* (1994), 47.2, printed p.261. None is an assumption of the
intended five-local theorem. Its earlier-source inputs are a `Seed`, the
order from 47.1, and `InvolutionGeometry.SelectedGeometry`.

The root-four branch retains the literal intrinsic layer of C_G(E), its
actual inclusion in the five-normalizer, generation by the selected seed
orbit, and its complement inside the centralizer of an inverting conjugate
of z. The other branch supplies the two-central normalizer, separation of
the classes, and the elementary abelian self-centralizing Sylow subgroup.
The final branch supplies the internal split extension and exhaustive fusion.

The product equivalences are marked on the actual component and dihedral
factors. In particular an unmarked group-family label cannot satisfy them.
-/

@[expose] public section

open Subgroup Theory.GroupTheory
open scoped Pointwise

namespace CFSG.Quasithin.Janko23.J2Recognition.SourceLocal.PrimeNormalizers.FiveLocal

variable {G : Type*} [Group G] [Finite G]

/-- The literal ambient image of E(C_G(E)). -/
def fiveComponent (E : Subgroup G) : Subgroup G :=
  (componentLayer (centralizer (E : Set G))).map (centralizer (E : Set G)).subtype

/-- The source notation ⟨Δ ∩ N_G(E)⟩, using the actual conjugates of D.X. -/
def orbitGenerated (D : Seed G) (E : Subgroup G) : Subgroup G :=
  sSup {A : Subgroup G | A ∈ MulAction.orbit (ConjAct G) D.X ∧
    A ≤ normalizer (E : Set G)}

/-- Full marked conclusion of 47.2(2) for one root-four five-subgroup. -/
structure RootFiveWitness (D : Seed G) (E : Subgroup G) where
  equiv : normalizer (E : Set G) ≃* (DihedralGroup 5 × alternatingGroup (Fin 5))
  component_factor :
    ((⊥ : Subgroup (DihedralGroup 5)).prod (⊤ : Subgroup (alternatingGroup (Fin 5)))).map
      ((normalizer (E : Set G)).subtype.comp equiv.symm.toMonoidHom) = fiveComponent E
  generation : fiveComponent E = orbitGenerated D E
  inverter : G
  inverter_conj : IsConj D.z inverter
  inverts : ∀ x ∈ E, inverter * x * inverter⁻¹ = x⁻¹
  dihedral_factor :
    ((⊤ : Subgroup (DihedralGroup 5)).prod (⊥ : Subgroup (alternatingGroup (Fin 5)))).map
      ((normalizer (E : Set G)).subtype.comp equiv.symm.toMonoidHom) =
      E ⊔ zpowers inverter
  component_le : fiveComponent E ≤ involutionCentralizer inverter
  complement : ((fiveComponent E).subgroupOf (involutionCentralizer inverter)).IsComplement'
    ((ambientCore inverter).subgroupOf (involutionCentralizer inverter))

/-- The root-four branch, still requiring its source proof. -/
def RootFiveFamily (D : Seed G) (t : G) : Prop :=
  ∀ E : Subgroup G, FiveCentralizing t E → Nonempty (RootFiveWitness D E)

/-- The two-central branch and the Sylow facts preceding the last paragraph of 47.2. -/
structure TwoCentralFiveFamily (D : Seed G) (t : G) : Prop where
  normalizer : ∀ E : Subgroup G, FiveCentralizing D.z E →
    Nonempty (normalizer (E : Set G) ≃* (DihedralGroup 5 × DihedralGroup 5))
  separated : ∀ E : Subgroup G, FiveCentralizing t E → ¬ FiveCentralizing D.z E
  elementary : ∀ P : Sylow 5 G, IsElementaryAbelian 5 P
  self_centralizing : ∀ P : Sylow 5 G, centralizer (P : Set G) = (P : Subgroup G)

/-- A genuine internal complement in the literal Sylow normalizer; D₁₂ has order twelve. -/
structure SylowSplitWitness (P : Sylow 5 G) where
  complement : Subgroup (normalizer (P : Set G))
  isComplement : complement.IsComplement'
    ((P : Subgroup G).subgroupOf (normalizer (P : Set G)))
  equiv : complement ≃* DihedralGroup 6

/-- The final action and fusion conclusions of 47.2(1),(4). -/
structure SylowFiveFamily (D : Seed G) (t : G) : Prop where
  split : ∀ P : Sylow 5 G, Nonempty (SylowSplitWitness P)
  coverage : ∀ E : Subgroup G, Nat.card E = 5 →
    FiveCentralizing t E ∨ FiveCentralizing D.z E

/-- Full source contract, rather than only the two unmarked normalizer types. -/
structure SourceConclusion (D : Seed G) (t : G) : Prop where
  root : RootFiveFamily D t
  twoCentral : TwoCentralFiveFamily D t
  sylow : SylowFiveFamily D t

end CFSG.Quasithin.Janko23.J2Recognition.SourceLocal.PrimeNormalizers.FiveLocal
