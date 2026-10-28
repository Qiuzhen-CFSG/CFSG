module
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.OutsideFusion.Defs

/-!
# The orbit and residual steps for a fixed seed

The orbit assertion concerns square-one elements in the coset R t, with
R = O₂(I₂); it does not assert transitivity on the involutions of R⟨t⟩.
The residual assertion retains the literal centralizer inside I₂ and its
embedded O². These are successive steps of Aschbacher--Smith 14.3.21(2),
printed p.998, before the final transport into Q^y.
-/

@[expose] public section
open Subgroup
namespace CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction
open Chapter12.Section08 Chapter12.Section08.InvariantFlag
variable {G : Type*} [Group G] {T : Sylow 2 G} {V : Subgroup G}

/-- Transitivity on involutions in the outside coset for a seed-fixing t. -/
def FixedSeedCosetTransitivity (F : InvariantFlag T V 2) (L : Subgroup G) : Prop :=
  ∀ t ∈ (T : Subgroup G), orderOf t = 2 →
    t ∉ (F.I₂ L).pCoreIn 2 ⊔ F.H.pCoreIn 2 →
    t ∈ centralizer (V : Set G) →
    ∀ x : G, x ^ 2 = 1 → x * t⁻¹ ∈ (F.I₂ L).pCoreIn 2 →
      ∃ r ∈ (F.I₂ L).pCoreIn 2, r⁻¹ * x * r = t

/-- The natural action places the seed in the centralizer's two-residual. -/
def FixedSeedResidualGeneration (F : InvariantFlag T V 2) (L : Subgroup G) : Prop :=
  ∀ t ∈ (T : Subgroup G), orderOf t = 2 →
    t ∉ (F.I₂ L).pCoreIn 2 ⊔ F.H.pCoreIn 2 →
    t ∈ centralizer (V : Set G) →
    let C := F.I₂ L ⊓ centralizer ({t} : Set G)
    V ≤ (pResidual 2 C).map C.subtype

end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction
