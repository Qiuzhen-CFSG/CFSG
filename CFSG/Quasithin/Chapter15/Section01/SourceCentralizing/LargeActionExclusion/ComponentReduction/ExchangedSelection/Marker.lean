module
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.Ordinary.FullSelection
public import CFSG.Quasithin.Chapter15.Section01.CaseI.MarkedNineControl

/-!
# Markers before the exclusions in original 15.1.23--24

The local action calculations in 15.1.16 provide a nonzero subgroup of
the Thompson fixed space, a Sylow centralizer, and a prime-order residual
in its faithful quotient. These are inputs to component construction;
they contain neither a component nor a model classification.

`PreExclusionSource` records the resulting 15.1.18--20 data, retaining
the prime and the original residual maps. In particular it is available
before excluding the decomposable prime five or the extraspecial row.
There is no assertion here that those source markers have been constructed.

Source: Aschbacher--Smith 15.1.16--20, printed pp.1092--1094.
-/

@[expose] public section
open Subgroup Representation Representation.BinaryOffender Stellmacher Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section01
open Section03
variable {G : Type*} [Group G] [Finite G]

/-- The finite action inputs to the component argument, before any component
is selected. The prime is the order of the literal faithful two-residual. -/
structure CaseIPreExclusionMarker (T : Sylow 2 G) (M V : Subgroup G)
    (hn : M ≤ normalizer (V : Set G)) where
  row : CaseIRow
  Z1 : Subgroup G
  prime : ℕ
  prime_prime : prime.Prime
  marked_fixed : Z1 ≤ thompsonFixed T V
  marked_nontrivial : Z1 ≠ ⊥
  generates : M = (M ⊓ centralizer (Z1 : Set G)) ⊔ (T : Subgroup G)
  local_sylow : Chapter1.IsSylowIn 2
    ((T : Subgroup G) ⊓ centralizer (Z1 : Set G)) (M ⊓ centralizer (Z1 : Set G))
  sylow_normal : (((T : Subgroup G) ⊓ centralizer (Z1 : Set G)).subgroupOf
    (T : Subgroup G)).Normal
  residual_card : letI := caseI_module_centralizer_normal (Z1 := Z1) hn
    Nat.card (pResidual 2 ((M ⊓ centralizer (Z1 : Set G) : Subgroup G) ⧸
      (M ⊓ centralizer (V : Set G)).subgroupOf (M ⊓ centralizer (Z1 : Set G)))) = prime
  seed_bound : centralInvolutions T ⊓ V ≤ Z1 ⊔
    ⁅V,(pResidual 2 (M ⊓ centralizer (Z1 : Set G) : Subgroup G)).map
      (M ⊓ centralizer (Z1 : Set G)).subtype⁆

namespace CaseIPreExclusionMarker
variable {T : Sylow 2 G} {M V : Subgroup G} {hn : M ≤ normalizer (V : Set G)}

def residual (m : CaseIPreExclusionMarker T M V hn) : Subgroup G :=
  (pResidual 2 (M ⊓ centralizer (m.Z1 : Set G) : Subgroup G)).map
    (M ⊓ centralizer (m.Z1 : Set G)).subtype

def movingPlane (m : CaseIPreExclusionMarker T M V hn) : Subgroup G := ⁅V,m.residual⁆

def fixedPlane (m : CaseIPreExclusionMarker T M V hn) : Subgroup G :=
  V ⊓ centralizer (m.residual : Set G)

end CaseIPreExclusionMarker

namespace CaseIComponentData
variable {T : Sylow 2 G} {M Mc V : Subgroup G}

/-- Actual component information obtained before choosing the surviving row.
It deliberately has no plane-size, cubic-escape or model-exclusion field. -/
structure PreExclusionSource (d : CaseIComponentData T M Mc V)
    (hn : M ≤ normalizer (V : Set G)) (p : ℕ) : Prop where
  prime_prime : p.Prime
  residual_card : letI : ((M ⊓ centralizer (V : Set G)).subgroupOf (M ⊓ d.G1)).Normal :=
      caseI_module_centralizer_normal (Z1 := d.Z1) hn
    Nat.card (pResidual 2 ((M ⊓ d.G1 : Subgroup G) ⧸
      (M ⊓ centralizer (V : Set G)).subgroupOf (M ⊓ d.G1))) = p
  odd_core : pPrimeCore 2 d.G1 = ⊥
  quasisimple : IsQuasisimple (d.L ⧸ pCore 2 d.L)
  local_component : d.L ∈ Chapter1.L G d.S
  component_sylow : Chapter1.IsSylowIn 2 d.SL d.L
  centralizer_sylow : Chapter1.IsSylowIn 2 d.S d.G1
  outside_M : ¬ d.L ≤ M
  ordinary : IsComponent d.G1 (d.L.subgroupOf d.G1) → d.OrdinarySource
  sylow_normal : (d.S.subgroupOf (T : Subgroup G)).Normal
  residual_intersection :
    (pResidual 2 (M ⊓ Mc ⊓ d.G1 : Subgroup G)).map (M ⊓ Mc ⊓ d.G1).subtype =
      (pResidual 2 (M ⊓ centralizer (V : Set G) : Subgroup G)).map
        (M ⊓ centralizer (V : Set G)).subtype
  residual_normalizes :
    (pResidual 2 (M ⊓ d.G1 : Subgroup G)).map (M ⊓ d.G1).subtype ⊔
        ⁅V,(pResidual 2 (M ⊓ d.G1 : Subgroup G)).map (M ⊓ d.G1).subtype⁆ ≤
          normalizer (d.L : Set G)
  seed_bound : centralInvolutions T ⊓ V ≤ d.Z1 ⊔
    ⁅V,(pResidual 2 (M ⊓ d.G1 : Subgroup G)).map (M ⊓ d.G1).subtype⁆
  moving_noncentral :
    ⁅d.L,⁅V,(pResidual 2 (M ⊓ d.G1 : Subgroup G)).map (M ⊓ d.G1).subtype⁆⁆ ≠ ⊥
  core_nontrivial : d.Q1 ≠ ⊥
  characteristic_control : d.Q1.characteristicNormalizerClosure ≤ Mc
  core_normalizer : d.G1 ⊓ normalizer (d.Q1 : Set G) = d.MZ
  sylow_normalizes_MZ : (T : Subgroup G) ≤ normalizer (d.MZ : Set G)
  sylow_normalizes_Q1 : (T : Subgroup G) ≤ normalizer (d.Q1 : Set G)

end CaseIComponentData
end CFSG.Quasithin.Chapter15.Section01
