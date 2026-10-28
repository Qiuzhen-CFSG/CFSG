module

public import CFSG.Quasithin.ChapterB.Section01.SolvableStructure.Glauberman.BlockConstruction.SupportSeparation
public import CFSG.Quasithin.ChapterB.Section01.SolvableStructure.Glauberman.BlockConstruction

/-!
# Cubic support separation for actual conjugate pairs

The proved cubic separation theorem discharges the support-separation premise
in the conjugate-pair and full-factor support calculations. Pair construction
and relative subnormality remain explicit: their producers are the independent
9.3.3 and 9.3.4 steps. No existence of a local factor is asserted here.

Source: Kurzweil–Stellmacher, *The Theory of Finite Groups*, 9.3.5–9.3.6,
printed pp.243–245 (PDF pp.256–258 of `refs/original/kurzweil.pdf`).
-/

public section

open Subgroup Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterB.Glauberman.BlockConstruction
variable {G V : Type*} [Group G] [Finite G] [AddCommGroup V]
  [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V)

/-- Separation holds in the actual odd core of the original group. -/
theorem oddCore_cubic_support_separation (hρ : Function.Injective ρ) :
    CubicSupportSeparation ρ (pPrimeCore 2 G) :=
  cubic_support_separation ρ hρ _
    (Nat.coprime_two_left.mp (pPrimeCore_coprime_card (p := 2) (G := G)))

/-- The common offender line forces equality of the supports of actual pairs. -/
theorem pair_support_eq_of_cubic_subnormality (hρ : Function.Injective ρ)
    {A : Subgroup G} (hA : IsMinimalBestOffender ρ A) {x y : G}
    (dx : PairData ρ A x) (dy : PairData ρ A y)
    (hxsub : ((conjugatePair A x ⊓ pPrimeCore 2 G).subgroupOf
      (pPrimeCore 2 G)).IsSubnormal)
    (hysub : ((conjugatePair A y ⊓ pPrimeCore 2 G).subgroupOf
      (pPrimeCore 2 G)).IsSubnormal) :
    subspaceCommutator ρ ⊤ (conjugatePair A x) =
      subspaceCommutator ρ ⊤ (conjugatePair A y) :=
  pair_support_eq_of_separation ρ hρ hA dx dy hxsub hysub
    (oddCore_cubic_support_separation ρ hρ)

/-- The actual factor has plane support once its pair witnesses and their
relative cubic subnormality have been supplied. -/
theorem factor_moved_finrank_of_pairs_and_subnormality
    (hsolv : Group.IsSolvable G) (hcore : pCore 2 G = ⊥)
    (hρ : Function.Injective ρ) {A : Subgroup G} (hA : IsMinimalBestOffender ρ A)
    (hpairs : ∀ x ∈ pPrimeCore 2 G, x ∉ centralizer (A : Set G) →
      Nonempty (PairData ρ A x))
    (hsub : ∀ x ∈ pPrimeCore 2 G, x ∉ centralizer (A : Set G) →
      ((conjugatePair A x ⊓ pPrimeCore 2 G).subgroupOf (pPrimeCore 2 G)).IsSubnormal) :
    Module.finrank (ZMod 2) (subspaceCommutator ρ ⊤ (⁅pPrimeCore 2 G, A⁆ ⊔ A)) = 2 :=
  factor_moved_finrank ρ hsolv hcore hρ hA hpairs hsub
    (oddCore_cubic_support_separation ρ hρ)

end CFSG.Quasithin.ChapterB.Glauberman.BlockConstruction
