module

public import CFSG.Quasithin.ChapterB.Section01.SolvableStructure.Glauberman.BlockConstruction
public import CFSG.Quasithin.ChapterB.Section01.SolvableStructure.Glauberman.BlockConstruction.PairRecognition

/-!
# Applying pair recognition to the full factor support

The proved natural-pair construction discharges the 9.3.3 premise in the
literal factor `[O₂′(G),A]A` support assembly. The relative subnormality and
cubic support separation premises remain the separate source steps 9.3.4
and 9.3.5, owned by the full local-block assembly.

Source: Kurzweil–Stellmacher, *The Theory of Finite Groups*, 9.3.6,
printed p.245, PDF p.258 of `refs/original/kurzweil.pdf`.
-/

public section

open Subgroup Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterB.Glauberman.BlockConstruction
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V) [Finite G] [FiniteDimensional (ZMod 2) V]

/-- Pair recognition removes the pair-witness premise from support equality. -/
theorem factor_support_eq_pair_of_rank_one (hρ : Function.Injective ρ)
    {A : Subgroup G} (hA : IsMinimalBestOffender ρ A) (hrank : rank A = 1)
    (hsub : ∀ x ∈ pPrimeCore 2 G, x ∉ centralizer (A : Set G) →
      ((conjugatePair A x ⊓ pPrimeCore 2 G).subgroupOf (pPrimeCore 2 G)).IsSubnormal)
    (hsep : CubicSupportSeparation ρ (pPrimeCore 2 G))
    {x : G} (hx : x ∈ pPrimeCore 2 G) (hxc : x ∉ centralizer (A : Set G)) :
    subspaceCommutator ρ ⊤ (⁅pPrimeCore 2 G, A⁆ ⊔ A) =
      subspaceCommutator ρ ⊤ (conjugatePair A x) :=
  factor_support_eq_pair ρ hρ hA
    (fun _ hx hxc => pairData_nonempty ρ hρ hA hrank hx hxc) hsub hsep hx hxc

/-- Pair recognition removes the pair-witness premise from the plane dimension. -/
theorem factor_moved_finrank_of_rank_one (hsolv : Group.IsSolvable G)
    (hcore : pCore 2 G = ⊥) (hρ : Function.Injective ρ)
    {A : Subgroup G} (hA : IsMinimalBestOffender ρ A) (hrank : rank A = 1)
    (hsub : ∀ x ∈ pPrimeCore 2 G, x ∉ centralizer (A : Set G) →
      ((conjugatePair A x ⊓ pPrimeCore 2 G).subgroupOf (pPrimeCore 2 G)).IsSubnormal)
    (hsep : CubicSupportSeparation ρ (pPrimeCore 2 G)) :
    Module.finrank (ZMod 2) (subspaceCommutator ρ ⊤ (⁅pPrimeCore 2 G, A⁆ ⊔ A)) = 2 :=
  factor_moved_finrank ρ hsolv hcore hρ hA
    (fun _ hx hxc => pairData_nonempty ρ hρ hA hrank hx hxc) hsub hsep

end CFSG.Quasithin.ChapterB.Glauberman.BlockConstruction
