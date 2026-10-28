module
public import CFSG.Quasithin.Chapter14.Section06.SourcePairedPointCentralizer
public import Theory.Representation.BinaryAlternatingFiveExtension.PointCoreGeometry.Transport
/-!
# Point-core centralizers and residual commutators in the original paired branch

The source point-centralizer marking identifies each literal B = Ki ∩ Mc
with the natural binary A₄ extension. Its two-core C and the ambient two-core
N of O²(B) therefore satisfy C_C(N) = Z(N), C_C(N/Z(N)) = N, and
[C,O²(B)] = N. The modulo assertion retains elementwise ambient commutators,
so it is available before normality of the eventual paired center in Mc.
No model equivalence or centralizer identity is an additional source premise.

Source: Aschbacher–Smith, proof of 14.6.9(i,l), printed p.1027.
-/
public section
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter14.Section06
open Subgroup Theory.GroupTheory Stellmacher
open ChapterC ChapterC.Section05.BlockAnalysis ChapterC.Section05.ConjugateSource
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]

theorem source_paired_block_point_core_geometry
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hunique : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hab : IsMulCommutative (conjugateSpanBy (localModule T M) Mc))
    (H : Subgroup G) (hH : H ∈ Chapter1.HOutside G (T : Set G) (M : Set G))
    (u : G) (hu : u ∈ conjugateSpanBy (localModule T M) H)
    (I : Subgroup G)
    (hI : I ∈ IMin (T : Subgroup G) (outsideOvergroups (Chapter1.H G)
      ((T : Subgroup G) ⊓ centralizer ({u} : Set G)) Mc M))
    (Λ : Subgroup G)
    (c : OriginalHypotheses I Λ ((pResidual 2 I).map I.subtype)
      ((T : Subgroup G) ⊓ I) ((T : Subgroup G) ⊓ I))
    (b : OrbitDecomposition (c.sylow : Subgroup I)
      (((T : Subgroup G) ⊓ I).subgroupOf I) (pResidual 2 I))
    (i j : Fin b.size) (hij : i ≠ j) (hs : b.size = 2)
    (hi : IsAlternatingBlock ((b.block i).map I.subtype) 5) :
    let B := (b.block i).map I.subtype ⊓ Mc
    let X := (pResidual 2 B).map B.subtype
    let N := X.pCoreIn 2
    let Z := (center N).map N.subtype
    B.pCoreIn 2 ⊓ centralizer (N : Set G) = Z ∧
      (∀ x ∈ B.pCoreIn 2, (∀ a ∈ N, ⁅a,x⁆ ∈ Z) → x ∈ N) ∧
      ⁅B.pCoreIn 2,X⁆ = N := by
  obtain ⟨eb⟩ := source_paired_block_borel hG T hempty hM hunique hmany hcard e hab
    H hH u hu I hI Λ c b i j hij hs hi
  exact BinaryPermutation.AlternatingFiveExtension.PointCoreGeometry.borel_ambient_geometry _ eb
end CFSG.Quasithin.Chapter14.Section06
