module
public import CFSG.Quasithin.Chapter2.Section04.LinearShadows.Single.DistinguishedTISource
public import CFSG.Quasithin.Chapter2.Section04.LinearShadows.Single.CenterFieldKernelSource
public import CFSG.Quasithin.Chapter2.Section04.LinearShadows.Single.WeakClosureSource

/-!
# The distinguished TI subgroup and its whole-subgroup weak closure

The original distinguished subgroup is Z(R) when L is centerless and Z(L)
otherwise. Its TI property follows from the two actual source branches.
The constructed centralizer identity C_S(Z)=R then gives that its whole
ambient conjugates contained in T generate exactly R. These wrappers
discharge every intermediate geometry premise in the literal source setup.

Source: Aschbacher–Smith, 2.4.18–19, printed p.534; using 2.4.16–17.
-/

public section
open Subgroup
namespace CFSG.Quasithin.Chapter2.LinearShadows.Single
variable {G : Type*} [Group G] [Finite G] {M : Subgroup G}

/-- Original 2.4.18(1): the distinguished subgroup is TI in the ambient group. -/
theorem source_distinguished_TI
    (d : MinimalBlockSetup M) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hST : (d.S : Subgroup d.H).map d.H.subtype < (T : Subgroup G))
    (hsingle : d.L0 = d.block) {n : ℕ} (hL : ChapterC.IsL2EvenBlock d.block n)
    (hM : IsMaximalTwoLocal M) (hTM : (T : Subgroup G) ≤ M)
    (hunique : ∀ K : Subgroup G, IsMaximalTwoLocal K → (T : Subgroup G) ≤ K → K = M) :
    ChapterI.Section06To08.IsTISubgroup (distinguishedZ d) := by
  by_cases hz : center (d.block.map d.H.subtype) = ⊥
  · exact (source_centerless_distinguished_TI d hG T hST hsingle hL hM hTM hunique hz
      (source_distinguished_sylow_centralizer_eq d hG T hST hsingle hL hM hTM hunique)).1
  · exact (source_distinguished_TI_of_center_ne_bot d hG T hST hsingle hL hM hTM hunique hz).1

/-- Original 2.4.18(2): in the centerless branch its normalizer is the unique maximal two-local. -/
theorem source_distinguished_normalizer_eq
    (d : MinimalBlockSetup M) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hST : (d.S : Subgroup d.H).map d.H.subtype < (T : Subgroup G))
    (hsingle : d.L0 = d.block) {n : ℕ} (hL : ChapterC.IsL2EvenBlock d.block n)
    (hM : IsMaximalTwoLocal M) (hTM : (T : Subgroup G) ≤ M)
    (hunique : ∀ K : Subgroup G, IsMaximalTwoLocal K → (T : Subgroup G) ≤ K → K = M)
    (hz : center (d.block.map d.H.subtype) = ⊥) :
    normalizer (distinguishedZ d : Set G) = M := by
  exact (source_centerless_distinguished_TI d hG T hST hsingle hL hM hTM hunique hz
    (source_distinguished_sylow_centralizer_eq d hG T hST hsingle hL hM hTM hunique)).2

/-- Original 2.4.19 with all preceding source inputs discharged. -/
theorem source_distinguished_weak_closure_eq
    (d : MinimalBlockSetup M) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hST : (d.S : Subgroup d.H).map d.H.subtype < (T : Subgroup G))
    (hsingle : d.L0 = d.block) {n : ℕ} (hL : ChapterC.IsL2EvenBlock d.block n)
    (hM : IsMaximalTwoLocal M) (hTM : (T : Subgroup G) ≤ M)
    (hunique : ∀ K : Subgroup G, IsMaximalTwoLocal K → (T : Subgroup G) ≤ K → K = M) :
    conjugateSubgroupClosure (distinguishedZ d) (T : Subgroup G) =
      Stellmacher.elementaryAbelianMaxJ ((d.S : Subgroup d.H).map d.H.subtype) := by
  exact source_distinguished_weak_closure d hG T hST hsingle hL hM hTM hunique
    (source_distinguished_TI d hG T hST hsingle hL hM hTM hunique)
    (source_distinguished_sylow_centralizer_eq d hG T hST hsingle hL hM hTM hunique)

/-- Each whole conjugate of the distinguished subgroup contained in T lies in R. -/
theorem source_distinguished_conjugate_le
    (d : MinimalBlockSetup M) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hST : (d.S : Subgroup d.H).map d.H.subtype < (T : Subgroup G))
    (hsingle : d.L0 = d.block) {n : ℕ} (hL : ChapterC.IsL2EvenBlock d.block n)
    (hM : IsMaximalTwoLocal M) (hTM : (T : Subgroup G) ≤ M)
    (hunique : ∀ K : Subgroup G, IsMaximalTwoLocal K → (T : Subgroup G) ≤ K → K = M)
    (g : G) (hg : (distinguishedZ d).map (MulAut.conj g).toMonoidHom ≤ (T : Subgroup G)) :
    (distinguishedZ d).map (MulAut.conj g).toMonoidHom ≤
      Stellmacher.elementaryAbelianMaxJ ((d.S : Subgroup d.H).map d.H.subtype) := by
  exact (map_conj_le_conjugateSubgroupClosure _ g hg).trans_eq
    (source_distinguished_weak_closure_eq d hG T hST hsingle hL hM hTM hunique)
end CFSG.Quasithin.Chapter2.LinearShadows.Single
