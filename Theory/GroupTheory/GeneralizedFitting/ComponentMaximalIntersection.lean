module
public import Theory.GroupTheory.GeneralizedFitting.ComponentOrbitKernel
public import Theory.GroupTheory.ComponentLocalOrbitCore
public import Theory.GroupTheory.CComponent.QuasisimpleFactors

/-!
# Local component cores under a maximal subgroup

Let L be an ordinary component and C a maximal proper subgroup. If the
p-core of L ∩ C does not centralize L, its normalizer inside L lies in C.
The C-orbit of the core is a p-group by component commutation, including
nontrivial covering centers. Its normalizer contains C. Were that
normalizer the whole group, the component calculus would make the orbit
centralize L, a contradiction. No ambient normality of L is assumed.

Source application: Aschbacher--Smith 15.2.24, printed p.1117,
refs/quasithin.pdf, the parabolic over the actual component Sylow.
-/

public section
open Subgroup Theory.GroupTheory
namespace Theory.GroupTheory
variable {G : Type*} [Group G] [Finite G]

/-- A noncentral local core forces its component normalizer into the maximal subgroup. -/
theorem IsComponent.normalizer_intersection_core_le
    {L C : Subgroup G} (hL : IsComponent G L) (hC : IsCoatom C)
    {p : ℕ} [Fact p.Prime]
    (hne : ¬ (L ⊓ C).pCoreIn p ≤ centralizer (L : Set G)) :
    L ⊓ normalizer ((L ⊓ C).pCoreIn p : Set G) ≤ C := by
  let D := L ⊓ C
  let Q := D.pCoreIn p
  let R := componentOrbit Q C
  have hinv : C ⊓ normalizer (L : Set G) ≤ normalizer (D : Set G) :=
    (le_inf inf_le_right (inf_le_left.trans C.le_normalizer)).trans
      inf_normalizer_le_normalizer_inf
  have hinvQ : C ⊓ normalizer (L : Set G) ≤ normalizer (Q : Set G) :=
    hinv.trans (normalizer_le_normalizer_characteristic_image D (pCore p D))
  have hRp : IsPGroup p R := (hL.local_core_orbit (p := p) inf_le_left hinv).1
  have hCN : C ≤ normalizer (R : Set G) := le_normalizer_componentOrbit Q C
  have hN : normalizer (R : Set G) ≠ ⊤ := by
    intro htop
    let : R.Normal := normalizer_eq_top_iff.mp htop
    rcases hL.normal_dichotomy R with hLR | hc
    · let : Group.IsNilpotent R := hRp.isNilpotent
      exact hL.isCComponent.not_isSolvable
        (Group.isSolvable_of_isSolvable_injective (f := inclusion hLR)
          (inclusion_injective hLR))
    · apply hne
      exact (le_componentOrbit Q C).trans
        (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hc))
  have he : normalizer (R : Set G) = C := (hC.le_iff_eq hN).mp hCN
  exact (hL.normalizes_local_kernel_orbit inf_le_left
    ((pCoreIn_le p D).trans inf_le_left) inf_le_right hinvQ).trans he.le
end Theory.GroupTheory
