module

public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.EvenLocalCandidates.CentralInvolutionCore
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.EvenLocalCandidates.CentralNormalizerThreePart
import all Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.EvenLocalCandidates.CentralNormalizerThreePart
public import Mathlib.GroupTheory.Perm.Closure
public import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
# The symmetric quotient of the HS fixed-pair kernel

The ten pairs of fixed letters of `e0` form the Petersen graph. Its five
independent four-sets carry the action constructed in `CentralNormalizerThreePart`.
Here that action is labeled by `Fin 5`, and its kernel is identified with the
exact subgroup `CentralInvolutionCore.core` of `localGroup 0`.

Two explicit elements prove surjectivity. The existing word `s1` acts as `(0 1)`.
Writing `a,b` for the defining carrier generators and `g = b²ab`, the word
`g (e0 g⁻¹ e0 g)²` centralizes `e0` and acts as `(0 2 1 4 3)`. All these
identities are checked on the actual permutations by Lean's kernel. A five-cycle
and a transposition generate the symmetric group in prime degree. The first
isomorphism theorem then identifies the quotient, without any group-order,
kernel-order, splitting, or recognition premise.

The `import all` is an intentional internal proof split: it reuses the private
pair and star actions, their finite tables, and the kernel-containment proof
from `CentralNormalizerThreePart`. Those implementation details remain private;
clients use `fiveHom`, its kernel and surjectivity theorems, or `quotientEquiv`.
No existing module or public boundary is changed.

Source: GLS volume 3, Table 5.3m, printed p.274; Aschbacher–Smith 16.1.5(10),
printed p.1172. ATLAS attribution and permutation conventions are inherited
from the carrier. `PairQuotient/source/discover.py` records witness discovery;
its output is not an input to any proof.
-/

open Sporadic.LeechRelated.HS Sporadic.LeechRelated.HS.EvenLocalCandidates
open CentralInvolutionCore CentralNormalizerThreePart
namespace Sporadic.LeechRelated.HS.EvenLocalCandidates.CentralNormalizerThreePart.PairQuotient
set_option maxRecDepth 100000
set_option maxHeartbeats 800000
set_option Elab.async false

private theorem kernel_eq : starHom.ker = core := by
  ext g
  constructor
  · intro hg
    exact (mem_core_iff g).mpr (ker_fixed_pair ⟨g, hg⟩)
  · intro hg
    have hp : pairHom g = 1 := by
      apply Equiv.ext
      intro i
      change pairOf (g.val.val (rep i)) = i
      rcases (mem_core_iff g).mp hg (rep i) (rep_fixed i) with h | h
      · rw [h, pairOf_rep]
      · rw [h, pairOf_twin _ (rep_fixed i), pairOf_rep]
    apply MonoidHom.mem_ker.mpr
    apply Equiv.ext
    intro s
    apply Subtype.ext
    change s.val.image (pairHom g) = s.val
    simp [hp]

private def starLabel (k : Fin 5) : Star := ⟨stars k, stars_valid k⟩
private theorem starLabel_injective : Function.Injective starLabel := by
  have h : ∀ i j : Fin 5, stars i = stars j → i = j := by
    apply allFin
    decide +kernel
  intro i j hij
  exact h i j (congrArg Subtype.val hij)

private noncomputable def starEquiv : Fin 5 ≃ Star :=
  Equiv.ofBijective starLabel ((Fintype.bijective_iff_injective_and_card _).mpr
    ⟨starLabel_injective, by rw [card_star]; rfl⟩)

/-- The action on the five independent four-sets of the fixed-pair graph. -/
public noncomputable def fiveHom : localGroup 0 →* Equiv.Perm (Fin 5) :=
  (Equiv.permCongrHom starEquiv.symm).toMonoidHom.comp starHom

private theorem fiveHom_apply_iff (g : localGroup 0) (i j : Fin 5) :
    fiveHom g i = j ↔ (stars i).image (pairHom g) = stars j := by
  change starEquiv.symm (starHom g (starEquiv i)) = j ↔ _
  rw [Equiv.symm_apply_eq]
  exact Subtype.ext_iff

/-- The action kernel is exactly the subgroup fixing each fixed-letter pair. -/
public theorem fiveHom_kernel : fiveHom.ker = core := by
  rw [← kernel_eq]
  ext g
  change (Equiv.permCongrHom starEquiv.symm) (starHom g) = 1 ↔ starHom g = 1
  exact (Equiv.permCongrHom starEquiv.symm).map_eq_one_iff

private def letterA : Carrier := ⟨ab0, by
  rw [ab0_eq]
  exact Subgroup.subset_closure (by simp)⟩
private def letterB : Carrier := ⟨ab1, by
  rw [ab1_eq]
  exact Subgroup.subset_closure (by simp)⟩

private def seed : Carrier := letterB ^ 2 * letterA * letterB
private def liftCycle : Carrier := seed * (e0 * seed⁻¹ * e0 * seed) ^ 2

private theorem liftCycle_commutes : liftCycle * e0 = e0 * liftCycle := by
  apply Subtype.ext
  apply Equiv.ext
  apply allFin
  decide +kernel

private theorem s1_commutes : s1 * e0 = e0 * s1 := by
  apply Subtype.ext
  apply Equiv.ext
  apply allFin
  decide +kernel

private def inLocal (g : Carrier) (hg : g * e0 = e0 * g) : localGroup 0 :=
  ⟨g, by
    apply Subgroup.centralizer_le_normalizer
    rw [elementary_zero, Subgroup.centralizer_closure]
    exact Subgroup.mem_centralizer_singleton_iff.mpr hg⟩

private def cycleLocal : localGroup 0 := inLocal liftCycle liftCycle_commutes
private def swapLocal : localGroup 0 := inLocal s1 s1_commutes

private def fiveCycle : Equiv.Perm (Fin 5) :=
  Equiv.swap 0 2 * Equiv.swap 2 1 * Equiv.swap 1 4 * Equiv.swap 4 3

private theorem cycleLocal_image : fiveHom cycleLocal = fiveCycle := by
  apply Equiv.ext
  intro i
  apply (fiveHom_apply_iff _ _ _).mpr
  have h : ∀ i : Fin 5,
      (stars i).image (pairHom cycleLocal) = stars (fiveCycle i) := by
    apply allFin
    decide +kernel
  exact h i

private theorem swapLocal_image : fiveHom swapLocal = Equiv.swap 0 1 := by
  apply Equiv.ext
  intro i
  apply (fiveHom_apply_iff _ _ _).mpr
  have h : ∀ i : Fin 5,
      (stars i).image (pairHom swapLocal) = stars (Equiv.swap 0 1 i) := by
    apply allFin
    decide +kernel
  exact h i

private theorem fiveCycle_isCycle : fiveCycle.IsCycle := by
  refine ⟨0, by decide +kernel, ?_⟩
  intro y _
  have h : ∀ y : Fin 5, ∃ n : Fin 5, (fiveCycle ^ n.val) 0 = y := by
    apply allFin
    decide +kernel
  obtain ⟨n, hn⟩ := h y
  exact ⟨(n.val : ℤ), by simpa using hn⟩

/-- The explicit cycle and transposition witnesses give the full symmetric image. -/
public theorem fiveHom_surjective : Function.Surjective fiveHom := by
  apply MonoidHom.range_eq_top.mp
  apply top_unique
  have hgen := Equiv.Perm.closure_prime_cycle_swap
    (show (Fintype.card (Fin 5)).Prime by decide) fiveCycle_isCycle
    (show fiveCycle.support = Finset.univ by decide +kernel)
    (show (Equiv.swap (0 : Fin 5) 1).IsSwap from ⟨0, 1, by decide, rfl⟩)
  rw [← hgen, Subgroup.closure_le, Set.insert_subset_iff, Set.singleton_subset_iff]
  exact ⟨⟨cycleLocal, cycleLocal_image⟩, ⟨swapLocal, swapLocal_image⟩⟩

attribute [local instance] core_normal

/-- The full first local modulo its exact pair kernel is the symmetric group on five letters. -/
public noncomputable def quotientEquiv :
    (localGroup 0) ⧸ core ≃* Equiv.Perm (Fin 5) :=
  (QuotientGroup.quotientMulEquivOfEq fiveHom_kernel.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective fiveHom fiveHom_surjective)

end Sporadic.LeechRelated.HS.EvenLocalCandidates.CentralNormalizerThreePart.PairQuotient
