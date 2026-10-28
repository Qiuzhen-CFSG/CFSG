module
public import CFSG.Quasithin.Chapter2.Section04.LinearShadows.Single.CenterlessReductionSource
public import CFSG.Quasithin.Chapter2.Section04.LinearShadows.Single.FixedSylowKernelSource
/-!
# The original centerless single-linear branch

The actual fixed-Sylow field kernels discharge the final p.539 alignment
and counting inputs. The full original centerless source setup is therefore
impossible by the marked involution transfer argument.
-/
public section
open Subgroup
namespace CFSG.Quasithin.Chapter2.LinearShadows.Single
open Stellmacher
variable {G : Type*} [Group G] [Finite G] {M : Subgroup G}
theorem source_centerless_false
    (d : MinimalBlockSetup M) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hST : (d.S : Subgroup d.H).map d.H.subtype < (T : Subgroup G))
    (hsingle : d.L0 = d.block) {n : ℕ} (hL : ChapterC.IsL2EvenBlock d.block n)
    (hM : IsMaximalTwoLocal M) (hTM : (T : Subgroup G) ≤ M)
    (hu : ∀ K : Subgroup G, IsMaximalTwoLocal K → (T : Subgroup G) ≤ K → K = M)
    (c : CyclicTorusSetup d T n) (hZ : center (d.block.map d.H.subtype) = ⊥)
    (s : T) (hs : (s:G)∈(d.S : Subgroup d.H).map d.H.subtype ⊓ normalizer (c.hall:Set G))
    (hs2 : orderOf s=2) (hsR : (s:G)∉elementaryAbelianMaxJ ((d.S : Subgroup d.H).map d.H.subtype))
 : False := by
  have hk := source_centerless_fixed_plane_sylow_kernel d hG T hST hsingle hL hM hTM hu c hZ s hs hs2 hsR
  have hi := source_centerless_fixed_center_index d hG T hST hsingle hL hM hTM hu c hZ s hs hs2 hsR
  exact source_centerless_false_of_kernels d hG T hST hsingle hL hM hTM hu c hZ s hs hs2 hsR hk hi
end CFSG.Quasithin.Chapter2.LinearShadows.Single
