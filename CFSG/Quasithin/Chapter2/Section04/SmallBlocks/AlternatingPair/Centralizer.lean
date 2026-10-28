module
public import CFSG.Quasithin.Chapter2.Section04.SmallBlocks.AlternatingPair.Base
public import CFSG.Quasithin.ChapterC.Section05.ConjugateSource.AlternatingFixedPhiCentralizer
public import Theory.GroupTheory.PResidual.PrimeTo

/-!
# The original paired-block cubic residual centralizes Φ

The selected source blocks, original Sylow subgroup and original maximal
local subgroup instantiate the intrinsic fixed-Frattini calculation. The
second block is outside M, while its Sylow subgroup lies in M. Therefore
M∩L₀ centralizes the literal Φ; its prime-to-three residual does as well.

Source: Aschbacher–Smith, proof of 2.4.25, printed p.541.
-/

public section
open Subgroup
namespace CFSG.Quasithin.Chapter2
open ChapterC.Section05.ConjugateSource.AlternatingFixedPhi
variable {G : Type*} [Group G] [Finite G] {M M₀ : Subgroup G}
  {d : MinimalBlockSetup M}

/-- The original maximal-local intersection with L₀ centralizes the actual Φ. -/
theorem AlternatingPairSourceSetup.phi_intersection_centralized
    (c : AlternatingPairSourceSetup d M₀) :
    M ⊓ d.L0.map d.H.subtype ≤ centralizer
      (Phi ((d.S : Subgroup d.H).map d.H.subtype) (d.block.map d.H.subtype) : Set G) := by
  have h := intersection_centralizes_Phi c.marked₁ c.marked₂ M
    (inf_le_left.trans d.full_pair.1.1.2.1) c.second_not_le_M
  rwa [c.join] at h

/-- The literal O^{3′}(M∩L₀) assertion used in the source construction of G_I. -/
theorem AlternatingPairSourceSetup.phi_cubic_residual_centralized
    (c : AlternatingPairSourceSetup d M₀) :
    (primeToResidual 3 (M ⊓ d.L0.map d.H.subtype : Subgroup G)).map
        (M ⊓ d.L0.map d.H.subtype).subtype ≤ centralizer
      (Phi ((d.S : Subgroup d.H).map d.H.subtype) (d.block.map d.H.subtype) : Set G) :=
  (map_subtype_le _).trans c.phi_intersection_centralized

end CFSG.Quasithin.Chapter2
