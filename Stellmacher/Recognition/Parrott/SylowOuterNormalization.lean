module

public import Stellmacher.Recognition.Parrott.SylowOuterSeed
public import Stellmacher.Recognition.Parrott.SylowSeedOuterCentralization
public import Stellmacher.Recognition.Parrott.SylowSeedOuterCompletion

/-!+# Reduction of the remaining Sylow normalization to two outer calculations

The explicit a,c replacement establishes equation (16) on an arbitrary
unprimed seed. The remaining construction has two mathematical inputs:
centralization of b by the forced involution x²z, and completion of the
coordinate choices from that centralization. This assembly keeps those
inputs explicit; it does not assert either local calculation.

The local proofs can import `SylowOuterSeed`, without importing this assembly
module. Supplying both results then gives a full frame on the original
z,t,v,F,T. In particular, the centralization input concerns the seed's b,
not the unrelated fixed generator n.b of the normalizer data.

Source: Parrott (1972), §3, printed p.680, equations (16)–(19).
-/

namespace Stellmacher.Recognition.ParrottSylowSeedData
variable {G : Type*} [Group G] {z : G} {e : ParrottSecondElementaryData z}
variable {n : ParrottNormalizerFusionData e}

/-- The two remaining outer calculations, if established on every seed
satisfying (16), complete the Sylow frame for an arbitrary unprimed seed.
Both inputs must be discharged by the local construction. -/
public theorem exists_generators_of_outer_steps (f : ParrottSylowSeedData n false)
    (hcentralize : ∀ g : ParrottSylowSeedData n false,
      Tits.parrottCommutator g.a g.x = 1 → Commute g.b (g.x^2*z))
    (hcomplete : ∀ g : ParrottSylowSeedData n false,
      Tits.parrottCommutator g.a g.x = 1 → Commute g.b (g.x^2*z) →
        Nonempty (ParrottSylowGeneratorData n)) :
    Nonempty (ParrottSylowGeneratorData n) := by
  obtain ⟨g, hg⟩ := f.exists_ax_eq_one
  exact hcomplete g hg (hcentralize g hg)

/-- An unprimed Sylow seed extends to the full normalized Sylow frame.

The first outer normalization changes only the auxiliary `a,c` coordinates and
produces equation (16).  The centralization calculation then supplies the
hypothesis needed by the remaining coordinate changes, which complete
equations (17)--(19) while retaining the marked local data. -/
public theorem exists_generators_of_seed [Finite G] [IsSimpleGroup G]
    (f : ParrottSylowSeedData n false)
    (hns : ¬ Group.IsSolvable G) (hN : IsNTwoGroup G)
    (h : ParrottCentralizerHypotheses z) :
    Nonempty (ParrottSylowGeneratorData n) := by
  obtain ⟨g, hax⟩ := f.exists_ax_eq_one
  have hby := g.b_comm_square_mul_z hns hN h hax
  exact g.exists_generators_of_b_comm_square_mul_z hns hN h hax hby

end Stellmacher.Recognition.ParrottSylowSeedData
