module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.LocalCommutator.CriticalCase.Selection.Inside.Recognition.Model.Star.Geometry
/-!
# Pointwise fixation in the index-two orbit-core case

For the escaping configuration of binary MS93 (1.6), assume that the seed has
index two over its actual common orbit core. The small escaping displacement
first fixes that core. The seed's stabilizer differences are consequently
central. The two escaping vectors in the normalized point geometry satisfy
the pair relation, and the cubic calculation forces every stabilizer element
to fix every seed vector in the original carrier.

The index-two condition is an explicit premise here; the independent orbit
clique argument and final displacement assembly discharge their own branches.
The final corollary applies Basic's displacement transfer to the literal right
conjugates. No splitting, constituent bound, or full-module displacement bound
is used to prove the fixation statement.

Source: Meierfrankenfeld–Stellmacher, *Pushing up weak BN-pairs of rank two*
(1993), (1.6), printed pp.845–847.
-/

@[expose] public section
open Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.LocalCommutator.CriticalCase.Inside.Recognition
open Escape.Initial.Natural.Splitting
set_option backward.isDefEq.respectTransparency false
variable {E : Type*} [Group E] [Finite E] [IsElementaryAbelian 2 E]

/-- In the index-two orbit-core case, the actual marked point stabilizer fixes
all seed vectors, including in a nonsplit central extension. -/
theorem seed_fixed_of_orbitCore_index_two (ρ : SL →* MulAut E)
    (_hfaithful : Function.Injective ρ) (d : EscapingConfiguration ρ)
    (hline : (actionOrbitCore ρ d.seed).relIndex d.seed = 2) :
    ∀ k ∈ markedPointStabilizer d.marking d.point, ∀ w ∈ d.seed, ρ k w = w := by
  obtain ⟨e,he⟩ := Star.exists_point_marking d.marking d.point d.point_ne_zero
  let σ := ρ.comp e.toMonoidHom
  intro k hk w hw
  have hcentral : ∀ l ∈ Matrix.PSL3Two.pointParabolicSL, ∀ g : SL,
      σ g (w⁻¹ * σ l w) = w⁻¹ * σ l w := by
    intro l hl g
    exact seed_difference_fixed ρ d hline w hw (e l) ((he l).mp hl) (e g)
  have hpair : σ Star.swap (σ Star.first w * σ Star.second w) =
      σ Star.first w * σ Star.second w := Star.pair_relation ρ d hline e he w hw
  have hf := Star.fixed_of_central_differences_of_pair_relation σ w hcentral hpair
  have hmem : e.symm k ∈ Matrix.PSL3Two.pointParabolicSL := (he _).mpr (by simpa using hk)
  simpa only [σ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    MulEquiv.apply_symm_apply] using hf (e.symm k) hmem

/-- Application to Basic's literal right-conjugate displacement transfer. -/
theorem displacement_transfer_of_orbitCore_index_two (ρ : SL →* MulAut E)
    (hfaithful : Function.Injective ρ) (d : EscapingConfiguration ρ)
    (hline : (actionOrbitCore ρ d.seed).relIndex d.seed = 2) :
    actionDisplacement ρ (zpowers d.involution) ⊤ ≤
      actionDisplacement ρ (zpowers d.involution)
        (actionEscapingSpan ρ (markedPointStabilizer d.marking d.point)
          d.involution d.seed) :=
  displacement_transfer_of_seed_fixed ρ d (seed_fixed_of_orbitCore_index_two ρ hfaithful d hline)

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.LocalCommutator.CriticalCase.Inside.Recognition
