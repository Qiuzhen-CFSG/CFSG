module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Flags.RankOne.Triple.Preparatory.Propagation.Pairing.Module.Section
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Flags.RankOne.Triple.Natural.GeometryBound.Displacement.Local

/-!
# The midpoint as an actual line in the split natural section

The edge index gives the seed index two modulo Z_alpha. The selected edge
kernel fixes it in that quotient, whereas the selected tilded residual moves
it: otherwise its commutator with V_alpha would vanish, contradicting the
chosen bad triple. These facts construct `SplitLineData` for the literal
subgroups in M and their original marked parabolics.

`SplitLineData` is an input interface for the remaining representation
calculation. It assumes neither an opposite-parabolic fixed line nor natural
two-space coordinates. Its construction does not prove `SeedModuleData`.

Source: Meierfrankenfeld--Stellmacher (1993), (4.6.8), claim (2), p.906,
using the edge indices from (4.6.3)--(4.6.7).
-/

@[expose] public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Flags.RankOne.Propagation.Pairing
open RankOnePairing
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}
  {source : LocalSource L R} {geometry : Geometry R} {i : Bool}

/-- Inputs for transporting one actual line in a split natural three-section.
The local core and ordered residual are literal subgroups of the same marked
parabolic. No orientation or transport conclusion is included. -/
structure SplitLineData {G : Type*} [Group G]
    (π : G →* SL) (flag : SL) (j : Bool) (H N X : Subgroup G) where
  surjective : Function.Surjective π
  kernel_two : IsPGroup 2 π.ker
  sectionData : Escape.SingleNaturalSection π π.ker (pResidual 2 G) H N
  seed_le_kernel : X ≤ π.ker
  denominator_le_seed : N ≤ X
  generation : generated X = H
  kernel_commutator : ⁅H, π.ker⁆ ≤ N
  line_index : N.relIndex X = 2
  core_fixed : ⁅X, localCore (parabolic π flag j)⁆ ≤ N
  residual_moves : ¬ ⁅X, rankOne (parabolic π flag j)⁆ ≤ N

omit [Finite M] in
/-- The identity seed is Z_alpha joined with the original midpoint. -/
theorem seed_one (p : FlagCriticalData source geometry i) :
    seed p 1 = centralLayer (R := R) ⊔ middleLayer p := by
  have he : (MulAut.conj (1 : M)).toMonoidHom = MonoidHom.id _ := by
    ext x
    simp
  rw [seed, he, map_id]

/-- The actual seed has a nonzero line as its image modulo Z_alpha. -/
theorem seed_line_index (common : CommonFacts R source geometry)
    (early : EarlyFacts R geometry) (p : FlagCriticalData source geometry i) :
    (centralLayer (R := R)).relIndex (seed p 1) = 2 := by
  rw [seed_one, relIndex_sup_left]
  exact middleLayer_index common early p

/-- The selected first parabolic core fixes the seed modulo Z_alpha. -/
theorem seed_core_fixed (common : CommonFacts R source geometry)
    (early : EarlyFacts R geometry) (p : FlagCriticalData source geometry i)
    (hkernel : flagKernel source i = Q R (beta R)) :
    ⁅seed p 1, localCore (parabolic source.projection source.flag i)⁆ ≤
      centralLayer (R := R) := by
  apply (map_le_map_iff_of_injective (embedM_injective R)).mp
  rw [map_commutator, map_seed common p 1, map_centralLayer, localConjugate_one]
  change ⁅Z R (alpha R) ⊔ Z R p.middle, flagKernel source i⁆ ≤ Z R (alpha R)
  have hh := localFlagKernel_centralizes_bar source geometry common early i hkernel 1
  simp only [localFlagKernel, localConjugate_one] at hh
  exact (commutator_mono
    (sup_le (Z_le_firstFlagLayer 1) p.middle_le_firstLayer) le_rfl).trans hh

omit [Finite M] in
/-- The bad triple excludes fixation by the selected tilded residual. -/
theorem seed_residual_moves (common : CommonFacts R source geometry)
    (p : FlagCriticalData source geometry i) :
    ¬ ⁅seed p 1, rankOne (parabolic source.projection source.flag i)⁆ ≤
      centralLayer (R := R) := by
  intro h
  have hh := map_mono (f := embedM R) h
  rw [map_commutator, map_seed common p 1, map_centralLayer, localConjugate_one] at hh
  change ⁅Z R (alpha R) ⊔ Z R p.middle, flagResidual source i⁆ ≤ Z R (alpha R) at hh
  have hz := (commutator_mono (le_sup_right : Z R p.middle ≤
    Z R (alpha R) ⊔ Z R p.middle) le_rfl).trans hh
  apply p.middle_triple
  exact ((commutator_mono hz (V_le_Q geometry common.large_distance _ rfl)).trans_eq
    (geometry.centralizes _ rfl)).trans bot_le

/-- Construct all geometric inputs for the split-three-space line transport.
No flag natural-section producer or later flag-control result is used. -/
noncomputable def splitLineData (common : CommonFacts R source geometry)
    (early : EarlyFacts R geometry) (p : FlagCriticalData source geometry i)
    (hkernel : flagKernel source i = Q R (beta R))
    (hseed : ⁅Z R p.middle, Q R (alpha R)⁆ ≤ U R (alpha R))
    (hs : SingleSection p) :
    SplitLineData source.projection source.flag i (spanLayer p)
      (centralLayer (R := R)) (seed p 1) where
  surjective := source.projection_surjective
  kernel_two := by rw [source.projection_kernel]; exact pCore_isPGroup
  sectionData := Classical.choice hs
  seed_le_kernel := (seed_le_core common p 1).trans (extensionCore_le_kernel _)
  denominator_le_seed := le_sup_left
  generation := generated_seed common p 1
  kernel_commutator := (spanLayer_kernel_commutator common p hseed).trans
    (comap_mono (U_le_Z _))
  line_index := seed_line_index common early p
  core_fixed := seed_core_fixed common early p hkernel
  residual_moves := seed_residual_moves common p

omit [Finite M] in
/-- Conjugating the identity seed gives the prescribed seed, with the central
layer unchanged by its proved ambient normality. -/
theorem seed_conjugate (p : FlagCriticalData source geometry i) (g : M) :
    (seed p 1).map (MulAut.conj g).toMonoidHom = seed p g := by
  have hc : (centralLayer (R := R)).map (MulAut.conj g).toMonoidHom =
      centralLayer (R := R) := Normal.map_conj_eq _ g
  rw [seed_one, Subgroup.map_sup, hc]
  rfl

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Flags.RankOne.Propagation.Pairing
