module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Flags.RankOne.Consequences.Quotient
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Flags.RankOne.Triple.Natural.Quotient
public import Theory.GroupTheory.Commutator.NormalizedIndexTwo

/-!
# Residual commutators after identifying Bzero

Coprime commutator idempotence is imported from the natural-section
quotient calculation, which proves it in the finite marked parabolic
and transports it through its actual inclusion. Once Bzero equals B_alpha,
the definition of B_alpha places the residual commutator in Z_alpha.
The normalized quotient Z_alpha/Z_beta has order two, so idempotence
sharpens the bound to Z_beta. All normality is relative to the parabolic;
the ambient free amalgam is not assumed finite.

The equality Bzero = B_alpha remains an explicit input to the last two
bounds. Its displacement proof belongs to the source assembly.
Source: Meierfrankenfeld--Stellmacher (1993), (4.6.9), printed p.908.
-/

@[expose] public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
open scoped commutatorElement
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Flags.RankOne
variable {M : Type*} [Group M] {L R : Subgroup M}

/-- Once B₀ is the radius center, idempotence sharpens the first commutator to Z_alpha. -/
theorem flag_commutator_le_Z_of_Bzero [Finite M] (source : LocalSource L R)
    (geometry : Geometry R) (hlarge : 2 < geometry.b R) (early : EarlyFacts R geometry)
    (i : Bool) (hkernel : flagKernel source i = Q R (beta R))
    (htriple : ⁅⁅V R (beta R), flagResidual source i⁆, V R (alpha R)⁆ ≤
      (center (stabilizer R (alpha R))).map (stabilizer R (alpha R)).subtype)
    (hzero : Bzero geometry (alpha R) = B R (alpha R) (geometry.Z_normal (alpha R))) :
    ⁅V R (beta R), flagResidual source i⁆ ≤ Z R (alpha R) := by
  have he := flag_commutator_le_Bzero source geometry hlarge early i hkernel htriple
  rw [hzero] at he
  have hres : flagResidual source i ≤ Ltilde R (alpha R) := by
    rw [← flagResidual_sup source]
    cases i
    · exact le_sup_left
    · exact le_sup_right
  rw [← flag_commutator_idempotent source geometry hlarge i hkernel]
  exact (commutator_mono he hres).trans
    (B_commutator_le_Z geometry (alpha R) (geometry.V_local (alpha R) rfl hlarge))

/-- The actual omega-center of the edge kernel is preserved by its marked parabolic. -/
theorem flagParabolic_normalizes_edge_Z [Finite M] (source : LocalSource L R)
    (i : Bool) (hkernel : flagKernel source i = Q R (beta R)) :
    flagParabolic source i ≤ normalizer (Z R (beta R) : Set (FreeAmalgam R)) := by
  have hQ := flagKernel_normalized source i
  rw [hkernel] at hQ
  have hZ : Z R (beta R) = omegaCenter (Q R (beta R)) := by
    rw [Z, if_neg (show color R (beta R) ≠ false by change true ≠ false; decide)]
    rfl
  intro g hg
  rw [mem_normalizer_iff_map_conj_eq, hZ, ← omegaCenter_map _ _ (MulAut.conj g).injective]
  rw [mem_normalizer_iff_map_conj_eq.mp (hQ hg)]

/-- The index-two edge quotient gives the first displayed bound in source (4.6.9). -/
theorem flag_commutator_le_edge_Z_of_Bzero [Finite M] (source : LocalSource L R)
    (geometry : Geometry R) (hlarge : 2 < geometry.b R) (early : EarlyFacts R geometry)
    (i : Bool) (hkernel : flagKernel source i = Q R (beta R))
    (htriple : ⁅⁅V R (beta R), flagResidual source i⁆, V R (alpha R)⁆ ≤
      (center (stabilizer R (alpha R))).map (stabilizer R (alpha R)).subtype)
    (hzero : Bzero geometry (alpha R) = B R (alpha R) (geometry.Z_normal (alpha R))) :
    ⁅V R (beta R), flagResidual source i⁆ ≤ Z R (beta R) := by
  rw [← flag_commutator_idempotent source geometry hlarge i hkernel]
  apply (commutator_mono
    (flag_commutator_le_Z_of_Bzero source geometry hlarge early i hkernel htriple hzero)
    le_rfl).trans
  exact commutator_le_of_normalized_index_two _ _ _
    (edge_Z_le (alpha R) (beta R) rfl (base_adjacent R))
    (early.edge_Z_index (alpha R) (beta R) rfl (base_adjacent R))
    ((flagResidual_le source i).trans ((flagParabolic_le source i).trans
      (Z_normalized R (alpha R))))
    ((flagResidual_le source i).trans (flagParabolic_normalizes_edge_Z source i hkernel))
end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Flags.RankOne
