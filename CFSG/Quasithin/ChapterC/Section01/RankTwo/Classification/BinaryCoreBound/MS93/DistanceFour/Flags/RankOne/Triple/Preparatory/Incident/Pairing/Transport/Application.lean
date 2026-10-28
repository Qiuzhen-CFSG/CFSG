module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Flags.RankOne.Triple.Preparatory.Incident.Pairing.Transport.Quotient

/-!
# Assembly boundary for the incident application of MS93 (1.7)(i)

The finite marked quotient, normality, core containments and genuine central
natural factor are constructed in `Transport.Quotient`. This module assembles
them with the explicit remaining group and rank-one calculations, applies the
audited (1.7)(i), and translates its triple conclusion back to G_alpha.
The remaining premises below are proof obligations, not new source hypotheses;
this conditional application does not complete claim (3).

Source: Meierfrankenfeld--Stellmacher (1993), (1.7)(i), pp.847--848,
and (4.6.8), claim (3), p.906.
-/

public section
open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Flags.RankOne.Incident.Pairing.Transport.Quotient
open RankOnePairing
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}
variable (source : LocalSource L R) (geometry : Geometry R)
  (common : CommonFacts R source geometry) (i : Bool)
  (hkernel : flagKernel source i = Q R (beta R)) (d : M)
  (hd : flagIncident source i 1 d)
  (htriple : ⁅⁅V R (beta R), localFlagKernel source (!i) d⁆,
    localFlagResidual source (!i) d⁆ ≤ Z R (alpha R))

local notation "E" => extension source (representative source i d hd)
local notation "Z₀" => image (Z R (alpha R))
local notation "W₀" => image (V R (alpha R))
local notation "X₀" => seed source i d
local notation "C₀" => fixed source i d hd

/-- Assemble the genuine finite source data once the remaining local calculations
have been proved. The natural central factor and all basic source fields are constructed. -/
noncomputable def sourceData_of_bounds
    (hPhi : (frattini (generated X₀)).map (generated X₀).subtype ≤ Z₀)
    (hcomm : ⁅X₀, W₀⁆ ≤ Z₀)
    (hnontrivial : Nat.card (⁅X₀, W₀⁆ : Subgroup (Carrier R)) ≠ 1)
    (hcard : Nat.card (⁅X₀, W₀⁆ : Subgroup (Carrier R)) ≤ 4)
    (hfixed : ⁅X₀, localResidual (localParabolic E (!i))⁆ ≤ C₀)
    (n : RankOneFactor (localResidual (localParabolic E i))
      (localGenerated (localParabolic E i) X₀) C₀) :
    SourceData E (!i) Z₀ W₀ X₀ where
  z_le := Z_le_seed source i d
  x_le := seed_le_core source geometry common.large_distance i hkernel d hd
  w_le := radius_le_core source geometry common.large_distance _
  x_normal := seed_normal source geometry common.large_distance i hkernel d hd htriple
  natural := by
    let z := naturalZ source geometry common (representative source i d hd)
    exact {
      marking := z.marking
      coordinates := z.coordinates
      surjective := z.surjective
      kernel := z.kernel
      normalized := le_top.trans z.normalized
      action := fun l _ => z.action l (mem_top l) }
  frattini_le := hPhi
  commutator_le := hcomm
  commutator_nontrivial := hnontrivial
  commutator_card_le := hcard
  seed_fixed := hfixed
  rank_one_natural := by simpa only [Bool.not_not, extension_projection, extension_flag, fixed] using n

include common hkernel htriple in
/-- Apply the actual audited (1.7)(i) on the finite fixed-core quotient.
All additional local calculations remain explicit until the source assembly proves them. -/
theorem pairing_bound_of_bounds
    (hPhi : (frattini (generated X₀)).map (generated X₀).subtype ≤ Z₀)
    (hcomm : ⁅X₀, W₀⁆ ≤ Z₀)
    (hnontrivial : Nat.card (⁅X₀, W₀⁆ : Subgroup (Carrier R)) ≠ 1)
    (hcard : Nat.card (⁅X₀, W₀⁆ : Subgroup (Carrier R)) ≤ 4)
    (hfixed : ⁅X₀, localResidual (localParabolic E (!i))⁆ ≤ C₀)
    (n : RankOneFactor (localResidual (localParabolic E i))
      (localGenerated (localParabolic E i) X₀) C₀)
    (hz : Z₀ ⊓ centralizer (localResidual (localParabolic E (!i)) : Set (Carrier R)) ≠ ⊥) :
    ⁅Vcirc R (alpha R), Pairing.span source i d⁆ ≤ fixedCore R (alpha R) := by
  have s := sourceData_of_bounds source geometry common i hkernel d hd htriple
    hPhi hcomm hnontrivial hcard hfixed n
  exact pairing_bound_of_quotient source geometry common.large_distance i hkernel d hd
    (theorem_1_7_i s hz).2.1

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Flags.RankOne.Incident.Pairing.Transport.Quotient
