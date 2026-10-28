module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Flags.RankOne.Triple.Natural.Quotient
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Flags.RankOne.Triple.Preparatory.Critical
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Flags.RankOne.Triple.Preparatory.Layers
/-!
# The actual incidence route to the p.905 fixed-quotient bound

The suggested intersection with `Q_alpha` is all of `V_beta`, and the bad
triple hypothesis rules out its containment in the fixed preimage. The source
instead compares conjugate first-color layers with the kernel at a critical
midpoint. Conjugation preserves their residual fixed-quotient indices; all
these layers are attached to actual parabolic cosets even before naturality.

`FlagP905Displacement` states the two strict displacement inequalities in
the proof of claim (1). It is a proof target, with no constructor here. The
source's incidence and symmetry argument must next make the midpoint edge
commutator central. We prove that this contradicts the chosen bad midpoint
and give the conditional index assembly. Neither of these geometric steps
is assumed to be a source theorem or asserted as proved in this module.

Source: Meierfrankenfeld--Stellmacher, *Pushing up weak BN-pairs of rank two*
(1993), proof of (4.6.8), claim (1), printed p.905.
-/

@[expose] public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Flags.RankOne
variable {M : Type*} [Group M] {L R : Subgroup M}

/-- The first edge layer already lies in the original M-kernel. -/
theorem edgeRadius_le_Q_alpha (geometry : Geometry R)
    (hlarge : 2 < geometry.b R) : V R (beta R) ≤ Q R (alpha R) :=
  (edgeRadius_le_radius (alpha R) (beta R) rfl (base_adjacent R)).trans
    (V_le_Q geometry hlarge (alpha R) rfl)

/-- Intersecting with the original M-kernel does not cut down the edge layer. -/
theorem edgeRadius_inf_Q_alpha_eq (geometry : Geometry R)
    (hlarge : 2 < geometry.b R) : V R (beta R) ⊓ Q R (alpha R) = V R (beta R) :=
  inf_eq_left.mpr (edgeRadius_le_Q_alpha geometry hlarge)

/-- The originally proposed fixed-intersection route contradicts the bad triple.
The source uses displacement against the midpoint kernel instead. -/
theorem edgeRadius_inf_Q_alpha_not_le_flagFixedPreimage (source : LocalSource L R)
    (geometry : Geometry R) (hlarge : 2 < geometry.b R) (i : Bool)
    (hbad : ¬ ⁅⁅V R (beta R), flagResidual source i⁆, V R (alpha R)⁆ ≤
      (center (stabilizer R (alpha R))).map (stabilizer R (alpha R)).subtype) :
    ¬ V R (beta R) ⊓ Q R (alpha R) ≤ flagFixedPreimage source i := by
  rw [edgeRadius_inf_Q_alpha_eq geometry hlarge]
  intro h
  exact flagFixedPreimage_ne_edgeRadius source geometry hlarge i hbad
    (le_antisymm (flagFixedPreimage_bounds source i).2 h)

private theorem map_commutatorPreimage_le {G : Type*} [Group G]
    (A K N : Subgroup G) (f : G →* G) (hAN : A ≤ normalizer N) :
    (commutatorPreimage A K N).map f ≤
      commutatorPreimage (A.map f) (K.map f) (N.map f) := by
  apply le_commutatorPreimage (map_mono (commutatorPreimage_le A K N))
  rw [← map_commutator]
  exact map_mono (commutator_commutatorPreimage_le A K N hAN)

private theorem localConjugate_Z (g : M) :
    localConjugate (Z R (alpha R)) g = Z R (alpha R) := by
  apply mem_normalizer_iff_map_conj_eq.mp
  apply Z_normalized R (alpha R)
  rw [alpha, stabilizer_m_base]
  exact ⟨g, rfl⟩

/-- The fixed preimage at a first-color coset is the conjugate of the original
fixed preimage. All actions and denominators are the literal source ones. -/
theorem localFlagFixedPreimage_eq_conjugate (source : LocalSource L R)
    (geometry : Geometry R) (hlarge : 2 < geometry.b R) (i : Bool) (g : M) :
    commutatorPreimage (firstFlagLayer (R := R) g)
      (localFlagResidual source i g) (Z R (alpha R)) =
        localConjugate (flagFixedPreimage source i) g := by
  have hz : localConjugate (Z R (alpha R)) g = Z R (alpha R) := localConjugate_Z g
  have hforward := map_commutatorPreimage_le (V R (beta R)) (flagResidual source i)
    (Z R (alpha R)) (MulAut.conj (embedM R g)).toMonoidHom
    ((edgeRadius_le_stabilizer geometry hlarge).trans (Z_normalized R _))
  change localConjugate (flagFixedPreimage source i) g ≤
    commutatorPreimage (firstFlagLayer (R := R) g) (localFlagResidual source i g)
      (localConjugate (Z R (alpha R)) g) at hforward
  rw [hz] at hforward
  refine le_antisymm ?_ hforward
  let C := commutatorPreimage (firstFlagLayer (R := R) g)
    (localFlagResidual source i g) (Z R (alpha R))
  have hback := map_commutatorPreimage_le (firstFlagLayer (R := R) g)
    (localFlagResidual source i g) (Z R (alpha R))
    (MulAut.conj (embedM R g⁻¹)).toMonoidHom
    ((firstFlagLayer_le_radius g).trans
      ((geometry.V_local _ rfl hlarge).trans (Z_normalized R _)))
  change localConjugate C g⁻¹ ≤ commutatorPreimage
    (localConjugate (localConjugate (V R (beta R)) g) g⁻¹)
    (localConjugate (localConjugate (flagResidual source i) g) g⁻¹)
    (localConjugate (Z R (alpha R)) g⁻¹) at hback
  rw [← localConjugate_mul, ← localConjugate_mul, inv_mul_cancel,
    localConjugate_one, localConjugate_one, localConjugate_Z] at hback
  have hm := map_mono (f := (MulAut.conj (embedM R g)).toMonoidHom) hback
  change localConjugate (localConjugate C g⁻¹) g ≤
    localConjugate (flagFixedPreimage source i) g at hm
  rw [← localConjugate_mul, mul_inv_cancel, localConjugate_one] at hm
  exact hm

/-- The residual fixed quotient has the same size at every first-color coset. -/
theorem localFlagFixedPreimage_relIndex (source : LocalSource L R)
    (geometry : Geometry R) (hlarge : 2 < geometry.b R) (i : Bool) (g : M) :
    (commutatorPreimage (firstFlagLayer (R := R) g)
      (localFlagResidual source i g) (Z R (alpha R))).relIndex
        (firstFlagLayer (R := R) g) =
          (flagFixedPreimage source i).relIndex (V R (beta R)) := by
  rw [localFlagFixedPreimage_eq_conjugate source geometry hlarge i g]
  exact relIndex_map_map_of_injective _ _ (MulAut.conj (embedM R g)).injective

/-- Representative independence needs only the genuine kernel identification,
without assuming that the fixed quotient is already a natural factor. -/
theorem firstFlagLayer_right_mul_of_kernel [Finite M] (source : LocalSource L R)
    (geometry : Geometry R) (hlarge : 2 < geometry.b R) (i : Bool)
    (hkernel : flagKernel source i = Q R (beta R))
    (g p : M) (hp : p ∈ parabolic source.projection source.flag i) :
    firstFlagLayer (R := R) (g * p) = firstFlagLayer (R := R) g :=
  localConjugate_right_mul _ _
    (flagParabolic_normalizes_edgeRadius source geometry hlarge i hkernel) g p hp

variable [Finite M]

/-- Centrality of the midpoint edge commutator would force the selected triple
to be central, because the local residual normalizes the radius group. -/
theorem FlagCriticalData.middle_edge_commutator_not_le_center
    {source : LocalSource L R} {geometry : Geometry R} {i : Bool}
    (p : FlagCriticalData source geometry i)
    (common : CommonFacts R source geometry) :
    ¬ ⁅Z R p.middle, Q R (beta R)⁆ ≤
      (center (stabilizer R (alpha R))).map (stabilizer R (alpha R)).subtype := by
  intro hc
  apply p.middle_triple
  let A := stabilizer R (alpha R)
  let N := (center A).map A.subtype
  let D := commutatorPreimage A (V R (alpha R)) N
  have hN : A ≤ normalizer N := A.le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image _ _)
  have hD : A ≤ normalizer D := commutatorPreimage_normalized _ _ _ _ hN
    A.le_normalizer (DistanceEight.V_normalized R _) hN
  have hZ : Z R p.middle ≤ A := by
    have h := p.middle_le_firstLayer
    rw [firstFlagLayer, localConjugate_one] at h
    exact h.trans (edgeRadius_le_stabilizer geometry common.large_distance)
  have hV : V R (alpha R) ≤ Q R (beta R) :=
    (V_le_Q geometry common.large_distance _ rfl).trans
      (Q_le_adjacent_h R (show color R (beta R) = true from rfl) (base_adjacent R))
  have hZD : Z R p.middle ≤ D :=
    le_commutatorPreimage hZ ((commutator_mono le_rfl hV).trans hc)
  have hKD : flagResidual source i ≤ normalizer D :=
    ((flagResidual_le source i).trans (flagParabolic_le source i)).trans hD
  exact (commutator_mono
    ((commutator_mono hZD le_rfl).trans
      (le_normalizer_iff_commutator_le_left.mp hKD)) le_rfl).trans
        (commutator_commutatorPreimage_le A (V R (alpha R)) N hN)

/-- The two displacement inequalities on p.905, before the final incidence
and symmetry argument. This definition specifies an intermediate target;
it does not supply either inequality from the source hypotheses. -/
def FlagP905Displacement (source : LocalSource L R) (geometry : Geometry R)
    (i : Bool) : Prop :=
  ∀ p : FlagCriticalData source geometry i,
    2 < (Q R (alpha R)).relIndex (V R p.middle) ∧
      ∀ d : M, flagIncident source i 1 d →
        ¬ Z R p.endpoint ⊓ localFlagKernel source (!i) d ≤ Q R (alpha R) →
        ∀ g : M, flagIncident source i g d →
          localFlagZ source i g ≠ localFlagZ source i 1 →
          2 < (Q R p.middle).relIndex (firstFlagLayer (R := R) g)

/-- Conditional assembly along the genuine p.905 route. The displacement
producer and the subsequent incidence/symmetry implication are separate,
unproved premises here; the source assembly must discharge both. -/
theorem flagFixedPreimage_relIndex_le_four_of_displacement_and_symmetry
    (source : LocalSource L R) (geometry : Geometry R)
    (common : CommonFacts R source geometry) (hb : geometry.b R = 4) (i : Bool)
    (hbad : ¬ ⁅⁅V R (beta R), flagResidual source i⁆, V R (alpha R)⁆ ≤
      (center (stabilizer R (alpha R))).map (stabilizer R (alpha R)).subtype)
    (hdisplacement : 4 < (flagFixedPreimage source i).relIndex (V R (beta R)) →
      FlagP905Displacement source geometry i)
    (hsymmetry : FlagP905Displacement source geometry i →
      ∀ p : FlagCriticalData source geometry i,
        ⁅Z R p.middle, Q R (beta R)⁆ ≤
          (center (stabilizer R (alpha R))).map (stabilizer R (alpha R)).subtype) :
    (flagFixedPreimage source i).relIndex (V R (beta R)) ≤ 4 := by
  by_contra h
  obtain ⟨p⟩ := flagCriticalData source geometry common hb i hbad
  exact p.middle_edge_commutator_not_le_center common
    (hsymmetry (hdisplacement (Nat.lt_of_not_ge h)) p)

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Flags.RankOne
