module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.PairingControl.FirstPairing.StepThree.Coordinates
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.PairingControl.FirstPairing.StepThree.Consequences
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.PairingControl.FirstPairing.StepThree.RankOne
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.PairingControl.FirstPairing.StepThree.Kernel

/-!
# Assembly of the local deductions in MS93 (4.3.2)(3)

The rank-one argument identifies [Z_delta,Q_alpha] with the alpha-side
edge displacement. Transported InitialFacts already identify the same
commutator with the delta-side displacement. Their equality yields moving
symmetry and H = U at every M-vertex.

The intrinsic-kernel argument bounds Vcirc intersect Z[V,Q]
by U. The coordinate restriction then constructs the actual dual Vcirc/U
under the original marking on U. It uses both surjectivity and the exact
kernel, so no abstract order or constituent count replaces the quotient.

`step_three_of_alpha_and_kernel` retains the conditional assembly interface.
`step_three` supplies both proved producers and establishes step (3) from
the actual opposite moving orientation supplied by step (2). The kernel
producer uses H = U, which the assembly proves from the rank-one identification.
The earlier module, normalization and initial facts remain explicit inputs.

Source: Meierfrankenfeld--Stellmacher (1993), (4.3.2)(3), printed p.884.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.PairingControl.FirstPairing
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M} {geometry : Geometry R}

theorem step_three_of_alpha_and_kernel (source : LocalSource L R)
    (hb : 2 < geometry.b R) (modules : ModuleFacts source geometry)
    (transfer : NormalizationTransfer R)
    (initial : ∀ q : Counterexample geometry, Nonempty (InitialFacts q))
    (orientations : ∀ a, color R a = false → Nonempty (MovingOrientationAt a))
    (p : Counterexample geometry) (bad : ¬ ⁅V R p.a, Q R p.a⁆ ≤ fixedCore R p.a)
    (identify : ∀ q : Counterexample geometry,
      ¬ ⁅V R q.a, Q R q.a⁆ ≤ fixedCore R q.a →
      ∀ t d, Adjacent R q.a t → Adjacent R d t → d ∈ movingNeighbors geometry q.a →
        ⁅Z R d, Q R q.a⁆ = edgeDisplacement q.a t)
    (kernel : (∀ a, color R a = false → H R a = U R a) →
      (Vcirc R p.a).subgroupOf (stabilizer R p.a) ⊓
        radicalPreimage ((Q R p.a).subgroupOf (stabilizer R p.a))
          ((V R p.a).subgroupOf (stabilizer R p.a))
          ((Z R p.a).subgroupOf (stabilizer R p.a)) ≤
        (U R p.a).subgroupOf (stabilizer R p.a)) : StepThreeAt geometry p.a := by
  have hH : ∀ a, color R a = false → H R a = U R a := by
    intro a ha
    obtain ⟨q, hqa, hbad⟩ := contrary_at p bad a ha
    obtain ⟨hq⟩ := initial q
    obtain ⟨o⟩ := orientations q.a q.color_a
    exact hqa ▸ StepThree.H_eq_U_of_alpha_commutators source hb modules transfer q hq
      hbad o (identify q hbad)
  have hedge : ∀ t d, Adjacent R p.a t → Adjacent R d t →
      d ∈ movingNeighbors geometry p.a → edgeDisplacement d t = edgeDisplacement p.a t := by
    intro t d hat hdt hd
    exact (StepThree.moving_commutator_eq_edge_at p (by omega) initial bad
      p.a t d p.color_a hat hdt hd).symm.trans (identify p bad t d hat hdt hd)
  refine ⟨?_, hedge, ?_⟩
  · obtain ⟨o⟩ := orientations p.a p.color_a
    exact ⟨StepThree.opposite_of_radical_intersection source hb p.a p.color_a o (kernel hH)⟩
  · intro d hd
    obtain ⟨t, hat, hdt⟩ := exists_common_neighbor_of_dist_two R p.a d hd.1
    obtain ⟨o⟩ := orientations d (moving_color p.color_a hd)
    exact StepThree.moving_symmetric_of_edge_eq source hb modules p initial bad
      p.color_a hat hdt hd o (hedge t d hat hdt hd).symm

/-- MS93 (4.3.2)(3), conditional on the opposite moving orientation from
step (2): the actual dual section Vcirc/U, equality of the displacements
at every incident moving edge, and symmetry of the moving-neighbor relation. -/
theorem step_three (source : LocalSource L R)
    (hb : 2 < geometry.b R) (modules : ModuleFacts source geometry)
    (transfer : NormalizationTransfer R)
    (initial : ∀ q : Counterexample geometry, Nonempty (InitialFacts q))
    (orientations : ∀ a, color R a = false → Nonempty (MovingOrientationAt a))
    (p : Counterexample geometry) (bad : ¬ ⁅V R p.a, Q R p.a⁆ ≤ fixedCore R p.a) :
    StepThreeAt geometry p.a := by
  exact step_three_of_alpha_and_kernel source hb modules transfer initial orientations p bad
    (StepThree.alpha_commutator source hb modules transfer initial orientations)
    (StepThree.radical_intersection_bound source hb modules transfer initial orientations p bad)

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.PairingControl.FirstPairing
