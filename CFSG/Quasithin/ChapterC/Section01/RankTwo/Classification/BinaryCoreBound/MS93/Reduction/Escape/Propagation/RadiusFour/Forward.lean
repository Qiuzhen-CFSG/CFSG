module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.Propagation.RadiusFour.Forward.Reduction
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.Propagation.RadiusFour.Forward.Stages
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.Propagation.RadiusFour.Forward.Reversal
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.Propagation.RadiusFour.Forward.Products

/-!
# The forward radius-four argument

Noncommutation selects an actual critical pair on a backwards extension of
the original geodesic. Movement at the sixth predecessor makes its reversed
pair a contrary configuration, using the local normal-product bound. Its
central critical commutator then contradicts the trivial central intersection.
The local-product noncontainment similarly excludes movement of mu at d.

The final theorem constructs both intermediate records from the preceding
source stages. Thus commutation, the local join and nonmovement hold for every
supplied geodesic configuration and its actual central orbit witnesses.

Source: Meierfrankenfeld--Stellmacher (1993), (4.3.8), first three paragraphs
of printed p.889, stopping before the final contradiction for (4.3).
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.Propagation.RadiusFour.Forward
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M} {geometry : Geometry R}

/-- The reversed critical configuration proves commutation once its two
local-algebra premises have been supplied. -/
theorem commutation_of_reversal (source : LocalSource L R)
    (rigidity : RigidityFacts geometry) (backward : BackwardFacts geometry)
    (reversal : ReversalFacts geometry) : CommutationFacts geometry := by
  intro p d t₃ t₅ hd h₃ h₅ w
  by_contra hn
  obtain ⟨x, hx, hxa, hal, hcrit⟩ := exists_critical_of_not_commuting
    p.color_a (lam_color p w) (lam_distance_bound p h₅ w) hn
  obtain ⟨s, hs⟩ := p.exists_before (show 6 ≤ geometry.b R by
    have := rigidity.six_lt p
    omega)
  have hmove := reversal.selected_moving p d t₃ t₅ s hd h₃ h₅ hs w x hx hcrit hxa hal
  obtain ⟨y, hxy, hya⟩ := exists_midpoint hxa
  have hb : 4 < geometry.b R := lt_trans (by decide) (rigidity.six_lt p)
  exact selected_contradiction source (by omega) backward p h₅ w
    (reversal.radius_disjoint p) x y hx hcrit hxa hal hxy hya
    (selected_trapped_of_moving hb backward p hs hmove hya.le)

/-- Final assembly with the remaining source outputs explicit. Their
producers must be discharged before claiming the source forward theorem. -/
theorem forwardFacts_of_stages (source : LocalSource L R)
    (rigidity : RigidityFacts geometry) (backward : BackwardFacts geometry)
    (reversal : ReversalFacts geometry) (products : ProductFacts geometry) :
    ForwardFacts geometry where
  commutation := commutation_of_reversal source rigidity backward reversal
  nonmoving p d t₃ t₅ hd h₃ h₅ w :=
    nonmoving_of_not_le (lt_trans (by decide) (rigidity.six_lt p)) backward p hd w
      (products.first_not_le p d t₃ t₅ hd h₃ h₅ w)
  radius_join := products.radius_join

/-- The first three paragraphs on printed p.889: radius-four commutation,
nonmovement of the specified first conjugate, and the full local kernel join.
Both reversal and product premises are proved from the preceding stages. -/
theorem forwardFacts (source : LocalSource L R) (hb : 2 < geometry.b R)
    (modules : ModuleFacts source geometry)
    (initial : ∀ p : Counterexample geometry, Nonempty (InitialFacts p))
    (control : ∀ p : Counterexample geometry, LocalControl p)
    (edge : EdgeTransfer geometry) (rigidity : RigidityFacts geometry)
    (backward : BackwardFacts geometry) : ForwardFacts geometry :=
  forwardFacts_of_stages source rigidity backward
    (reversalFacts source hb modules initial)
    (Products.productFacts source hb modules initial control edge rigidity backward)

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.Propagation.RadiusFour.Forward
