module

public import Stellmacher.Recognition.Parrott.SylowSeedMiddleAdjustment
public import Stellmacher.Recognition.Parrott.SylowSeedBxNormalization
public import Stellmacher.Recognition.Parrott.SylowSeedYdCoset

/-!
# Assembly of the middle Sylow normalization

The initial commutator lies in bw⟨v,z⟩. Coordinate corrections give equation
(17), preserving (16) and the centralization of b by y=x²z. Compatibility
with (17) then removes the t-error in (18), and x↦xu removes its remaining
central error. Each step uses actual seed constructors, retaining the marked
z,t,v and the prescribed elementary, core, and Sylow subgroups.

Source: D. Parrott, *A characterization of the Tits' simple group* (1972),
§3, printed p.680, equations (16)–(18).
-/

namespace Stellmacher.Recognition.ParrottSylowSeedData
variable {G : Type*} [Group G] {z : G} {e : ParrottSecondElementaryData z}
variable {n : ParrottNormalizerFusionData e}

/-- Assemble the middle relations from the initial coset bound and a
normalization of (18). The two input proofs are independent: the latter
starts from an arbitrary seed already satisfying (17). -/
public theorem exists_outer_middle_relations_of_eq17_normalization
    (f : ParrottSylowSeedData n false)
    (hax : Tits.parrottCommutator f.a f.x = 1) (hby : Commute f.b (f.x^2*z))
    (hyd : Tits.parrottCommutator (f.x^2*z) f.d = f.b*f.w ∨
      Tits.parrottCommutator (f.x^2*z) f.d = f.b*f.w*z ∨
      Tits.parrottCommutator (f.x^2*z) f.d = f.b*f.w*n.v ∨
      Tits.parrottCommutator (f.x^2*z) f.d = f.b*f.w*n.v*z)
    (hnormalize18 : ∀ g : ParrottSylowSeedData n false,
      Tits.parrottCommutator g.a g.x = 1 → Commute g.b (g.x^2*z) →
      Tits.parrottCommutator (g.x^2*z) g.d = g.b*g.w →
      ∃ g' : ParrottSylowSeedData n false, g'.OuterMiddleRelations) :
    ∃ f' : ParrottSylowSeedData n false, f'.OuterMiddleRelations := by
  obtain ⟨g, hga, hgb, hgd⟩ := f.exists_eq17_of_yd_cases hax hby hyd
  exact hnormalize18 g hga hgb hgd

/-- Normalize equations (17)–(18) on the supplied actual local subgroups,
preserving (16) and using y=x²z for the resulting seed. -/
public theorem exists_outer_middle_relations [Finite G] [IsSimpleGroup G]
    (f : ParrottSylowSeedData n false)
    (hns : ¬ Group.IsSolvable G) (hN : IsNTwoGroup G)
    (h : ParrottCentralizerHypotheses z)
    (hax : Tits.parrottCommutator f.a f.x = 1) (hby : Commute f.b (f.x^2*z)) :
    ∃ f' : ParrottSylowSeedData n false, f'.OuterMiddleRelations := by
  exact f.exists_outer_middle_relations_of_eq17_normalization hax hby
    (yd_commutator_cases hns hN h f hax hby)
    (fun g hga hgb hgd => g.exists_outer_middle_relations_of_eq17 hns hN h hga hgb hgd)

end Stellmacher.Recognition.ParrottSylowSeedData
