module

public import Stellmacher.Recognition.Parrott.LocalGeneratorData
public import Theory.SpecificGroups.Tits.RecognitionSylowSeed

/-!
# Intermediate generators in Parrott's Sylow construction

These data retain the actual E,F,J,T and marked elements z,t,v while recording
both alternatives of equations (1)–(15). They do not assert existence. The
normalization module converts Case 2 to Case 1 inside the same subgroups; the
remaining construction chooses x,y to obtain equations (16)–(19).

Source: Parrott (1972), §3, pp.678–680. The a,x alternative is proved just before
(6), and the two alternatives for the core relations are printed on p.679.
-/

open Subgroup
namespace Stellmacher.Recognition
variable {G : Type*} [Group G] {z : G} {e : ParrottSecondElementaryData z}

/-- The actual subgroup witnesses through (15), permitting either printed case. -/
public structure ParrottSylowSeedData (n : ParrottNormalizerFusionData e) (caseTwo : Bool) where
  u : G
  w : G
  a : G
  b : G
  c : G
  d : G
  x : G
  derived_basis : closure ({z, n.t, n.v, u, w} : Set G) =
    (commutator (pCore 2 (centralizer ({z} : Set G)))).map
      ((centralizer ({z} : Set G)).subtype.comp
        (pCore 2 (centralizer ({z} : Set G))).subtype)
  elementary_basis : closure ({z, n.t, n.v, u, a} : Set G) = e.F
  core_generators : closure ({a, b, c, d} : Set G) =
    (pCore 2 (centralizer ({z} : Set G))).map (centralizer ({z} : Set G)).subtype
  sylow_generators : closure ({x, a, b, c, d} : Set G) = (e.sylow : Subgroup G)
  relations : Tits.ParrottSylowSeedRelations caseTwo z n.t n.v u w a b c d x

namespace ParrottSylowSeedData
variable {n : ParrottNormalizerFusionData e} {caseTwo : Bool}

/-- The intermediate outer generator belongs to the supplied Sylow subgroup. -/
public theorem x_mem_sylow (f : ParrottSylowSeedData n caseTwo) : f.x ∈ e.sylow := by
  change f.x ∈ (e.sylow : Subgroup G)
  rw [← f.sylow_generators]
  exact subset_closure (by simp)

end ParrottSylowSeedData
end Stellmacher.Recognition
