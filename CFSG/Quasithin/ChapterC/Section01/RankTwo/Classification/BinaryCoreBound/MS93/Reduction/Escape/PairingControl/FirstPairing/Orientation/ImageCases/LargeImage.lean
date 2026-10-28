module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.PairingControl.FirstPairing.Orientation.ImageCases.LargeImage.ImageOrder

/-!
# The large-image estimate in the first escape pairing

The original alpha+1,+2,+3 path is retained throughout. Forward
nonnormality proves the moving condition, and the natural-section radical
calculation puts its edge displacement in V_(alpha+3). This centralizes V_c,
so the actual large image identifies the displacement with [Z_alpha,V_c].
Finally V_c lies in C_{Q_(alpha+2)}(V_(alpha+3)), and the supplied triple
bound places that commutator in D_(alpha+2).

Every additional premise of the intermediate helpers is discharged here.
The two-case contradiction remains with ImageCases.lean.
Source: Meierfrankenfeld--Stellmacher (1993), (4.3.2)(2), first paragraph
of printed p.884.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
open scoped commutatorElement
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.PairingControl.FirstPairing.Orientation.ImageCases
variable {M : Type*} [Group M] {L R : Subgroup M} {geometry : MS93.Geometry R}

variable [Finite M]

/-- The complete final chain in the large-image case, conditional only on
placing the edge displacement in the third radius layer. -/
theorem large_image_edge_le_fixed_of_third_containment (source : LocalSource L R)
    (hb : 2 < geometry.b R) (modules : ModuleFacts source geometry)
    (initial : ∀ q : Counterexample geometry, Nonempty (InitialFacts q))
    (p : Counterexample geometry) (path : FrontPath p)
    (bounds : BoundsAt geometry path.second)
    (hi : 2 < (Q R p.a).relIndex (V R p.c))
    (hthird : edgeDisplacement p.a path.first ≤ V R path.third) :
    edgeDisplacement p.a path.first ≤ fixedCore R path.second := by
  obtain ⟨ip⟩ := initial p
  have hc := path.predecessor_centralizes_third ip
  have he := large_image_edge_eq_of_centralizes source modules initial p path hi
    (hthird.trans (le_centralizer_iff.mp hc))
  rw [he]
  apply (commutator_mono path.start_Z_le_second_V (le_inf
    (predecessor_V_le_path_kernel p path.second_before (by decide)
      (by have := ip.six_le; omega)) hc)).trans
  exact neighbor_centralizer_bound source hb path.second_color
    (adjacent_symm R path.third_second_adjacent) bounds

/-- Assemble the estimate from a third-layer placement; the source-only
producer below discharges this additional premise. -/
theorem large_image_estimate_of_third_containment (source : LocalSource L R)
    (hb : 2 < geometry.b R) (modules : ModuleFacts source geometry)
    (initial : ∀ q : Counterexample geometry, Nonempty (InitialFacts q))
    (p : Counterexample geometry) (path : FrontPath p)
    (bounds : ∀ a, color R a = false → BoundsAt geometry a)
    (hi : 2 < (Q R p.a).relIndex (V R p.c))
    (hthird : edgeDisplacement p.a path.first ≤ V R path.third) :
    LargeImageEstimate p path :=
  ⟨path.start_moving_at_second source hb modules,
    large_image_edge_le_fixed_of_third_containment source hb modules initial p path
      (bounds path.second path.second_color) hi hthird⟩

/-- MS93 (4.3.2)(2), large-image case: the original path displacement lies
in D_(alpha+2), at which alpha is a moving neighbor. Every intermediate
placement and the actual image-order comparison have been proved above. -/
theorem large_image_estimate (source : LocalSource L R)
    (hb : 2 < geometry.b R) (modules : ModuleFacts source geometry)
    (initial : ∀ q : Counterexample geometry, Nonempty (InitialFacts q))
    (p : Counterexample geometry)
    (bad : ¬ ⁅V R p.a, Q R p.a⁆ ≤ fixedCore R p.a)
    (bounds : ∀ a, color R a = false → BoundsAt geometry a)
    (hi : 2 < (Q R p.a).relIndex (V R p.c)) (path : FrontPath p) :
    LargeImageEstimate p path :=
  large_image_estimate_of_third_containment source hb modules initial p path bounds hi
    (path.edge_le_third_V source hb modules initial bad)

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.PairingControl.FirstPairing.Orientation.ImageCases
