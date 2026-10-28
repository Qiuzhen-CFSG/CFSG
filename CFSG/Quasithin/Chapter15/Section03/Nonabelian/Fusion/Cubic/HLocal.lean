module

public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Cubic.HLocal.Involution
public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Cubic.HLocal.Count
public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Cubic.HLocal.CubicModel

/-!
# H-local cubic calculations for 15.3.60–61(1)

The recognized actor has order 336, and each Sylow three-group of H has
order three. A supplied square-one source element swapping the actual
natural and dual summands has an outer actor image; this constructs a
subgroup of order three in its actor centralizer.

For the other calculation, the source centralizer maps onto its full actor
centralizer. Its kernel is the fixed subgroup of U, and fixed points lift
through the actual central subgroup Z. The recognized natural-plus-dual
action gives four quotient fixed points, so the kernel has order eight.
The actor centralizer has order six; hence the source centralizer has order
48. This constructs a Sylow two-group of order sixteen and its ambient
image, with both intrinsic model counts discharged.

The recognized plus-type central product, literal quotient action and
quadratic geometry are retained throughout. No splitting of H is assumed.
The earlier recognition and core conclusions remain explicit inputs;
the parent cubic assembly supplies the source involution and proves nonfusion.
Source: Aschbacher–Smith, combined manuscript (1 March 2004), pp.1148–1150.
-/

public section

open Subgroup
namespace CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Cubic.HLocal
variable {G : Type*} [Group G] [Finite G] (Z ZS : Subgroup G)
  [(Z.subgroupOf (closureU Z ZS)).Normal]

/-- The source cubic fixes eight elements of the actual extraspecial kernel. -/
theorem kernelFixed_card_eight (d : Recognition Z ZS)
    (P : Sylow 3 (centralizerH Z)) : Nat.card (kernelFixed Z ZS d P) = 8 := by
  rw [kernelFixed_card Z ZS d P, quotientFixed_card Z ZS d P]

/-- The H-local centralizer has order 48, by its actual fixed kernel and actor image. -/
theorem centralizer_card (d : Recognition Z ZS) (P : Sylow 3 (centralizerH Z)) :
    Nat.card (centralizer ((P : Subgroup (centralizerH Z)) : Set (centralizerH Z))) = 48 := by
  rw [centralizer_card_formula Z ZS d P, quotientFixed_card Z ZS d P,
    cubic_actor_centralizer_card Z ZS d P]

/-- A Sylow two-group of the H-local centralizer has order sixteen.
Its specified ambient image retains both that order and its centralizing property. -/
theorem sylow_centralizer (d : Recognition Z ZS) (P : Sylow 3 (centralizerH Z)) :
    ∃ S : Sylow 2 (centralizer ((P : Subgroup (centralizerH Z)) : Set (centralizerH Z))),
      Nat.card S = 16 ∧
      ∃ R : Subgroup G,
        R = ((S : Subgroup _).map
          (centralizer ((P : Subgroup (centralizerH Z)) : Set (centralizerH Z))).subtype).map
          (centralizerH Z).subtype ∧
        IsPGroup 2 R ∧ Nat.card R = 16 ∧
        R ≤ centralizer (((P : Subgroup (centralizerH Z)).map (centralizerH Z).subtype) :
          Set G) :=
  sylow_centralizer_of_model_counts Z ZS d P
    (quotientFixed_card Z ZS d P) (cubic_actor_centralizer_card Z ZS d P)

/-- The ambient two-subgroup needed to separate the two source cubic classes. -/
theorem exists_ambient_centralizer_sixteen (d : Recognition Z ZS)
    (P : Sylow 3 (centralizerH Z)) :
    ∃ R : Subgroup G, IsPGroup 2 R ∧ Nat.card R = 16 ∧
      R ≤ centralizer (((P : Subgroup (centralizerH Z)).map (centralizerH Z).subtype) :
        Set G) := by
  obtain ⟨_, _, R, _, hR, hcard, hcentralizes⟩ := sylow_centralizer Z ZS d P
  exact ⟨R, hR, hcard, hcentralizes⟩

end CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Cubic.HLocal
