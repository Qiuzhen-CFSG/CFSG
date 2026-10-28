module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.Propagation.Backward.Products.Individual
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.Propagation.Backward.Products.SelectionGeometry

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.Propagation.Backward.Products.RelativeNormalizer
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.Propagation.Backward.Products.Selection

/-!
# The product deduction in MS93 (4.3.7)(i)

Selection constructs a neighbor t for which the source relative normalizer
`G_a ∩ N(Q_t)` generates G_a with the critical endpoint and W(t) lies in Q_c.
RelativeNormalizer proves its action on the actual reverse-moving span and
then the local normality and residual bound for every individual product.
The theorem `productFacts` discharges every selection and normalization
premise, retaining the original preceding-stage inputs and literal output.

The old conditional edge-stabilizer API remains available separately.
Source: Meierfrankenfeld--Stellmacher (1993), printed pp.881, 887--888.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.Propagation.Backward.Products
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}
variable {geometry : Geometry R}

/-- Assembly from actual edge choices. Their existence is a separate
remaining source argument, and must be discharged by this module's owner. -/
theorem productFacts_of_selected_edges (source : LocalSource L R)
    (initial : ∀ p : Counterexample geometry, Nonempty (InitialFacts p))
    (rigidity : RigidityFacts geometry)
    (selected : ∀ p : Counterexample geometry, ∃ t,
      Adjacent R p.a t ∧
        (stabilizer R p.a ⊓ stabilizer R t) ⊔ Z R p.a' = stabilizer R p.a ∧
        backwardSpan geometry p.a t ≤ Q R p.c) : ProductFacts geometry := by
  constructor
  intro p d hd hmove
  obtain ⟨t, hat, hgen, hW⟩ := selected p
  obtain ⟨hi⟩ := initial p
  exact products_of_selected_edge source p (by have := rigidity.six_lt p; omega)
    hi t hat hgen hW d hd hmove

/-- Product assembly using the source relative normalizer. Its action on
W(t) is proved, so only the selected neighbor and its kernel bound remain
explicit in this intermediate interface. -/
theorem productFacts_of_selected_relative_normalizers (source : LocalSource L R)
    (initial : ∀ p : Counterexample geometry, Nonempty (InitialFacts p))
    (rigidity : RigidityFacts geometry)
    (selected : ∀ p : Counterexample geometry, ∃ t,
      Adjacent R p.a t ∧
        (stabilizer R p.a ⊓ normalizer (Q R t : Set (FreeAmalgam R))) ⊔
          Z R p.a' = stabilizer R p.a ∧
        backwardSpan geometry p.a t ≤ Q R p.c) : ProductFacts geometry := by
  constructor
  intro p d hd hmove
  obtain ⟨t, hat, hgen, hW⟩ := selected p
  obtain ⟨hi⟩ := initial p
  exact products_of_selected_relativeNormalizer source p
    (by have := rigidity.six_lt p; omega) hi t hat hgen hW d hd hmove

/-- Original MS93 (4.3.7)(i): every reverse-moving distance-two neighbor
has its product normal in G_a and its two-residual commutator in Vcirc_a.
The original transfer and bound inputs are retained; the selected witnesses
are constructed by the stronger preceding-stage selection theorem. -/
theorem productFacts (source : LocalSource L R)
    (hb : 2 < geometry.b R) (modules : ModuleFacts source geometry)
    (_transfer : NormalizationTransfer R)
    (initial : ∀ p : Counterexample geometry, Nonempty (InitialFacts p))
    (control : ∀ p : Counterexample geometry, LocalControl p) (edge : EdgeTransfer geometry)
    (rigidity : RigidityFacts geometry) (_bound : BoundFacts geometry) :
    ProductFacts geometry := by
  exact productFacts_of_selected_relative_normalizers source initial rigidity
    (Selection.relative_edge_choices source hb modules initial control edge rigidity).2

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.Propagation.Backward.Products
