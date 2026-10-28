module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.Propagation.Backward.Control
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.Propagation.Backward.Stages
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.Propagation.Backward.Bound
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.Propagation.Backward.Products
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.Propagation.Backward.Moving

/-!
# The backward argument in MS93 (4.3.6)--(4.3.7)

The critical-commutator argument bounds W(t) under noncentrality at the
vertex four before the endpoint. The product step constructs the favorable
neighbor and proves normalization by the source relative normalizer
`G_a ∩ N(Q_t)`, obtaining each individual product's relative normality and
two-residual commutator bound. The three-subgroup argument then gives moving
symmetry, and transported normal products give both far-propagation clauses.

The theorem `backwardFacts` discharges all three intermediate stages from
the authorized preceding inputs. It preserves the original BackwardFacts
interface. The source version of (4.3.6), with relative-normalizer generation,
is also re-exported as `relativeBoundFacts`; the product proof uses that
corrected bound. The old edge-stabilizer conditional helpers and their
non-generation diagnostics remain separate and unchanged.

Source: Meierfrankenfeld--Stellmacher (1993), notation on p.881 and
(4.3.6)--(4.3.7), printed pp.886--888.
-/

public section

namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.Propagation.Backward
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M} {geometry : Geometry R}

/-- Complete backward propagation from the preceding source stages.
The bound, individual product normality and residual estimate, moving
symmetry, and both far clauses are all constructed here. The product stage
uses the source relative normalizer, with its action and choices proved. -/
theorem backwardFacts (source : LocalSource L R)
    (hb : 2 < geometry.b R) (modules : ModuleFacts source geometry)
    (transfer : NormalizationTransfer R)
    (initial : ∀ p : Counterexample geometry, Nonempty (InitialFacts p))
    (control : ∀ p : Counterexample geometry, LocalControl p) (edge : EdgeTransfer geometry)
    (rigidity : RigidityFacts geometry) : BackwardFacts geometry := by
  have bound := boundFacts source hb modules initial control edge rigidity
  have products := Products.productFacts source hb modules transfer initial control edge rigidity bound
  have moving := Moving.movingFacts source hb modules initial control edge rigidity products
  exact {
    backward_bound := bound.bound
    product_normal := products.products
    moving_symmetric := moving.symmetric
    far_not_moving := moving.far_not_moving
    moving_radius_bound := moving.radius_bound }

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.Propagation.Backward
