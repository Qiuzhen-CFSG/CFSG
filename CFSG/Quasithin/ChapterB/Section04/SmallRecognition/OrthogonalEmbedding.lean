module

public import CFSG.Quasithin.ChapterB.Section04.SmallRecognition.Orthogonal
public import CFSG.Quasithin.ChapterB.Section04.SmallRecognition.OrthogonalEmbedding.Presentation

/-!
# The line-presentation route to the marked orthogonal embedding

The permutation-module descent constructs a marked injective intertwiner from
one local line relation and the concrete model's line geometry. The original
orbit-spanning hypothesis then supplies the actual module equivalence via
`lemma_B_4_13_of_embedding`.

This assembly remains conditional: the parabolic seed's line relation and the
orthogonal model's transitivity, kernel presentation and two-point coverage
are explicit premises, not consequences asserted by this module.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
manuscript (1 March 2004), Lemma B.4.13, printed pp.97–98.
-/

public section
open Representation
open scoped MatrixGroups

namespace CFSG.Quasithin.ChapterB.SmallRecognition
open OrthogonalEmbedding
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]

/-- Construct the marked embedding once the seed relation and model geometry are supplied. -/
theorem orthogonalEmbedding_of_line_presentation (e : G ≃* PSL(4, ZMod 2))
    (ρ : Representation (ZMod 2) G V) (v : V) (s : OrthogonalSeed e ρ v)
    (hcover : ∀ w : OrthogonalSpace,
      ∃ p q : PointOrbit e s.point, w = p.val - q.val)
    (hker : LinearMap.ker (pointEvaluation e s.point) ≤ lineRelations e s.point)
    (htrans : LineTransitive e s.point)
    (hline : HasLineRelation e ρ v s.point) :
    ∃ f : IntertwiningMap (orthogonalAction e) ρ,
      Function.Injective f ∧ f s.point = v :=
  exists_intertwiner_of_presentation e ρ v s.point s.stabilizer hcover hker
    (respectsLines_of_one_line e ρ v s.point s.stabilizer htrans hline)

/-- Apply the line construction to the original spanning orbit in B.4.13. -/
theorem orthogonalEquiv_of_line_presentation (e : G ≃* PSL(4, ZMod 2))
    (ρ : Representation (ZMod 2) G V) (v : V) (s : OrthogonalSeed e ρ v)
    (hspan : Submodule.span (ZMod 2) (Set.range fun g => ρ g v) = ⊤)
    (hcover : ∀ w : OrthogonalSpace,
      ∃ p q : PointOrbit e s.point, w = p.val - q.val)
    (hker : LinearMap.ker (pointEvaluation e s.point) ≤ lineRelations e s.point)
    (htrans : LineTransitive e s.point)
    (hline : HasLineRelation e ρ v s.point) :
    Nonempty (ρ.Equiv (orthogonalAction e)) :=
  lemma_B_4_13_of_embedding e ρ v s hspan
    (orthogonalEmbedding_of_line_presentation e ρ v s hcover hker htrans hline)

end CFSG.Quasithin.ChapterB.SmallRecognition
