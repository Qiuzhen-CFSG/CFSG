module

public import CFSG.Quasithin.ChapterF.Section05.ModelSystem
public import Theory.GroupTheory.GraphUniquenessSystem.UniversalCompletion.LocalHom

/-!
# The direct model homomorphism in F.5

Compatible vertex and triangle-stabilizer maps from the concrete orthogonal
model lift directly into the source ambient group. The already proved model
cycle base discharges the geometric input. Only agreement on the original
intersection and the genuine F.5.7 edge-conjugation identity remain; a target
coset graph, reverse membership conditions, and edge-map injectivity are not
needed to construct the homomorphism.

Source: Aschbacher--Smith F.5.7--F.5.8, printed pp.303--304.
-/

public section
namespace CFSG.Quasithin.ChapterF.Section05.CompletionRecognition
open Theory.GroupTheory.GraphUniquenessSystem
open OmegaSixThree.OrthogonalityGraph

local notation "Model" => OmegaSixThree.omegaPlusSixThree
variable {G : Type*} [Group G]

/-- The literal model cycle base lifts the two original local maps without
constructing a graph or uniqueness system on the target group. -/
theorem model_hom_of_local_conjugation
    (vertexHom : modelSystem.vertexGroup →* G) (localHom : modelSystem.H →* G)
    (agree : ∀ (g : Model) (hgH : g ∈ modelSystem.H)
      (hgx : g ∈ modelSystem.vertexGroup),
      vertexHom ⟨g,hgx⟩ = localHom ⟨g,hgH⟩)
    (t : modelSystem.H) (htx : (t : Model) • modelSystem.x = modelSystem.y)
    (hty : (t : Model) • modelSystem.y = modelSystem.x)
    (hconj : ∀ b : modelSystem.edgeGroup,
      vertexHom ⟨(t : Model) * b * (t : Model)⁻¹,
        (modelSystem.conj_mem_edgeGroup htx hty b.property).1⟩ =
      localHom t * vertexHom ⟨b,b.property.1⟩ * (localHom t)⁻¹) :
    ∃! f : Model →* G,
      (∀ a : modelSystem.vertexGroup, f a = vertexHom a) ∧
      (∀ a : modelSystem.H, f a = localHom a) :=
  modelSystem.existsUnique_hom_of_local_conjugation vertexHom localHom agree
    t htx hty hconj
    (GraphRecognition.model_isBase modelSystem rfl modelLocalTriangle model_triangle_orbit)

end CFSG.Quasithin.ChapterF.Section05.CompletionRecognition
