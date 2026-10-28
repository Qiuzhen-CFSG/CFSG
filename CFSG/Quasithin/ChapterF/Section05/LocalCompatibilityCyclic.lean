module
public import CFSG.Quasithin.ChapterF.Section05.ModelEdge
public import Theory.SpecificGroups.OmegaSixThree.TriangleLocal.CyclicRoot

/-!
# Actual local-map agreement from the F.5 cyclic subgroup

The supplied source vertex and local isomorphisms retain their ambient
subgroup inclusions. An isomorphism of their vertex intersection records the
restriction of the actual vertex map. A source element whose square is the
marked graph involution and which centralizes the marked independent `S₄`
eliminates the local central twist. The corrected local map then agrees
pointwise with the original vertex map, as required by `ModelLocalHom`.

The square and commutation conditions are precisely the source `R₀` inputs;
their construction remains with the original F.5.5 source branch.
Source: Aschbacher--Smith F.5.5 and F.5.7, printed pp.301--303.
-/

public noncomputable section
namespace CFSG.Quasithin.ChapterF.Section05.CompletionRecognition
open OmegaSixThree OrthogonalityGraph TriangleLocal TriangleLocal.LocalCompatibility
local notation "Model" => omegaPlusSixThree

/-- The literal source comparison agrees on every element of the model
intersection once its cyclic-four mark is supplied. -/
theorem model_local_agreement_of_commuting_root {G : Type*} [Group G]
    (M J : Subgroup G) (eV : modelSystem.vertexGroup ≃* M)
    (rho : modelSystem.H ≃* J)
    (hrho : ∀ g : modelSystem.H, (rho g : G) ∈ M ↔ g ∈ vertexLocal)
    (s : vertexLocal ≃* M.subgroupOf J)
    (hs : ∀ g : vertexLocal, ((s g).val : G) =
      (eV ⟨g.val.val,g.property⟩ : G))
    (r : G) (hr : r ∈ J)
    (hsq : r ^ 2 = (eV modelGraphElement : G))
    (hc : ∀ g : vertexLocal, g.val ∈ complementFactor →
      r * ((s g).val : G) = ((s g).val : G) * r) :
    ∃ e : modelSystem.H ≃* J,
      (∀ (g : Model) (hgH : g ∈ modelSystem.H) (hgx : g ∈ modelSystem.vertexGroup),
        (eV ⟨g,hgx⟩ : G) = (e ⟨g,hgH⟩ : G)) ∧
      (∀ g : modelSystem.H, (e g : G) ∈ M ↔ g ∈ vertexLocal) := by
  let v := vertexProductEquiv.symm (reflection,1)
  have hv : (⟨v.val.val,v.property⟩ : modelSystem.vertexGroup) = modelGraphElement := by
    apply Subtype.ext
    exact congrArg (fun h : H => h.val) marked_reflection_eq_graph
  have hsq' : (⟨r,hr⟩ : J) ^ 2 = (s v).val := by
    apply Subtype.ext
    change r ^ 2 = ((s v).val : G)
    rw [hs, hv, hsq]
  have hc' (g : vertexLocal) (hg : g.val ∈ complementFactor) :
      (⟨r,hr⟩ : J) * (s g).val = (s g).val * ⟨r,hr⟩ :=
    Subtype.ext (hc g hg)
  obtain ⟨e,he,hm⟩ := compatible_local_equiv_of_commuting_root (M.subgroupOf J)
    rho hrho s ⟨r,hr⟩ hsq' hc'
  refine ⟨e,?_,hm⟩
  intro g hgH hgx
  let v : vertexLocal := ⟨⟨g,hgH⟩,hgx⟩
  exact (hs v).symm.trans (congrArg Subtype.val (he v)).symm

end CFSG.Quasithin.ChapterF.Section05.CompletionRecognition
