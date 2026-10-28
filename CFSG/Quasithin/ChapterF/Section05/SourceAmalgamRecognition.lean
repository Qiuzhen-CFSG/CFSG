module
public import CFSG.Quasithin.ChapterF.Section05.ModelLocalHom
public import CFSG.Quasithin.ChapterF.Section05.ModelEdge
public import CFSG.Quasithin.ChapterF.Section05.ExceptionalLocal.FusionFacts

/-!
# Direct F.5 recognition from the model amalgam

The concrete model has a proved normal cycle base. Its compatible rank-three
amalgam maps therefore extend to a homomorphism into the original ambient
group. Source fusion and the graph-centralizer join make the image all of G.
The model is simple, and the original root involution excludes a trivial map,
so the extension is an isomorphism with PSL₄(3).

This route requires neither a source coset system nor reverse subgroup
membership or maximality proofs. The actual maps on the model vertex, setwise
edge and local group, including their three intersection agreements, remain
genuine obligations; they retain the F.5.7 conjugation relation.

Source: Aschbacher--Smith F.5.7--8, printed pp.303--304, using the universal
completion theorem of Aschbacher, Sporadic Groups, sections35--37.
-/

public noncomputable section
namespace CFSG.Quasithin.ChapterF.Section05
open Subgroup Theory.GroupTheory Theory.GroupTheory.GraphUniquenessSystem
open GreenBook.LieModels.UnitaryFour ExceptionalLocal
open OmegaSixThree.OrthogonalityGraph
local notation "O" => OmegaSixThree.omegaPlusSixThree
local notation "hn" => Nat.le_refl 1
variable {G G0 : Type*} [Group G] [Group G0] [Finite G]
  (c : RankTwoAmalgam.FaithfulCompletion (Extension.amalgam 1 hn) (G := G0))
  (i : G0 →* G) (z : pointParabolic 1 hn) (h : Source.Hypotheses c i z)
  (R : Sylow 2 (C c i)) (hR : Tf c i ≤ (R : Subgroup (C c i)))
  (hcentral : C c i = Rimage c i R ⊔ D c i)

include h hR hcentral
theorem source_ambient_of_model_amalgam
    (m : modelSystem.AmalgamMap G)
    (hv : m.vertexHom.range = i.range)
    (hl : m.localHom.range = H c i) :
    Nonempty (G ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 4) (ZMod 3)) := by
  let _ := OmegaSixThree.omega_simple
  have hb : modelSystem.IsBase := GraphRecognition.model_isBase modelSystem rfl
    modelLocalTriangle CompletionRecognition.model_triangle_orbit
  let f := m.liftOfBase hb
  have hsur : Function.Surjective f.hom := by
    apply MonoidHom.range_eq_top.mp
    apply top_unique
    rw [←source_generation_of_graph_centralizer c i z h R hR hcentral, ←hv, ←hl]
    apply sup_le
    · rintro a ⟨b,rfl⟩
      exact ⟨b,f.onVertex b⟩
    · rintro a ⟨b,rfl⟩
      exact ⟨b,f.onLocal b⟩
  have hinj : Function.Injective f.hom := by
    rcases (inferInstance : f.hom.ker.Normal).eq_bot_or_eq_top with hk | hk
    · exact (MonoidHom.ker_eq_bot_iff f.hom).mp hk
    · have hf : f.hom=1 := MonoidHom.ker_eq_top_iff.mp hk
      obtain ⟨a,ha⟩ := hsur (rootElement c i z)
      have hz : rootElement c i z=1 := by simpa [hf] using ha.symm
      have ho := source_root_order c i z h
      simp [hz] at ho
  exact ⟨(MulEquiv.ofBijective f.hom ⟨hinj,hsur⟩).symm.trans OmegaSixThree.omegaEquivPSL⟩

open CompletionRecognition

/-- The actual F.5 endpoint from two agreeing local isomorphisms and the
conjugation identity for the specified model reversal. Every source-graph,
edge-intersection, and reverse membership obligation is eliminated. -/
theorem source_ambient_of_marked_local_conjugation
    (eV : modelSystem.vertexGroup ≃* i.range) (eH : modelSystem.H ≃* H c i)
    (hagree : ∀ (g : O) (hgH : g∈modelSystem.H) (hgv : g∈modelSystem.vertexGroup),
      (eV ⟨g,hgv⟩:G)=(eH ⟨g,hgH⟩:G))
    (hconj : ∀ b : modelSystem.edgeGroup,
      (eV ⟨(modelEdgeReversal : O) * b * (modelEdgeReversal : O)⁻¹,
        (modelSystem.conj_mem_edgeGroup modelEdgeReversal_first
          modelEdgeReversal_second b.property).1⟩ : G) =
      (eH modelEdgeReversal : G) * (eV ⟨b,b.property.1⟩ : G) *
        (eH modelEdgeReversal : G)⁻¹) :
    Nonempty (G ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 4) (ZMod 3)) := by
  let v : modelSystem.vertexGroup →* G := i.range.subtype.comp eV.toMonoidHom
  let l : modelSystem.H →* G := (H c i).subtype.comp eH.toMonoidHom
  have ha : ∀ (g : O) (hh : g∈modelSystem.H) (hv : g∈modelSystem.vertexGroup),
      v ⟨g,hv⟩ = l ⟨g,hh⟩ := hagree
  have hc : ∀ b : modelSystem.edgeGroup,
      v ⟨(modelEdgeReversal : O) * b * (modelEdgeReversal : O)⁻¹,
        (modelSystem.conj_mem_edgeGroup modelEdgeReversal_first
          modelEdgeReversal_second b.property).1⟩ =
      l modelEdgeReversal * v ⟨b,b.property.1⟩ * (l modelEdgeReversal)⁻¹ := hconj
  let m := modelSystem.amalgamMapOfLocalConjugation v l ha modelEdgeReversal
    modelEdgeReversal_first modelEdgeReversal_second hc
  apply source_ambient_of_model_amalgam c i z h R hR hcentral m
  · dsimp only [m]
    rw [System.amalgamMapOfLocalConjugation_vertexHom]
    ext g
    constructor
    · rintro ⟨a,rfl⟩
      exact (eV a).property
    · intro hg
      exact ⟨eV.symm ⟨g,hg⟩, congrArg Subtype.val (eV.apply_symm_apply _)⟩
  · dsimp only [m]
    rw [System.amalgamMapOfLocalConjugation_localHom]
    ext g
    constructor
    · rintro ⟨a,rfl⟩
      exact (eH a).property
    · intro hg
      exact ⟨eH.symm ⟨g,hg⟩, congrArg Subtype.val (eH.apply_symm_apply _)⟩


end CFSG.Quasithin.ChapterF.Section05
