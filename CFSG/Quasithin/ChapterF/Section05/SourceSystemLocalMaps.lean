module
public import CFSG.Quasithin.ChapterF.Section05.ModelSystem
public import Theory.GroupTheory.GraphUniquenessSystem.CosetConstruction
public import CFSG.Quasithin.ChapterF.Section05.ExceptionalLocal.FusionFacts

/-!
# The source uniqueness system from its compatible local maps

The concrete orthogonal model already supplies both local generation identities.
Transport them through the marked vertex and local isomorphisms before constructing
the source system. This avoids separate maximal-subgroup arguments. The maps have
exactly the agreement and subgroup-membership conditions required of a similarity;
no system or ambient recognition is assumed in their types.

The original fusion theorem supplies global generation from the graph-centralizer
join, and ambient simplicity supplies faithful coset action. The final consumer
retains only the edge-conjugation identity of an equivalence, whose source proof
uses the marked cyclic four-group in F.5.7.

Source: Aschbacher--Smith F.5.6--7, printed pp.302--303; the original simple-group
application is 13.5.17. All earlier source premises retain their literal maps.
-/

@[expose] public noncomputable section
namespace CFSG.Quasithin.ChapterF.Section05
open Subgroup Theory.GroupTheory Theory.GroupTheory.GraphUniquenessSystem
open GreenBook.LieModels.UnitaryFour ExceptionalLocal
local notation "hn" => Nat.le_refl 1
variable {G G0 : Type*} [Group G] [Group G0]

private theorem sup_eq_of_local_equiv {X : Type*} [Group X]
    (A : Subgroup X) (B : Subgroup G) (e : A ≃* B)
    (P Q : Subgroup X) (P' Q' : Subgroup G)
    (hP : P ≤ A) (hQ : Q ≤ A) (hgen : P ⊔ Q=A)
    (hP' : P' ≤ B) (hQ' : Q' ≤ B)
    (heP : ∀a : A, (a:X)∈P → (e a:G)∈P')
    (heQ : ∀a : A, (a:X)∈Q → (e a:G)∈Q') : P' ⊔ Q'=B := by
  apply le_antisymm (sup_le hP' hQ')
  intro b hb
  let f := B.subtype.comp e.toMonoidHom
  have hp : P.subgroupOf A ≤ (P' ⊔ Q').comap f := fun a ha =>
    mem_sup_left (heP a ha)
  have hq : Q.subgroupOf A ≤ (P' ⊔ Q').comap f := fun a ha =>
    mem_sup_right (heQ a ha)
  have ht : P.subgroupOf A ⊔ Q.subgroupOf A=⊤ := by
    rw [←subgroupOf_sup hP hQ,hgen,subgroupOf_self]
  have hh : (e.symm ⟨b,hb⟩)∈(P' ⊔ Q').comap f :=
    (ht ▸ sup_le hp hq) (mem_top _)
  change (e (e.symm ⟨b,hb⟩):G)∈P' ⊔ Q' at hh
  simpa only [e.apply_symm_apply] using hh

open OmegaSixThree.OrthogonalityGraph (modelSystem)
local notation "O" => OmegaSixThree.omegaPlusSixThree
variable [Finite G] [IsSimpleGroup G]
variable (c : RankTwoAmalgam.FaithfulCompletion (Extension.amalgam 1 hn) (G := G0))
  (i : G0 →* G) (z : pointParabolic 1 hn) (h : Source.Hypotheses c i z)
  (R : Sylow 2 (C c i)) (hR : Tf c i ≤ (R : Subgroup (C c i)))
  (hcentral : C c i = Rimage c i R ⊔ D c i)
  (r : G) (hrH : r ∈ H c i) (hrnot : r ∉ i.range)
  (eV : modelSystem.vertexGroup ≃* i.range) (eH : modelSystem.H ≃* H c i)
  (hagree : ∀ (g : O) (hgH : g∈modelSystem.H) (hgv : g∈modelSystem.vertexGroup),
    (eV ⟨g,hgv⟩:G)=(eH ⟨g,hgH⟩:G))
  (hlocalV : ∀a : modelSystem.H, (a:O)∈modelSystem.vertexGroup ↔ (eH a:G)∈i.range)
  (hedge : ∀a : modelSystem.vertexGroup, (a:O)∈modelSystem.edgeGroup ↔
    (eV a:G)∈i.range ⊓ i.range.comap (MulAut.conj r⁻¹).toMonoidHom)
  (hlocalE : ∀a : modelSystem.H, (a:O)∈modelSystem.edgeSetGroup ↔
    (eH a:G)∈edgeStabilizer G (Cosets.vertex i.range 1) (Cosets.vertex i.range r))

/-- Transport local generation from the actual model into the source coset action. -/
def sourceCosetSystemOfMaps : System G (G ⧸ i.range) where
  graph := Cosets.graph i.range r hrnot
  H := H c i
  x := Cosets.vertex i.range 1
  y := Cosets.vertex i.range r
  adjacent := Cosets.graph_adj_base i.range r hrnot
  preserves := Cosets.preserves i.range r hrnot
  faithful := by
    apply Cosets.faithful
    rcases (inferInstance : i.range.normalCore.Normal).eq_bot_or_eq_top with hb | ht
    · exact hb
    · exact (hrnot (i.range.normalCore_le (ht ▸ mem_top r))).elim
  vertex_transitive := Cosets.transitive i.range
  edge_transitive := Cosets.edge_transitive i.range r hrnot
  local_orbit := ⟨⟨r,hrH⟩,by simp⟩
  generate := by
    rw [Cosets.stabilizer_base,sup_comm]
    exact source_generation_of_graph_centralizer c i z h R hR hcentral
  vertex_generate := by
    rw [Cosets.stabilizer_base,Cosets.edgeFixer_eq]
    apply sup_eq_of_local_equiv modelSystem.vertexGroup i.range eV modelSystem.edgeGroup
      (modelSystem.H ⊓ modelSystem.vertexGroup) _ _ inf_le_left inf_le_right modelSystem.vertex_generate
      inf_le_left inf_le_right
    · intro a ha
      exact (hedge a).mp ha
    · intro a ha
      refine ⟨?_,(eV a).property⟩
      rw [hagree a ha.1 a.property]
      exact (eH ⟨a,ha.1⟩).property
  local_generate := by
    rw [Cosets.stabilizer_base]
    apply sup_eq_of_local_equiv modelSystem.H (H c i) eH (modelSystem.H ⊓ modelSystem.edgeSetGroup)
      (modelSystem.H ⊓ modelSystem.vertexGroup) _ _ inf_le_left inf_le_left modelSystem.local_generate
      inf_le_left inf_le_left
    · intro a ha
      exact ⟨(eH a).property,(hlocalE a).mp ha.2⟩
    · intro a ha
      exact ⟨(eH a).property,(hlocalV a).mp ha.2⟩

/-- The supplied marked maps give a similarity to the constructed source system. -/
def sourceCosetSimilarityOfMaps : Similarity modelSystem
    (sourceCosetSystemOfMaps c i z h R hR hcentral r hrH hrnot eV eH
      hagree hlocalV hedge hlocalE) where
  vertexIso := eV.trans (MulEquiv.subgroupCongr (Cosets.stabilizer_base i.range).symm)
  localIso := eH
  agree := hagree
  local_vertex := by
    intro a
    change (a:O)∈modelSystem.vertexGroup ↔ (eH a:G)∈MulAction.stabilizer G (Cosets.vertex i.range 1)
    rw [Cosets.stabilizer_base]
    exact hlocalV a
  edge := by
    intro a
    change (a:O)∈modelSystem.edgeGroup ↔ (eV a:G)∈edgeFixer G (Cosets.vertex i.range 1) (Cosets.vertex i.range r)
    rw [Cosets.edgeFixer_eq]
    exact hedge a
  local_edge := hlocalE

/-- The literal F.5 endpoint using compatible local maps, with no additional
local maximality or involution-fusion premises. -/
theorem source_ambient_of_compatible_maps
    (hs : (sourceCosetSimilarityOfMaps c i z h R hR hcentral r hrH hrnot eV eH
      hagree hlocalV hedge hlocalE).IsEquivalence) :
    Nonempty (G ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 4) (ZMod 3)) :=
  CompletionRecognition.source_ambient_of_model_equivalence i _
    (sourceCosetSimilarityOfMaps c i z h R hR hcentral r hrH hrnot eV eH
      hagree hlocalV hedge hlocalE) hs

end CFSG.Quasithin.ChapterF.Section05
