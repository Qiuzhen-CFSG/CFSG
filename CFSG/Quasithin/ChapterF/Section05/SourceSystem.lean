module
public import CFSG.Quasithin.ChapterF.Section05.ModelSystem
public import CFSG.Quasithin.ChapterF.Section05.ExceptionalLocal.Generation
public import Theory.GroupTheory.GraphUniquenessSystem.CosetConstruction

/-!
# The source coset system for the simple-group consumer

The original 13.5.17 context makes the ambient group simple. A proper coset
stabilizer therefore has trivial normal core, so its coset action is faithful.
The proved controlled-fusion generation theorem supplies ambient generation.
The two local generation identities follow from exactly the maximal subgroups
used on printed p.302: the edge fixer in the vertex group, and the vertex
intersection in the local group. In particular, the vertex/local intersection
is not required to be maximal in the whole vertex group.

The marked edge reversal, local maximality and noncontainment remain explicit
outputs of F.5.5--7. The final consumer uses the concrete orthogonal model,
leaving only the genuine compatible local-map equivalence.

Source: Aschbacher--Smith F.5.6--7, printed pp.302--303, applied to 13.5.17.
-/

@[expose] public noncomputable section
namespace CFSG.Quasithin.ChapterF.Section05
open Subgroup Theory.GroupTheory Theory.GroupTheory.GraphUniquenessSystem
open GreenBook.LieModels.UnitaryFour
open ExceptionalLocal
local notation "hn" => Nat.le_refl 1
variable {G G0 : Type*} [Group G] [Group G0]

private theorem sup_eq_of_relative_coatom (M A B : Subgroup G)
    (hAM : A ≤ M) (hBM : B ≤ M) (hmax : IsCoatom (A.subgroupOf M))
    (hnot : ¬ B ≤ A) : A ⊔ B = M := by
  have hle : A ⊔ B ≤ M := sup_le hAM hBM
  have hi : A.subgroupOf M ≤ (A ⊔ B).subgroupOf M := by
    intro a ha
    exact mem_sup_left ha
  have htop : (A ⊔ B).subgroupOf M = ⊤ := by
    apply (hmax.ne_iff_eq_top hi).mp
    intro he
    apply hnot
    intro b hb
    have hh : (⟨b,hBM hb⟩ : M) ∈ (A ⊔ B).subgroupOf M := mem_sup_right hb
    rw [he] at hh
    exact hh
  apply le_antisymm hle
  intro a ha
  have hh : (⟨a,ha⟩ : M) ∈ (A ⊔ B).subgroupOf M := by rw [htop]; trivial
  exact hh

variable [Finite G] [IsSimpleGroup G]
variable (c : RankTwoAmalgam.FaithfulCompletion (Extension.amalgam 1 hn) (G := G0))
  (i : G0 →* G) (z : pointParabolic 1 hn) (h : Source.Hypotheses c i z)
  (R : Sylow 2 (C c i)) (hRH : Rimage c i R ≤ H c i)
  (hcentral : C c i = Rimage c i R ⊔ D c i)
  (hfusion : ∀ x ∈ Source.sylowImage c i, orderOf x = 2 →
    ∃ k ∈ i.range ⊔ H c i,
      k * rootElement c i z * k⁻¹ = x ∨
      k * Source.graphElement c i * k⁻¹ = x)
  (r : G) (hrH : r ∈ H c i) (hrnot : r ∉ i.range) (hrsq : r * r ∈ i.range)
  (hvertex : IsCoatom ((i.range ⊓ i.range.comap (MulAut.conj r⁻¹).toMonoidHom).subgroupOf i.range))
  (hlocal : IsCoatom (i.range.subgroupOf (H c i)))
  (hnot : ¬ H c i ⊓ i.range ≤ i.range ⊓ i.range.comap (MulAut.conj r⁻¹).toMonoidHom)

/-- The original coset system, using simplicity available in 13.5.17. -/
def sourceCosetSystem : System G (G ⧸ i.range) where
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
    rw [Cosets.stabilizer_base, sup_comm]
    exact source_generation_of_centralizer_join c i z h R hRH hcentral hfusion
  vertex_generate := by
    rw [Cosets.stabilizer_base, Cosets.edgeFixer_eq]
    exact sup_eq_of_relative_coatom i.range _ _ inf_le_left inf_le_right hvertex hnot
  local_generate := by
    rw [Cosets.stabilizer_base, sup_comm]
    apply sup_eq_of_relative_coatom (H c i) _ _ inf_le_left inf_le_left
    · have he : (H c i ⊓ i.range).subgroupOf (H c i) = i.range.subgroupOf (H c i) := by
        ext x
        simp only [mem_subgroupOf, mem_inf]
        exact ⟨And.right,fun hx => ⟨x.property,hx⟩⟩
      rw [he]
      exact hlocal
    · intro hle
      exact hrnot (hle ⟨hrH,Or.inr (Cosets.swap i.range r hrsq)⟩).2

/-- Actual application of the coset construction to the concrete model endpoint. -/
theorem source_ambient_of_simple_coset_equivalence
    (s : Similarity OmegaSixThree.OrthogonalityGraph.modelSystem
      (sourceCosetSystem c i z h R hRH hcentral hfusion r hrH hrnot hrsq hvertex hlocal hnot))
    (hs : s.IsEquivalence) :
    Nonempty (G ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 4) (ZMod 3)) :=
  CompletionRecognition.source_ambient_of_model_equivalence i _ s hs

end CFSG.Quasithin.ChapterF.Section05
