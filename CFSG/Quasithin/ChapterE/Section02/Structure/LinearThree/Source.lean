module

public import Theory.SpecificGroups.PSL3Even.MinimalParabolicWitness.Extension
public import Theory.GroupTheory.SylowNormalIntersection
public import CFSG.Quasithin.ChapterB.Section06To07.Structure

/-!
# The actual linear-three branch of E.2.2

Starting with the original normal subgroup K, its actual PSL₃ model, and
H=KT, Sylow conjugacy aligns the model with T∩K. Minimal parabolicity then
forces a nontrivial diagram actor in the original T and identifies the
original maximal subgroup's intersection with K as the marked Borel.
No Borel or diagram-action conclusion is assumed.

Source: Aschbacher--Smith, E.2.2(2b), printed pp.215--216.
-/

public section
open scoped MatrixGroups
open Subgroup Matrix.PSL3.LinearThree
open Matrix.PSL3.LinearThree.OuterExtensions
open Matrix.PSL3Even.MinimalParabolicWitness
namespace CFSG.Quasithin.ChapterE.Structure.LinearThree
open ChapterB
variable {H : Type*} [Group H] [Finite H]
variable (F : Type*) [Field F] [Finite F]
variable {n : ℕ} (hn : 0 < n) (hF : Nat.card F = 2 ^ n)
variable (K : Subgroup H) [K.Normal] (e : K ≃* PSL(3,F)) (T : Sylow 2 H)

include hn hF in
/-- The actual Sylow intersection can be marked by an inner adjustment of the
supplied model. -/
theorem exists_alignment : ∃ g : PSL(3,F),
    (T : Subgroup H).comap (modelEmbedding F K (e.trans (MulAut.conj g))) =
      unipotent F := by
  obtain ⟨P,hP⟩ := T.exists_subgroupOf_eq_of_normal K
  let Q := P.mapSurjective (f := e.toMonoidHom) e.surjective
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq PSL(3,F) Q (unipotentSylow F hn hF)
  refine ⟨g, ?_⟩
  have hm := congrArg Sylow.toSubgroup hg
  change ((P : Subgroup K).map e.toMonoidHom).map (MulAut.conj g).toMonoidHom =
    unipotent F at hm
  rw [hP, Subgroup.map_map] at hm
  change ((T : Subgroup H).subgroupOf K).map (e.trans (MulAut.conj g)).toMonoidHom = _ at hm
  rw [← hm]
  change (((T : Subgroup H).comap K.subtype).comap
    (e.trans (MulAut.conj g)).symm.toMonoidHom) = _
  exact comap_equiv_eq_map_symm (e.trans (MulAut.conj g)).symm _

/-- E.2.2's linear-three diagram and Borel conclusions for the original H,K,T,M.
This includes the degree-one model; no unjustified lower-degree exclusion occurs. -/
theorem exists_diagram_and_borel (hgen : K ⊔ (T : Subgroup H) = ⊤)
    (hP : IsMinimalParabolicOver T ⊤) :
    ∃ g : PSL(3,F),
      let e' := e.trans (MulAut.conj g)
      (T : Subgroup H).comap (modelEmbedding F K e') = unipotent F ∧
      (∃ t ∈ (T : Subgroup H), diagramAction F hn hF (modelAction F K e' t) ≠ 1) ∧
      (minimalParabolicMax T hP).comap (modelEmbedding F K e') = borel F := by
  obtain ⟨g,hg⟩ := exists_alignment F hn hF K e T
  refine ⟨g,hg, ?_⟩
  exact diagram_and_borel F K _ hn hF (T : Subgroup H) (minimalParabolicMax T hP)
    hgen hg hP.1 ⟨(minimalParabolicMax_spec T hP).2,(minimalParabolicMax_spec T hP).1⟩

end CFSG.Quasithin.ChapterE.Structure.LinearThree
