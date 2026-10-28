module
public import CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels.Source.OddTwo
public import CFSG.Quasithin.ChapterE.Section02.Structure.LinearThree.Source
import all CFSG.Quasithin.ChapterB.Section06To07.Structure
/-!
# The original linear-three Borel and diagram marking

Pass to the literal maximal-core quotient, align the normal component's
Sylow subgroup with the standard unipotent group, and apply the actual
minimal-parabolic diagram theorem. The same equivalence identifies the
original maximal overlap with the Borel and carries an actual Sylow actor
to an automorphism moving a parabolic conjugacy class. This includes the
field-two case and makes no generation-parameter assertion.

Source: Aschbacher–Smith E.2.2(2b), printed pp.215–216.
-/

public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
open Matrix.PSL3.LinearThree Matrix.PSL3.LinearThree.OuterExtensions
open Matrix.PSL3Even.MinimalParabolicWitness
namespace CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels
variable {H : Type*} [Group H] [Finite H]
theorem source_binary_linear_three_model (T:Sylow 2 H)
    (hP:ChapterB.IsMinimalParabolicOver T ⊤) (hs:¬Group.IsSolvable H)
    (K:Subgroup H) (hK:K.IsCComponent) [K.Normal]
    (hgen:K⊔(T:Subgroup H)=⊤) {n:ℕ} (hn:0<n)
    (hm:ClassicalGroup.IsPSL (sourceImage (ChapterB.minimalParabolicMax T hP) K) 3 (2^n)) :
    DiagramModel (ChapterB.minimalParabolicMax T hP) K (T:Subgroup H) n := by
  let M := ChapterB.minimalParabolicMax T hP
  let J := sourceKernel M
  let q := QuotientGroup.mk' J
  let S := T.mapSurjective (QuotientGroup.mk'_surjective J)
  let D := sourceImage M K
  have hi := Structure.source_normal_simple_image T hP hs K hK hgen
  let : D.Normal := hi.2.2.1
  have hmin := (Structure.source_star_minimal_core_free T hP).1
  have hmax : ChapterB.minimalParabolicMax S hmin = M.map q :=
    (ChapterB.minimalParabolicMax_map_core T hP q (QuotientGroup.mk'_surjective J)
      (by rw [QuotientGroup.ker_mk'];exact le_rfl)).symm
  obtain ⟨F,hF,hfin,hcard,⟨e⟩⟩ := hm
  let : Fintype F := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow (p:=2) (f:=n)
    (by simpa only [Nat.card_eq_fintype_card] using hcard)
  obtain ⟨g,_,⟨t,ht,ha⟩,hB⟩ := Structure.LinearThree.exists_diagram_and_borel
    F hn hcard D e S hi.2.2.2 hmin
  let e' := e.trans (MulAut.conj g)
  refine Or.inl ⟨F,hF,hfin,inferInstance,hn,hcard,e',?_,?_⟩
  · rw [source_overlap_coordinate]
    change ((M.map q).subgroupOf D).map e'.toMonoidHom = borel F
    rw [←hB,hmax]
    exact (comap_equiv_eq_map_symm e'.symm _).symm
  · refine ⟨MulAut.conjNormal t,?_,?_⟩
    · rw [sourceAutomizer_eq_map_conjNormal]
      exact mem_map_of_mem _ ht
    · intro hp
      have hd : modelAction F D e' t ∈ diagramTrivial F :=
        (mem_diagramTrivial_iff F _).mpr hp
      have hk : modelAction F D e' t ∈ (diagramAction F hn hcard).ker := by
        rwa [diagramAction_ker]
      exact ha hk
end CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels
