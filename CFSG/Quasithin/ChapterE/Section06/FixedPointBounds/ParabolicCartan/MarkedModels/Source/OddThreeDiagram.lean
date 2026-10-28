module
public import CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels.Source.OddThree
public import Theory.SpecificGroups.PSL3.LinearThreeOuterExtensions.Diagram.ParabolicSeparation
import all CFSG.Quasithin.ChapterB.Section06To07.Structure
/-!
# The original odd-linear diagram actor

The original Sylow supplies a genuine graph actor in the faithful full
PSL₃ graph extension. Restrict that same extension isomorphism to the
simple component and identify its inner subgroup with the projective
matrix group. Conjugation then agrees with the actual normalizer action
in the source automizer. Inverse transpose moves the point-parabolic
conjugacy class, since point and plane stabilizers are not inner-conjugate.

This constructs the entire odd-linear rank-three model row, with the
original maximal overlap and quotient maps. No diagram witness or
parabolic-separation premise remains. Source: Aschbacher–Smith E.2.2(2d),
printed pp.215–216.
-/

public section
open Subgroup Theory.GroupTheory
open scoped Pointwise MatrixGroups
namespace CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels
open Matrix Matrix.PSL3 Matrix.PSL3.OuterSolvable
open Matrix.PSL3.OddPrimeGraphExtension
open Matrix.PSL3.OddPrimeGraphExtension.GraphLargeStructure
open Matrix.PSL3.LinearThree.OuterExtensions
open CFSG.Quasithin.ChapterE
variable {H : Type*} [Group H] [Finite H]

omit [Finite H] in
private theorem conj_transport {X Y : Type*} [Group X] [Group Y] (e:X≃*Y)
    (K:Subgroup X) [K.Normal] (L:Subgroup Y) [L.Normal]
    (h:K.map e.toMonoidHom=L) (x:X) :
    MulAut.congr ((e.subgroupMap K).trans (MulEquiv.subgroupCongr h))
      (MulAut.conjNormal x) = MulAut.conjNormal (e x) := by
  ext y
  change e ((MulAut.conjNormal x
    (((e.subgroupMap K).trans (MulEquiv.subgroupCongr h)).symm y):K):X) = _
  simp only [MulAut.conjNormal_apply, map_mul, map_inv]
  have hy : e ((((e.subgroupMap K).trans (MulEquiv.subgroupCongr h)).symm y : K) : X) = y :=
    congrArg Subtype.val (((e.subgroupMap K).trans (MulEquiv.subgroupCongr h)).apply_symm_apply y)
  rw [hy]

/-- The same actual Sylow actor moves the marked projective diagram. -/
theorem source_odd_linear_diagram (T : Sylow 2 H)
    (hP : ChapterB.IsMinimalParabolicOver T ⊤) (hs : ¬ Group.IsSolvable H)
    (K : Subgroup H) (hK : K.IsCComponent) [K.Normal]
    (hgen : K ⊔ (T : Subgroup H) = ⊤) {p : ℕ} (hp : p.Prime) (ho : Odd p)
    (hm : ClassicalGroup.IsPSL (sourceImage (ChapterB.minimalParabolicMax T hP) K) 3 p) :
    p%4=3 ∧ ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = p ∧
      ∃ e : sourceImage (ChapterB.minimalParabolicMax T hP) K ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 3) F,
        MovesDiagram (ChapterB.minimalParabolicMax T hP) K (T : Subgroup H) e
          (Matrix.PSL3.LinearThree.pointParabolic F)
          (Matrix.PSL3.LinearThree.lineParabolic F) := by
  let M := ChapterB.minimalParabolicMax T hP
  let J := sourceKernel M
  let S := T.mapSurjective (QuotientGroup.mk'_surjective J)
  have hi := Structure.source_normal_simple_image T hP hs K hK hgen
  let D := sourceImage M K
  let : IsSimpleGroup D := hi.1
  have hmin := (Structure.source_star_minimal_core_free T hP).1
  have hcore : pCore 2 (H ⧸ J) = ⊥ := by
    exact bot_unique ((ChapterB.minimalParabolicTwoCore_le_core S hmin).trans
      (Structure.source_star_minimal_core_free T hP).2.le)
  rcases hm with ⟨F, hF, hfin, hcard, ⟨e⟩⟩
  let : Field F := hF
  let : Finite F := hfin
  let : D.Normal := hi.2.2.1
  have hg := Structure.OddDegreeThree.linear_graph_actor S hmin D hi.2.2.2 hcore hp ho hcard e
  rcases hg with ⟨f,hf,t,g,hact,hout⟩
  let : IsSimpleGroup (sourceImage M K) := hi.1
  let : IsSimpleGroup PSL(3,F) := e.symm.isSimpleGroup
  have hnorm : (t:H ⧸ J) ∈ normalizer (D : Set _) := by
    rw [normalizer_eq_top]
    trivial
  have htS : (t:H ⧸ J) ∈ S := t.property
  have htT : (t:H ⧸ J) ∈ sourceImage M (T : Subgroup H) := by
    exact htS
  have htK : (t:H ⧸ J) ∈ normalizer (sourceImage M K : Set _) := by
    exact hnorm
  let z : (sourceImage M (T : Subgroup H)).subgroupOf
      (normalizer (sourceImage M K : Set _)) := ⟨⟨t,htK⟩,htT⟩
  let a0 : sourceAutomizer M K (T : Subgroup H) :=
    ⟨(sourceImage M K).normalizerMonoidHom z, ⟨z,z.property,rfl⟩⟩
  let ef : D ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 3) F :=
    ((f.subgroupMap D).trans (MulEquiv.subgroupCongr hf)).trans
      (innerPartEquiv F).symm
  have hact' : MulAut.congr ef a0.val = (MulAut.conj g * Matrix.PSL3.OuterSolvable.graph F) := by
    have hh := innerPart_conj_action F (f (t:H ⧸ J))
    rw [←conj_transport f D (innerPart F) hf (t:H ⧸ J)] at hh
    have heq : MulAut.congr ef (MulAut.conjNormal (H:=D) (t:H ⧸ J)) = (f (t:H ⧸ J)).val := by
      convert hh using 1
      ext x
      rfl
    change MulAut.congr ef (MulAut.conjNormal (H:=D) (t:H ⧸ J)) = _
    exact heq.trans hact
  have hmoves : ¬ (PreservesParabolicClass (MulAut.congr ef a0.val)
      (Matrix.PSL3.LinearThree.pointParabolic F) ∧
      PreservesParabolicClass (MulAut.congr ef a0.val)
      (Matrix.PSL3.LinearThree.lineParabolic F)) := by
    rw [hact']
    intro hh
    exact ParabolicSeparation.not_preservesPointType_inner_graph F g hh.1
  refine ⟨?_, F, hF, hfin, hcard, ef, ?_⟩
  · exact (Structure.OddDegreeThree.linear S hmin D hi.2.2.2 hcore hp ho ⟨F,hF,hfin,hcard,⟨e⟩⟩ |>.1)
  exact ⟨a0,a0.property,hmoves⟩
/-- The complete odd-linear rank-three row on the same original star component. -/
theorem source_odd_linear_model (T : Sylow 2 H)
    (hP : ChapterB.IsMinimalParabolicOver T ⊤) (hs : ¬ Group.IsSolvable H)
    (K : Subgroup H) (hK : K.IsCComponent) [K.Normal]
    (hgen : K ⊔ (T : Subgroup H) = ⊤) {p : ℕ} (hp : p.Prime) (ho : Odd p)
    (hm : ClassicalGroup.IsPSL (sourceImage (ChapterB.minimalParabolicMax T hP) K) 3 p) :
    SingleOddRankThreeModel (ChapterB.minimalParabolicMax T hP) K (T : Subgroup H) := by
  have hc := source_odd_linear_centralizer T hP hs K hK hgen hp ho hm
  have hd := source_odd_linear_diagram T hP hs K hK hgen hp ho hm
  exact ⟨p,hp,ho,hc.2,Or.inr hd⟩

end CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels
