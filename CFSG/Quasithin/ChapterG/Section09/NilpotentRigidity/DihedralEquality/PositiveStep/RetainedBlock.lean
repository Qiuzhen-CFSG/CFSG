module

public import CFSG.Quasithin.ChapterG.Section09.NilpotentRigidity.DihedralEquality.PositiveStep.RetainedBlock.Classification
public import CFSG.Quasithin.ChapterG.Section09.NilpotentRigidity.DihedralEquality.SpaceTransport

/-!
# Completing the retained block in the equality induction

The retained product fixes the already classified rotation-fixed space,
so it acts faithfully on the rotation-moved space. Sharpness and the degree
bound leave a cubic plane or two cubic factors acting on an orthogonal
four-space. After constructing this genuine ordinary block, the classified
centralizer input forces every complementary actor to fix it pointwise.
The displacement span is identified with the actual rotation-moved space.

This is a conditional producer of `BlockClassificationTheorem`: the splitting,
degree, orthogonal-pair, and classified-centralizer theorems remain explicit
inputs for the source-theorem assembly owner.

Source: Aschbacher--Smith G.9.2, printed pp.351--353, especially the retained
factors on p.353.
-/

public section

namespace CFSG.Quasithin.ChapterG.Section09.NilpotentRigidity.DihedralEquality.PositiveStep
open DihedralDegree RetainedBlock
universe v

/-- Classify the genuine retained plane or orthogonal four-space and prove
pointwise fixation by the complementary product. All four earlier inputs
remain explicit; in particular no centralizer producer is assumed proved. -/
theorem blockClassification_of_inputs
    (split : DihedralSplittingTheorem.{v}) (bounds : DihedralDegreeTheorem.{v})
    (pair : OrthogonalPairTheorem.{v})
    (centralizer : ClassifiedInvolutionCentralizerTheorem.{0,v}) :
    BlockClassificationTheorem.{v} := by
  intro ι _ _ p hp ho W _ _ _ σ hf i exceptional s
  let M := rotationMoved (factorRep σ i)
  let C := rotationFixed (factorRep σ i)
  let R := s.retainedIndices
  let I := s.fixedIndices
  let μ := movedRep σ i
  let τ := μ.comp (subproductHom R)
  have hs := split W (p i) (hp i) (ho i) (factorRep σ i) (factorRep_injective σ hf i)
  have hfaith := retained_faithful σ i split centralizer (hp i) (ho i) hf s
  have hm := retained_moved_top σ i split centralizer (hp i) (ho i) hf s
  have hOrd := ordinary_retained σ i split bounds pair centralizer hp ho hf s
  let d : ClassifiedDecomposition τ ⊤ False :=
    { count := 1
      internal := singletonInternal τ hm
      exceptional_factor := False.elim
      ordinary_factor := fun _ _ => hOrd }
  have hC (g : s.retainedGroup) (w : C) : σ g w = (w : W) := by
    obtain ⟨a, ha⟩ := g.property
    simpa only [ha] using retained_fixes_fixed σ i centralizer s a w
  have hOrdM : IsOrdinaryFactor μ s.retainedGroup := by
    change IsOrdinaryFactor μ (subproductHom R).range
    simpa only [← MonoidHom.range_eq_map] using
      isOrdinaryFactor_map μ (subproductHom R) (subproduct_injective R) ⊤ hOrd
  refine ⟨?_, retained_moved_eq σ i split centralizer (hp i) (ho i) hf s,
    isOrdinaryFactor_of_subrepresentation σ (moved_stable σ i)
      hs.1.symm.sup_eq_top s.retainedGroup hC hOrdM⟩
  intro g w
  let ν := μ.comp (subproductHom I)
  have hk : g ∈ ν.ker := by
    apply Subgroup.pi_mem_of_mulSingle_mem
    intro j
    have hjI := Finset.mem_sdiff.mp j.property
    have hjR : j.val ∉ R := by
      intro hj
      rcases Finset.mem_insert.mp hj with hj | hj
      · exact (Finset.mem_erase.mp hjI.1).1 hj
      · exact hjI.2 hj
    let υ := μ.comp (MonoidHom.mulSingle (fun j => DihedralGroup (p j)) j.val)
    have hc : ∀ x (g : (⊤ : Subgroup (∀ j : R, DihedralGroup (p j)))),
        Commute (υ x) (τ g) := by
      intro x g
      exact ((subproduct_commutes R j.val hjR g.val x).map μ).symm
    have hh := dihedral_fixes_classified centralizer τ ⊤ False d
      (hfaith.comp Subtype.val_injective) υ hc (g j)
    change μ (Pi.mulSingle j.val (g j)) = 1 at hh
    change ν (Pi.mulSingle j (g j)) = 1
    simpa only [ν, MonoidHom.comp_apply, subproductHom_single] using hh
  exact congrArg Subtype.val (congrArg (fun f : Module.End (ZMod 2) M => f w) hk)

end CFSG.Quasithin.ChapterG.Section09.NilpotentRigidity.DihedralEquality.PositiveStep
