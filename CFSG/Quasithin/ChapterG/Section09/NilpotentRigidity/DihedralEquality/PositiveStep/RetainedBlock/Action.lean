module

public import CFSG.Quasithin.ChapterG.Section09.NilpotentRigidity.DihedralEquality.PositiveStep.RetainedBlock.Invariance

/-!
# The faithful retained action and its degree

Since the retained actors fix the rotation-fixed complement, faithfulness
of the full action descends to the rotation-moved space. Its displacement
span is the entire moved space, both internally and in the ambient module.
The degree bound then forces every retained prime to be three in both of
the sharp dimension cases. This uses no complementary-fixation assumption.

Source: Aschbacher--Smith G.9.2, printed p.353.
-/

@[expose] public section

namespace CFSG.Quasithin.ChapterG.Section09.NilpotentRigidity.DihedralEquality.PositiveStep.RetainedBlock
open DihedralDegree DihedralGroup
universe v
variable {ι : Type} [Fintype ι] [DecidableEq ι] {p : ι → ℕ}
  {W : Type v} [AddCommGroup W] [Module (ZMod 2) W]
  (σ : Representation (ZMod 2) (∀ i, DihedralGroup (p i)) W) (i : ι)
  [FiniteDimensional (ZMod 2) W]

abbrev movedRep := σ.subrepresentation (rotationMoved (factorRep σ i)) (moved_stable σ i)

theorem retained_faithful
    (split : DihedralSplittingTheorem.{v})
    (centralizer : ClassifiedInvolutionCentralizerTheorem.{0,v})
    (hp : (p i).Prime) (ho : Odd (p i)) (hf : Function.Injective σ)
    {exceptional : Prop} (s : PreparedSplit σ i exceptional) :
    Function.Injective ((movedRep σ i).comp (subproductHom s.retainedIndices)) := by
  have hs := split W (p i) hp ho (factorRep σ i) (factorRep_injective σ hf i)
  exact faithful_subrepresentation_of_fixed_complement
    (σ.comp (subproductHom s.retainedIndices))
    (hf.comp (subproduct_injective s.retainedIndices))
    (fun g => moved_stable σ i _) hs.1.symm.sup_eq_top
    (retained_fixes_fixed σ i centralizer s)

theorem retained_moved_eq
    (split : DihedralSplittingTheorem.{v})
    (centralizer : ClassifiedInvolutionCentralizerTheorem.{0,v})
    (hp : (p i).Prime) (ho : Odd (p i)) (hf : Function.Injective σ)
    {exceptional : Prop} (s : PreparedSplit σ i exceptional) :
    movedSpace σ s.retainedGroup = rotationMoved (factorRep σ i) := by
  have hs := split W (p i) hp ho (factorRep σ i) (factorRep_injective σ hf i)
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨⟨g, w⟩, rfl⟩
    obtain ⟨a, ha⟩ := g.property
    obtain ⟨c, hc, m, hm, rfl⟩ := Submodule.mem_sup.mp
      (show w ∈ rotationFixed (factorRep σ i) ⊔ rotationMoved (factorRep σ i) by
        rw [hs.1.sup_eq_top]; trivial)
    have hC := retained_fixes_fixed σ i centralizer s a ⟨c, hc⟩
    change σ (subproductHom s.retainedIndices a) c = c at hC
    rw [ha] at hC
    change σ g (c + m) - (c + m) ∈ _
    have he : σ g (c + m) - (c + m) = σ g m - m := by rw [map_add, hC]; abel
    rw [he]
    exact (rotationMoved (factorRep σ i)).sub_mem (moved_stable σ i g hm) hm
  · apply Submodule.span_le.mpr
    rintro _ ⟨⟨g, w⟩, rfl⟩
    let a : s.retainedIndices := ⟨i, Finset.mem_insert_self _ _⟩
    have hg : Pi.mulSingle i g.val ∈ s.retainedGroup :=
      ⟨Pi.mulSingle a g.val, subproductHom_single s.retainedIndices a g.val⟩
    exact Representation.Coinvariants.sub_mem_ker (ρ := σ.comp s.retainedGroup.subtype)
      ⟨Pi.mulSingle i g.val, hg⟩ w

theorem retained_moved_top
    (split : DihedralSplittingTheorem.{v})
    (centralizer : ClassifiedInvolutionCentralizerTheorem.{0,v})
    (hp : (p i).Prime) (ho : Odd (p i)) (hf : Function.Injective σ)
    {exceptional : Prop} (s : PreparedSplit σ i exceptional) :
    movedSpace ((movedRep σ i).comp (subproductHom s.retainedIndices)) ⊤ = ⊤ := by
  have hs := split W (p i) hp ho (factorRep σ i) (factorRep_injective σ hf i)
  have hC (g : s.retainedGroup) (w : rotationFixed (factorRep σ i)) : σ g w = (w : W) := by
    obtain ⟨a, ha⟩ := g.property
    simpa only [ha] using retained_fixes_fixed σ i centralizer s a w
  have he := movedSpace_subrepresentation_map_of_fixed_complement σ (moved_stable σ i)
    hs.1.symm.sup_eq_top s.retainedGroup hC
  rw [retained_moved_eq σ i split centralizer hp ho hf s] at he
  have he' := movedSpace_map (movedRep σ i) (subproductHom s.retainedIndices) ⊤
  rw [← MonoidHom.range_eq_map] at he'
  change (movedSpace (movedRep σ i) (subproductHom s.retainedIndices).range).map
    (rotationMoved (factorRep σ i)).subtype = _ at he
  rw [he'] at he
  apply le_antisymm le_top
  intro w _
  have hw : (w : W) ∈ (movedSpace ((movedRep σ i).comp
      (subproductHom s.retainedIndices)) ⊤).map (rotationMoved (factorRep σ i)).subtype := by
    rw [he]
    exact w.property
  obtain ⟨v, hv, heq⟩ := hw
  exact (Subtype.ext heq : v = w) ▸ hv

theorem retained_cubic
    (split : DihedralSplittingTheorem.{v}) (bounds : DihedralDegreeTheorem.{v})
    (centralizer : ClassifiedInvolutionCentralizerTheorem.{0,v})
    (hp : ∀ j, (p j).Prime) (ho : ∀ j, Odd (p j)) (hf : Function.Injective σ)
    {exceptional : Prop} (s : PreparedSplit σ i exceptional) :
    ∀ j : s.retainedIndices, p j = 3 := by
  have hb := dihedralDegree_fintype bounds (fun j : s.retainedIndices => p j)
    (fun j => hp j) (fun j => ho j)
    ((movedRep σ i).comp (subproductHom s.retainedIndices))
    (retained_faithful σ i split centralizer (hp i) (ho i) hf s)
  have hcard : Fintype.card s.retainedIndices = s.actions.J.card + 1 := by
    change Fintype.card (insert i s.actions.J : Finset ι) = _
    rw [Fintype.card_coe, Finset.card_insert_of_notMem s.actions.excluded]
  intro j
  by_contra hj
  have hb' := hb.2.1 ⟨j, hj⟩
  rw [hcard] at hb'
  rcases s.small with ⟨hJ, hM⟩ | ⟨hJ, hM⟩ <;> omega

end CFSG.Quasithin.ChapterG.Section09.NilpotentRigidity.DihedralEquality.PositiveStep.RetainedBlock
