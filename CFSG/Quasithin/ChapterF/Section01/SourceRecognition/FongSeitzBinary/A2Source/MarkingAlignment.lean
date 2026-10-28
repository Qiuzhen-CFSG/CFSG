module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.LinearThreePresentation
public import Theory.GroupTheory.SolvableSylowControl.Marked
public import Theory.SpecificGroups.PSL3.LinearThreeFlags.ParabolicResiduals

/-!
# Recovering the original A₂ markings after root generation

Sylow conjugacy changes the simultaneous root frame so that its positive
subgroup is the actual U. Normalizers recover the entire Borel. The two
distinct maximal Borel overgroups are exactly the point and line parabolics,
in either source orientation; hence the negative-root placements follow.
All six root parameters move through one equivalence. The whole-group
recognition used here is constructed from source geometry in RootGeneration,
and the source consumer in Recognition discharges that premise.

Source: DGS, Groups and Graphs, Theorem D, printed p.224; Sylow conjugacy
and the elementary SL₃ Borel-overgroup calculation. Fields of order two and
four are included.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Matrix.PSL3
open Theory.SpecificGroups.LinearHigher Matrix.PSL3.LinearThree Matrix.PSL3.RootPresentationRecognition
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.A2Source.MarkingAlignment
variable {X F : Type*} [Group X] [Field F] [Finite F] [CharP F 2]
  {P : Fin 2 → Subgroup X} (Q : MarkedQuotient P) (split : SplitData Q.tits)

/-- Sylow conjugacy aligns the proved whole-group equivalence with the actual U. -/
theorem exists_unipotent_aligned (e : (X ⧸ Q.D) ≃* PSL(3,F)) :
    ∃ (g : PSL(3,F)) (e' : (X ⧸ Q.D) ≃* PSL(3,F)), e' = e.trans (MulAut.conj g) ∧
      split.U.map e'.toMonoidHom = unipotent F := by
  let := Fintype.ofFinite F
  obtain ⟨n,_,hn⟩ := FiniteField.card F 2
  have hF : Nat.card F = 2^(n : ℕ) := by simpa only [Nat.card_eq_fintype_card] using hn
  exact SolvableSylowControl.exists_aligned_equiv e split.sylow (unipotentSylow F n.property hF)

/-- The full Borel follows from its original normalizer equation. -/
theorem map_borel (e : (X ⧸ Q.D) ≃* PSL(3,F))
    (hU : split.U.map e.toMonoidHom = unipotent F) :
    Q.tits.B.map e.toMonoidHom = Matrix.PSL3.LinearThree.borel F := by
  rw [←split.normalizer_eq,map_normalizer_eq_of_bijective _ e.bijective,hU,
    normalizer_unipotent_of_charTwo]

omit [CharP F 2] in
/-- Both full endpoint images are determined together, with the actual orientation retained. -/
theorem exists_point_index (e : (X ⧸ Q.D) ≃* PSL(3,F))
    (hB : Q.tits.B.map e.toMonoidHom = Matrix.PSL3.LinearThree.borel F) :
    ∃ i : Fin 2,
      (Q.tits.standardParabolic {Q.simple i}).map e.toMonoidHom = pointParabolic F ∧
      (Q.tits.standardParabolic {Q.simple (1-i)}).map e.toMonoidHom = lineParabolic F := by
  have hn : Q.tits.standardParabolic {Q.simple 0} ≠ Q.tits.standardParabolic {Q.simple 1} := by
    intro he
    have hs := (Q.tits.standardParabolic_eq_iff
      (Set.singleton_subset_iff.mpr (Q.simple_mem 0))
      (Set.singleton_subset_iff.mpr (Q.simple_mem 1))).mp he
    exact (by decide : (0 : Fin 2) ≠ 1) (Q.simple_injective (Set.singleton_injective hs))
  have hn' : (Q.tits.standardParabolic {Q.simple 0}).map e.toMonoidHom ≠
      (Q.tits.standardParabolic {Q.simple 1}).map e.toMonoidHom :=
    fun he => hn (map_injective e.injective he)
  have hc (i : Fin 2) := ParabolicResiduals.coatom_over_borel F
    ((Q.tits.standardParabolic {Q.simple i}).map e.toMonoidHom)
    (hB ▸ map_mono (Q.tits.B_le_standardParabolic {Q.simple i}))
    ((OrderIso.isCoatom_iff e.mapSubgroup _).mpr (Q.parabolic_isCoatom i))
  rcases hc 0 with h0 | h0 <;> rcases hc 1 with h1 | h1
  · exact (hn' (h0.trans h1.symm)).elim
  · exact ⟨0,h0,by simpa using h1⟩
  · exact ⟨1,h1,by simpa using h0⟩
  · exact (hn' (h0.trans h1.symm)).elim

/-- The new frame pulls every root parameter back through the same equivalence. -/
def alignedRoot (e : (X ⧸ Q.D) ≃* PSL(3,F)) (r : Root 3) (a : F) : X ⧸ Q.D :=
  e.symm (projectiveRoot r a)

omit [Finite F] [CharP F 2] in
@[simp] theorem alignedRoot_apply (e : (X ⧸ Q.D) ≃* PSL(3,F)) (r : Root 3) (a : F) :
    e (alignedRoot Q e r a) = projectiveRoot r a := e.apply_symm_apply _

omit [Finite F] [CharP F 2] in
theorem alignedRoot_relations (e : (X ⧸ Q.D) ≃* PSL(3,F)) :
    Relations (alignedRoot Q e) := projectiveRoot_relations.map e.symm.toMonoidHom

omit [Finite F] [CharP F 2] in
/-- Elementary generation is preserved by this simultaneous frame change. -/
theorem alignedRoot_generate (e : (X ⧸ Q.D) ≃* PSL(3,F)) :
    closure {g | ∃ r a, g = alignedRoot Q e r a} = ⊤ := by
  apply top_unique
  intro g _
  obtain ⟨A,hA⟩ := projection_surjective F (e g)
  have he : g = e.symm (projection F A) := by rw [hA,e.symm_apply_apply]
  rw [he]
  apply Atlas.sl_elementary_induction
    (fun A : SL(3,F) => e.symm (projection F A) ∈
      closure {g | ∃ r a, g = alignedRoot Q e r a}) _
    (fun A B hA hB => by rw [map_mul,map_mul]; exact mul_mem hA hB) A
  intro i j hij a
  exact subset_closure ⟨root i j hij,a,rfl⟩

omit [Finite F] [CharP F 2] in
/-- The positive subgroup is the literal source U after Sylow alignment. -/
theorem alignedRoot_positive (e : (X ⧸ Q.D) ≃* PSL(3,F))
    (hU : split.U.map e.toMonoidHom = unipotent F) :
    positiveClosure (alignedRoot Q e) = split.U := by
  apply map_injective (f := e.toMonoidHom) e.injective
  rw [hU]
  exact map_positiveClosure e (alignedRoot_apply Q e)

/-- Negative-root placements are recovered from the actual full endpoint images. -/
def rootData (e : (X ⧸ Q.D) ≃* PSL(3,F))
    (hU : split.U.map e.toMonoidHom = unipotent F) (i : Fin 2)
    (hp : (Q.tits.standardParabolic {Q.simple i}).map e.toMonoidHom = pointParabolic F)
    (hl : (Q.tits.standardParabolic {Q.simple (1-i)}).map e.toMonoidHom = lineParabolic F) :
    RootData Q split F i where
  x := alignedRoot Q e
  relations := alignedRoot_relations Q e
  generate := alignedRoot_generate Q e
  positive := alignedRoot_positive Q split e hU
  negative_point := by
    apply (mem_map_iff_mem (f := e.toMonoidHom) e.injective).mp
    rw [hp]
    change e (alignedRoot Q e (root 2 1 (by decide)) 1) ∈ pointParabolic F
    rw [alignedRoot_apply]
    apply mem_map_of_mem (projection F)
    rw [mem_pointParabolicSL_iff]
    simp [matrixRoot,root,Matrix.SpecialLinearGroup.transvection_coe]
  negative_line := by
    apply (mem_map_iff_mem (f := e.toMonoidHom) e.injective).mp
    rw [hl]
    change e (alignedRoot Q e (root 1 0 (by decide)) 1) ∈ lineParabolic F
    rw [alignedRoot_apply]
    apply mem_map_of_mem (projection F)
    rw [mem_lineParabolicSL_iff]
    simp [matrixRoot,root,Matrix.SpecialLinearGroup.transvection_coe]

/-- A proved whole-group recognition supplies every field of the accepted marked root data.
No endpoint, positive-subgroup or negative-placement premise remains. -/
theorem exists_rootData (e : (X ⧸ Q.D) ≃* PSL(3,F)) :
    ∃ i : Fin 2, Nonempty (RootData Q split F i) := by
  obtain ⟨g,e',_,hU⟩ := exists_unipotent_aligned Q split e
  obtain ⟨i,hp,hl⟩ := exists_point_index Q e' (map_borel Q split e' hU)
  exact ⟨i,⟨rootData Q split e' hU i hp hl⟩⟩

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.A2Source.MarkingAlignment
