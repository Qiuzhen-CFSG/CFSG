module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Flags.RankOne.Triple.BinaryAuxiliary.Structure.Moving.Geometry.ReverseIndex.Contained.Nonquadratic.Model
public import Theory.SpecificGroups.PSL3Two.Parabolics.MarkedProduct
/-!
# A fixed simultaneous affine marking

The line parabolic acts on the four affine vectors (x,y,1). Label them by
x + 2y. The incident point core then gives the two disjoint transpositions,
while the line core gives the translations, or double transpositions.
Faithfulness follows from the images of three affine points; order 24 gives
surjectivity. Four-element subgroup orders certify the exact core images.

The affine action is adapted from
`Theory.SpecificGroups.PSL3Two.Parabolics.MarkedAutomorphisms.SymmetricModels`.
Source: Meierfrankenfeld--Stellmacher (1993), local flag setup, pp.905--907.
-/

public section
open Matrix Subgroup Matrix.PSL3Two Matrix.PSL3Two.MarkedAutomorphisms
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Flags.RankOne.BinaryAuxiliary.Moving.Nonquadratic.MarkingConstruction
private abbrev Four := ZMod 2 × ZMod 2
private def affineVec (x : Four) : Fin 3 → ZMod 2 := ![x.1,x.2,1]
private def firstTwo (v : Fin 3 → ZMod 2) : Four := (v 0, v 1)
private def affineAct (g : SL) (x : Four) : Four :=
  firstTwo (g.val.mulVec (affineVec x))

private theorem line_last_entry (g : SL) (hg : g ∈ lineParabolicSL) : g.val 2 2 = 1 := by
  obtain ⟨h20, h21⟩ := (mem_lineParabolicSL_iff g).mp hg
  have hd := g.property
  rw [det_fin_three] at hd
  have hz : g.val 2 2 ≠ 0 := by
    intro h
    simp [h20, h21, h] at hd
  exact (by decide : ∀ a : ZMod 2, a ≠ 0 → a = 1) _ hz

private theorem affineVec_act (g : SL) (hg : g ∈ lineParabolicSL) (x : Four) :
    affineVec (affineAct g x) = g.val.mulVec (affineVec x) := by
  have h := (mem_lineParabolicSL_iff g).mp hg
  funext i
  fin_cases i
  · rfl
  · rfl
  · simp [affineVec, mulVec, dotProduct, Fin.sum_univ_three, h.1, h.2, line_last_entry g hg]

private theorem affineAct_mul (g h : SL) (hh : h ∈ lineParabolicSL) (x : Four) :
    affineAct (g * h) x = affineAct g (affineAct h x) := by
  have he : (g * h).val.mulVec (affineVec x) =
      g.val.mulVec (affineVec (affineAct h x)) := by
    rw [affineVec_act h hh, mulVec_mulVec]
    rfl
  exact congrArg firstTwo he

private theorem affineAct_one (x : Four) : affineAct 1 x = x := by
  simp [affineAct, firstTwo, affineVec]

private def linePerm (g : lineParabolicSL) : Equiv.Perm Four where
  toFun := affineAct g
  invFun := affineAct (g : SL)⁻¹
  left_inv x := by
    rw [← affineAct_mul _ _ g.property, inv_mul_cancel, affineAct_one]
  right_inv x := by
    rw [← affineAct_mul _ _ (lineParabolicSL.inv_mem g.property),
      mul_inv_cancel, affineAct_one]

private def linePermHom : lineParabolicSL →* Equiv.Perm Four where
  toFun := linePerm
  map_one' := by
    apply Equiv.ext
    intro x
    exact affineAct_one x
  map_mul' g h := by
    apply Equiv.ext
    intro x
    exact affineAct_mul g h h.property x

private theorem affine_faithful (g : SL) (hg : g ∈ lineParabolicSL)
    (h0 : affineAct g (0,0) = (0,0)) (h1 : affineAct g (1,0) = (1,0))
    (h2 : affineAct g (0,1) = (0,1)) : g = 1 := by
  obtain ⟨h20, h21⟩ := (mem_lineParabolicSL_iff g).mp hg
  have h22 := line_last_entry g hg
  simp [affineAct, firstTwo, affineVec, mulVec, dotProduct, Fin.sum_univ_three,
    Prod.mk.injEq] at h0 h1 h2
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp_all

private theorem linePermHom_injective : Function.Injective linePermHom := by
  apply (MonoidHom.ker_eq_bot_iff linePermHom).mp
  apply le_bot_iff.mp
  intro g hg
  apply Subtype.ext
  apply affine_faithful g g.property
  · exact Equiv.congr_fun hg (0,0)
  · exact Equiv.congr_fun hg (1,0)
  · exact Equiv.congr_fun hg (0,1)

private noncomputable def lineEquivPerm : lineParabolicSL ≃* Equiv.Perm Four :=
  MulEquiv.ofBijective linePermHom
    ((Nat.bijective_iff_injective_and_card linePermHom).mpr ⟨linePermHom_injective, by
      rw [card_lineParabolicSL, Nat.card_eq_fintype_card, Fintype.card_perm]
      norm_num [Four, Nat.factorial]⟩)

open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Flags.RankOne.BinaryAuxiliary.Moving.Nonquadratic

private def label : Four ≃ Fin 4 := (Equiv.prodComm _ _).trans finProdFinEquiv
/-- The faithful affine action with the fixed labeling (x,y) ↦ x + 2y. -/
noncomputable def lineMarking : lineParabolicSL ≃* S4Model.Actor :=
  lineEquivPerm.trans (Equiv.permCongrHom label)

private theorem lineMarking_apply (g : lineParabolicSL) (x : Fin 4) :
    lineMarking g x = label (affineAct g (label.symm x)) := rfl

private def s0 : lineParabolicSL := ⟨(⟨!![1,1,1; 0,1,0; 0,0,1], by decide⟩ : SL), by
  apply (mem_lineParabolicSL_iff _).mpr; exact ⟨rfl,rfl⟩⟩
private def s1 : lineParabolicSL := ⟨(⟨!![1,1,0; 0,1,0; 0,0,1], by decide⟩ : SL), by
  apply (mem_lineParabolicSL_iff _).mpr; exact ⟨rfl,rfl⟩⟩
private def tx : lineParabolicSL := ⟨(⟨!![1,0,1; 0,1,0; 0,0,1], by decide⟩ : SL), by
  apply (mem_lineParabolicSL_iff _).mpr; exact ⟨rfl,rfl⟩⟩
private def ty : lineParabolicSL := ⟨(⟨!![1,0,0; 0,1,1; 0,0,1], by decide⟩ : SL), by
  apply (mem_lineParabolicSL_iff _).mpr; exact ⟨rfl,rfl⟩⟩

private theorem s0_image : lineMarking s0 = Equiv.swap 0 1 := by
  ext x
  rw [lineMarking_apply]
  revert x
  decide +kernel
private theorem s1_image : lineMarking s1 = Equiv.swap 2 3 := by
  ext x
  rw [lineMarking_apply]
  revert x
  decide +kernel
private theorem tx_image : lineMarking tx = Equiv.swap 0 1 * Equiv.swap 2 3 := by
  ext x
  rw [lineMarking_apply]
  revert x
  decide +kernel
private theorem ty_image : lineMarking ty = Equiv.swap 0 2 * Equiv.swap 1 3 := by
  ext x
  rw [lineMarking_apply]
  revert x
  decide +kernel

private theorem closure_eq_of_card_four (H : Subgroup S4Model.Actor) (a b : S4Model.Actor)
    (ha : a ∈ H) (hb : b ∈ H) (hcard : Nat.card H = 4)
    (hinj : Function.Injective (![1,a,b,a*b] : Fin 4 → S4Model.Actor)) :
    closure {a,b} = H := by
  have hle : closure {a,b} ≤ H := by
    rw [closure_le, Set.insert_subset_iff, Set.singleton_subset_iff]
    exact ⟨ha,hb⟩
  have ha' : a ∈ closure ({a,b} : Set S4Model.Actor) := subset_closure (by simp)
  have hb' : b ∈ closure ({a,b} : Set S4Model.Actor) := subset_closure (by simp)
  let f : Fin 4 → closure ({a,b} : Set S4Model.Actor) := fun j =>
    ⟨(![1,a,b,a*b] : Fin 4 → S4Model.Actor) j, by
      fin_cases j
      · exact one_mem _
      · exact ha'
      · exact hb'
      · exact mul_mem ha' hb'⟩
  have hc := Nat.card_le_card_of_injective f (fun x y h => hinj (congrArg Subtype.val h))
  apply eq_of_le_of_card_ge hle
  simpa only [Nat.card_fin, hcard] using hc

/-- The point translations preserve the incident standard line. -/
theorem pointV_le_line : pointV ≤ lineParabolicSL := by
  intro g hg
  rw [mem_lineParabolicSL_iff]
  exact ⟨hg.2.2.1, hg.2.2.2.2.2.1⟩

/-- The diagram involution identifies the literal line core with its intrinsic two-core. -/
theorem line_core : lineParabolicSL.pCoreIn 2 = lineV := by
  have h := map_pCoreIn_of_injective 2 pointParabolicSL diagram.toMonoidHom diagram.injective
  rw [MarkedProduct.pointParabolic_core, pointV_map_diagram, pointParabolic_map_diagram] at h
  exact h.symm

private theorem card_lineV : Nat.card lineV = 4 := by
  rw [← pointV_map_diagram, ← Nat.card_congr (pointV.equivMapOfInjective diagram.toMonoidHom diagram.injective).toEquiv]
  exact card_pointV

private theorem card_image (C : Subgroup SL) (hC : C ≤ lineParabolicSL)
    (hc : Nat.card C = 4) :
    Nat.card ((C.subgroupOf lineParabolicSL).map lineMarking.toMonoidHom) = 4 := by
  rw [← Nat.card_congr ((C.subgroupOf lineParabolicSL).equivMapOfInjective
    lineMarking.toMonoidHom lineMarking.injective).toEquiv,
    Nat.card_congr (subgroupOfEquivOfLe hC).toEquiv, hc]

/-- The incident point core maps to the two disjoint transpositions. -/
theorem point_image :
    (pointV.subgroupOf lineParabolicSL).map lineMarking.toMonoidHom = S4Model.firstCore := by
  symm
  apply closure_eq_of_card_four
  · exact ⟨s0, by change (s0 : SL) ∈ pointV; decide +kernel, s0_image⟩
  · exact ⟨s1, by change (s1 : SL) ∈ pointV; decide +kernel, s1_image⟩
  · exact card_image pointV pointV_le_line card_pointV
  · decide +kernel

/-- The actor’s line core maps to the normal four-group of double transpositions. -/
theorem line_image :
    (lineV.subgroupOf lineParabolicSL).map lineMarking.toMonoidHom = S4Model.oppositeCore := by
  symm
  apply closure_eq_of_card_four
  · exact ⟨tx, by change (tx : SL) ∈ lineV; decide +kernel, tx_image⟩
  · exact ⟨ty, by change (ty : SL) ∈ lineV; decide +kernel, ty_image⟩
  · apply card_image lineV
    · rw [← line_core]; exact map_subtype_le _
    · exact card_lineV
  · decide +kernel

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Flags.RankOne.BinaryAuxiliary.Moving.Nonquadratic.MarkingConstruction
