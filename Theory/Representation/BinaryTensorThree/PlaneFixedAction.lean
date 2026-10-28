module
public import Theory.Representation.BinaryTensorThree.PlaneFixed
public import Theory.GroupTheory.PCoreSurjective
public import Theory.SpecificGroups.SymmetricFourSolvable
public import Theory.SpecificGroups.PSL3Two.Parabolics.LineCore

/-!
# The plane parabolic on its fixed four-space

Restrict the original tensor action to the four-space fixed by the paired
plane radicals. The intrinsic two-core of the plane parabolic acts trivially.
The faithful elementary nine on this space exhausts the parabolic's odd part,
so the action kernel is a two-group. Core lifting therefore makes the actual
faithful action image two-core-free; it is solvable as an image of S₄ wr C₂.

The Chapter 10 weak-closure consumer uses this action image to show that every
corank-one conjugate subgroup fixes this exact four-space. Neither the full
Sylow subgroup nor the original plane parabolic is asserted to fix it.
Source: Aschbacher--Smith H.4.11(2), 8.3.3 and 8.3.9, printed pp.384,723,725.
-/

public noncomputable section
open Subgroup
namespace BinaryTensorThree.PlaneFixed
open Matrix.PSL3Two
abbrev Line := WreathPair.line

/-- Restriction of the literal paired tensor action to the radical fixed four-space. -/
@[expose] def lineAction : Representation (ZMod 2) Line square where
  toFun a :=
    { toFun X := ⟨action (PointParabolic.tensorHom a.val) X.val,
        line_preserves_square a.val a.property X.val X.property⟩
      map_add' X Y := Subtype.ext (map_add _ _ _)
      map_smul' c X := Subtype.ext (map_smul _ _ _) }
  map_one' := by apply LinearMap.ext; intro X; apply Subtype.ext; exact LinearMap.congr_fun (map_one (action.comp PointParabolic.tensorHom)) X.val
  map_mul' a b := by apply LinearMap.ext; intro X; apply Subtype.ext; exact LinearMap.congr_fun (map_mul (action.comp PointParabolic.tensorHom) a.val b.val) X.val

private abbrev P := lineParabolicSL
private abbrev Q := P ⧸ pCore 2 P
private abbrev WQ := RegularWreathProduct Q WreathPair.Bit
private def pairQuotient : Line →* WQ where
  toFun x := ⟨fun i => QuotientGroup.mk' _ ⟨x.val.left i,x.property i⟩,x.val.right⟩
  map_one' := by
    apply RegularWreathProduct.ext
    · funext i
      exact (QuotientGroup.mk' (pCore 2 P)).map_one
    · rfl
  map_mul' x y := by
    apply RegularWreathProduct.ext
    · funext i
      exact (QuotientGroup.mk' (pCore 2 P)).map_mul
        ⟨x.val.left i,x.property i⟩
        ⟨y.val.left (x.val.right⁻¹*i),y.property (x.val.right⁻¹*i)⟩
    · rfl

private theorem pairQuotient_surjective : Function.Surjective pairQuotient := by
  intro x
  choose a ha using fun i => QuotientGroup.mk'_surjective (pCore 2 P) (x.left i)
  refine ⟨⟨⟨fun i => (a i).val,x.right⟩,fun i => (a i).property⟩,?_⟩
  exact RegularWreathProduct.ext (funext ha) rfl

private theorem quotient_twoCore : pCore 2 WQ = ⊥ := by
  let eQ := (ParabolicCoreModel.coreQuotientEquiv MarkedAutomorphisms.lineEquivSymmetric).trans
    (Classical.choice SLTwoPermThree.sl2Two_equiv_perm_three).symm
  let e := RegularWreathProduct.congr eQ (MulEquiv.refl WreathPair.Bit)
  apply (map_injective (f := e.toMonoidHom) e.injective)
  rw [pCore_map_iso,Theory.GroupTheory.WreathTwoResidual.twoCore_eq_bot,Subgroup.map_bot]

private theorem line_core_radical (g : SL) (hg : g ∈ lineParabolicSL.pCoreIn 2) :
    g = radical (Multiplicative.ofAdd ![g.val 0 2,g.val 1 2]) := by
  rw [lineParabolicSL_pCoreIn_two_eq_R] at hg
  obtain ⟨c,rfl⟩ := hg
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

private theorem core_coordinates {w : Actor} (hw : w ∈ Line.pCoreIn 2) :
    w.right = 1 ∧ ∀ i, w.left i ∈ lineParabolicSL.pCoreIn 2 := by
  obtain ⟨x,hx,rfl⟩ := hw
  have hm : ((pCore 2 Line).map pairQuotient).Normal :=
    (inferInstance : (pCore 2 Line).Normal).map _ pairQuotient_surjective
  have hl : (pCore 2 Line).map pairQuotient ≤ pCore 2 WQ :=
    le_sSup ⟨hm,pCore_isPGroup.map pairQuotient⟩
  have he := hl (mem_map_of_mem pairQuotient hx)
  rw [quotient_twoCore,mem_bot] at he
  refine ⟨congrArg RegularWreathProduct.right he,fun i => ?_⟩
  have hi : QuotientGroup.mk' (pCore 2 P) ⟨x.val.left i,x.property i⟩ = 1 :=
    congrArg (fun a : WQ => a.left i) he
  exact ⟨⟨x.val.left i,x.property i⟩,(QuotientGroup.eq_one_iff _).mp hi,rfl⟩

/-- The intrinsic two-core acts trivially on the literal fixed four-space. -/
theorem core_le_lineAction_kernel : pCore 2 Line ≤ lineAction.asGroupHom.ker := by
  intro a ha
  obtain ⟨hr,hl⟩ := core_coordinates (show a.val ∈ Line.pCoreIn 2 from ⟨a,ha,rfl⟩)
  have he : a.val = radicalPair
      (Multiplicative.ofAdd ![(a.val.left 1).val 0 2,(a.val.left 1).val 1 2],
        Multiplicative.ofAdd ![(a.val.left BinaryPermutation.FiveTensorSquare.swapIndex).val 0 2,
          (a.val.left BinaryPermutation.FiveTensorSquare.swapIndex).val 1 2]) := by
    apply RegularWreathProduct.ext
    · funext i
      rcases BinaryPermutation.FiveTensorSquare.index_cases i with rfl | rfl
      · simpa [radicalPair,pair] using line_core_radical _ (hl 1)
      · simpa [radicalPair,pair] using line_core_radical _ (hl _)
    · exact hr
  apply Units.ext
  apply LinearMap.ext
  intro X
  apply Subtype.ext
  change action (PointParabolic.tensorHom a.val) X.val = X.val
  rw [he]
  exact (radical_fixed_iff X.val).mpr X.property _

private def cubicLine : Three × Three →* Line :=
  cubicPair.codRestrict Line cubic_mem_line

private theorem cubic_action_injective :
    Function.Injective (lineAction.asGroupHom.comp cubicLine) := by
  apply (injective_iff_map_eq_one _).mpr
  intro a ha
  apply cubic_faithful a
  intro X hX
  exact congrArg (fun f : (Module.End (ZMod 2) square)ˣ => (f.val ⟨X,hX⟩).val) ha

private theorem card_line : Nat.card Line = 1152 := by
  change Nat.card (RegularWreathProduct.coordinateSubgroup (Q := WreathPair.Bit) lineParabolicSL) = _
  rw [Nat.card_congr (RegularWreathProduct.coordinateSubgroupEquiv lineParabolicSL).toEquiv,
    RegularWreathProduct.card,card_lineParabolicSL]
  norm_num [WreathPair.Bit,Nat.card_eq_fintype_card]

/-- The action kernel on the fixed four-space is a two-group: the actual
faithful elementary nine exhausts the odd part of the plane parabolic. -/
theorem lineAction_kernel_isTwoGroup : IsPGroup 2 lineAction.asGroupHom.ker := by
  let f := lineAction.asGroupHom
  let c : Three × Three →* f.range :=
    f.rangeRestrict.comp cubicLine
  have hi : Function.Injective c := by
    intro x y h
    exact cubic_action_injective (congrArg Subtype.val h)
  have hd : 9 ∣ Nat.card f.range := by
    have h := card_dvd_of_injective c hi
    simpa [Nat.card_prod,Three,Nat.card_eq_fintype_card] using h
  obtain ⟨k,hk⟩ := hd
  have hc := f.ker.card_mul_index
  rw [index_ker,card_line,hk] at hc
  apply IsPGroup.of_card_dvd_pow (n := 7)
  refine ⟨k,?_⟩
  change 128 = Nat.card f.ker*k
  nlinarith

/-- Fixing the whole four-space forces the actor into the paired plane radicals. -/
theorem lineAction_kernel_radical (a : Line) (ha : lineAction.asGroupHom a = 1) :
    a.val ∈ radicalPair.range := by
  have hk : lineAction.asGroupHom.ker ≤ pCore 2 Line :=
    le_sSup ⟨inferInstance,lineAction_kernel_isTwoGroup⟩
  obtain ⟨hr,hl⟩ := core_coordinates
    (show a.val ∈ Line.pCoreIn 2 from ⟨a,hk ha,rfl⟩)
  refine ⟨(Multiplicative.ofAdd ![(a.val.left 1).val 0 2,(a.val.left 1).val 1 2],
    Multiplicative.ofAdd ![(a.val.left BinaryPermutation.FiveTensorSquare.swapIndex).val 0 2,
      (a.val.left BinaryPermutation.FiveTensorSquare.swapIndex).val 1 2]),?_⟩
  apply RegularWreathProduct.ext
  · funext i
    rcases BinaryPermutation.FiveTensorSquare.index_cases i with rfl | rfl
    · simpa [radicalPair,pair] using (line_core_radical _ (hl 1)).symm
    · simpa [radicalPair,pair] using (line_core_radical _ (hl _)).symm
  · exact hr.symm

/-- The faithful action image of the plane parabolic has trivial two-core. -/
theorem lineAction_image_twoCore : pCore 2 lineAction.asGroupHom.range = ⊥ := by
  let f := lineAction.asGroupHom.rangeRestrict
  have hk : IsPGroup 2 f.ker := by
    dsimp only [f]
    rw [MonoidHom.ker_rangeRestrict]
    exact lineAction_kernel_isTwoGroup
  let : Finite lineAction.asGroupHom.range := Finite.of_surjective _ lineAction.asGroupHom.rangeRestrict_surjective
  have hc := f.comap_pCore_of_ker_isPGroup lineAction.asGroupHom.rangeRestrict_surjective hk
  apply bot_unique
  intro x hx
  obtain ⟨a,rfl⟩ := lineAction.asGroupHom.rangeRestrict_surjective x
  have ha : a ∈ pCore 2 Line := hc ▸ hx
  exact Subtype.ext (core_le_lineAction_kernel ha)

private theorem line_solvable : Group.IsSolvable Line := by
  let : Group.IsSolvable (Equiv.Perm (Fin 4)) := Equiv.Perm.isSolvable_fin_four
  let W := RegularWreathProduct (Equiv.Perm (Fin 4)) WreathPair.Bit
  let f : W →* WreathPair.Bit := RegularWreathProduct.rightHom
  let c : WreathPair.Bit := Multiplicative.ofAdd 1
  let j : f.ker →* (Equiv.Perm (Fin 4) × Equiv.Perm (Fin 4)) := {
    toFun := fun x => (x.val.left 1,x.val.left c)
    map_one' := rfl
    map_mul' := fun x y => by
      have hx : x.val.right = 1 := x.property
      apply Prod.ext
      · change x.val.left 1 * y.val.left (x.val.right⁻¹*1) = x.val.left 1 * y.val.left 1
        rw [hx,inv_one,one_mul]
      · change x.val.left c * y.val.left (x.val.right⁻¹*c) = x.val.left c * y.val.left c
        rw [hx,inv_one,one_mul] }
  have hj : Function.Injective j := by
    intro x y hxy
    apply Subtype.ext
    apply RegularWreathProduct.ext
    · funext i
      have hi : i = 1 ∨ i = c := by revert i; decide
      rcases hi with rfl | rfl
      · exact congrArg Prod.fst hxy
      · exact congrArg Prod.snd hxy
    · exact x.property.trans y.property.symm
  let : Group.IsSolvable f.ker := Group.isSolvable_of_isSolvable_injective hj
  let : Group.IsSolvable W :=
    Group.isSolvable_of_ker_le_range f.ker.subtype f (by rw [range_subtype])
  exact Group.isSolvable_of_isSolvable_injective (f := WreathPair.lineEquiv.toMonoidHom) WreathPair.lineEquiv.injective

/-- Solvability is inherited by the actual action image, with its kernel retained. -/
theorem lineAction_image_solvable : Group.IsSolvable lineAction.asGroupHom.range := by
  let : Group.IsSolvable Line := line_solvable
  exact Group.isSolvable_of_surjective lineAction.asGroupHom.rangeRestrict_surjective

end BinaryTensorThree.PlaneFixed
