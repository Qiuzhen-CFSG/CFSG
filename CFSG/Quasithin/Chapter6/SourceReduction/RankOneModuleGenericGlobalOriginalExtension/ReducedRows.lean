module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.OriginalExtension.LinearNativeApplication
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.OriginalExtension.ReducedSolvability
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.OriginalExtension.UnitaryFourNativeApplication
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.OriginalExtension.ReeNative
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalOriginalExtension.UnitaryFourCatalogue

/-!
# Reduced DGS rows in the original selected-perfect pair

Nonsolvability of the actual reduced endpoints excludes the binary linear,
unitary-four and Ree parameters before applying native restoration. In the
linear row, normalized-Borel containment S ≤ R makes S equal its reduced
subgroup. Transport then restores both endpoint maps and the whole Borel.
The Ree restoration gives the same full diagram; the unitary-four row keeps
its possible degree-two graph extension. All statements retain arbitrary
selected perfect R and the original S = O₂(N_G(L) ∩ H).

These are conditional reductions of genuine reduced model comparisons,
not exhaustive DGS recognition. Source: Aschbacher--Smith F.1.12,
pp.263--264, and 5.2.6, pp.650--651 (`refs/quasithin.pdf`); DGS,
*Groups and Graphs*, (15.2), pp.226--228 (`refs/groups-and-graphs.pdf`).
-/

public noncomputable section
open Subgroup Theory.GroupTheory RankTwoAmalgam
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
open ChapterF.Source.DGS85.OriginalExtension
namespace ReducedRows
open Matrix.PSL3.LinearThree

private theorem binary_point_solvable (F : Type) [Field F] [Finite F]
    (hF : Nat.card F = 2) : Group.IsSolvable (pointParabolic F) := by
  let := Fintype.ofFinite F
  let e : F ≃+* ZMod 2 := (ZMod.ringEquivOfPrime F Nat.prime_two
    (by rwa [← Nat.card_eq_fintype_card])).symm
  have hu : ∀ a : F, a ≠ 0 → a = 1 := by
    intro a ha
    apply e.injective
    have hne : e a ≠ 0 := by simpa only [map_ne_zero] using ha
    have h : ∀ z : ZMod 2, z ≠ 0 → z = 1 := by decide
    simpa only [map_one] using h (e a) hne
  have hp : pointLocalSL F = pointParabolicSL F := by
    apply le_antisymm (pointLocalSL_le F)
    intro g hg
    have h := (mem_pointParabolicSL_iff F g).mp hg
    have hn : g.val 0 0 ≠ 0 := by
      intro hz
      have hi := congrArg (fun a : Matrix.SpecialLinearGroup (Fin 3) F => a.val 0 0)
        (inv_mul_cancel g)
      change (g⁻¹.val * g.val) 0 0 = 1 at hi
      simp [Matrix.mul_apply, Fin.sum_univ_three, h.1, h.2, hz] at hi
    exact (mem_pointLocalSL_iff F g).mpr ⟨hu _ hn,h⟩
  have he : pointLocal F = pointParabolic F :=
    congrArg (fun K => K.map (Matrix.PSL3.projection F)) hp
  rw [← he]
  let : Group.IsSolvable (Equiv.Perm (Fin 4)) := Equiv.Perm.isSolvable_fin_four
  exact Group.isSolvable_of_isSolvable_injective
    (f := (ChapterF.GreenBook.LieModels.LinearThree.pointLocalEquivS4 F hF).toMonoidHom)
    (ChapterF.GreenBook.LieModels.LinearThree.pointLocalEquivS4 F hF).injective

open Matrix Theory.SpecificGroups.ClassicalUnitary
open ChapterF.GreenBook.LieModels.UnitaryFour in
private theorem binary_unitary_point_solvable :
    Group.IsSolvable (pointParabolic 1 (Nat.le_refl 1)) := by
  let := PointLocal.matrixLocal_isSolvable_two
  have hsol : Group.IsSolvable (pointParabolicMatrix 1 (Nat.le_refl 1)) := by
    apply Group.isSolvable_of_ker_le_range
      (inclusion (UnitaryFourPointLocal.localSU_le_pointParabolicSU (MatrixField 1)
        (standardForm 1 (Nat.le_refl 1))))
      (UnitaryFourPointResidual.pointScalarUnits (MatrixField 1) (standardForm 1 (Nat.le_refl 1)))
    rw [inclusion_range, UnitaryFourPointResidual.pointScalarUnits_ker]
  let := hsol
  let e : pointParabolicMatrix 1 (Nat.le_refl 1) ≃* pointParabolic 1 (Nat.le_refl 1) :=
    (pointParabolicMatrix 1 (Nat.le_refl 1)).equivMapOfInjective (projection 1 (Nat.le_refl 1))
      (projection_injective 1 (Nat.le_refl 1))
  exact Group.isSolvable_of_surjective (f := e.toMonoidHom) e.surjective
end ReducedRows

section Reindex
variable {X B Y X' B' Y' X'' B'' Y'' : Type*}
  [Group X] [Group B] [Group Y] [Group X'] [Group B'] [Group Y']
  [Group X''] [Group B''] [Group Y'']
  {α : RankTwoAmalgam X B Y} {β : RankTwoAmalgam X' B' Y'}
  {γ : RankTwoAmalgam X'' B'' Y''}

private theorem cancel_reindex_left (a : Iso α β) (b : Iso β γ) (x : X') :
    (a.symm.trans (a.trans b)).left x = b.left x :=
  congrArg b.left (a.left.apply_symm_apply x)

private theorem cancel_reindex_middle (a : Iso α β) (b : Iso β γ) (x : B') :
    (a.symm.trans (a.trans b)).middle x = b.middle x :=
  congrArg b.middle (a.middle.apply_symm_apply x)

private theorem cancel_reindex_right (a : Iso α β) (b : Iso β γ) (x : Y') :
    (a.symm.trans (a.trans b)).right x = b.right x :=
  congrArg b.right (a.right.apply_symm_apply x)
end Reindex

namespace Preparation
variable {G : Type*} [Group G] [Finite G]
  {κ : GroupClass} {T : Sylow 2 G} {L W H A B R : Subgroup G} {n : ℕ}
  (d : Preparation T L H A B R) (h : Input κ T L W n)
  (hTH : (T : Subgroup G) ≤ H) (hp : Group.IsPerfect R)

include d h hTH hp in
/-- The binary linear point endpoint cannot contain its original nonsolvable factor. -/
theorem linear_reduced_parameter
    (F : Type) [Field F] [Finite F] [CharP F 2]
    {m : ℕ} (hm : 0 < m) (hF : Nat.card F = 2^m) (i : Bool)
    (e : Iso (reducedAmalgam ![L,R] (sourceS L H)) (LinearNative.amalgam F i)) :
    1 < m := by
  by_contra hgt
  have hm1 : m = 1 := by omega
  have hc : Nat.card F = 2 := by simpa only [hm1,pow_one] using hF
  let := ReducedRows.binary_point_solvable F hc
  cases i
  · let j : _ ≃* Matrix.PSL3.LinearThree.pointParabolic F := e.left
    exact reduced_parabolics_not_solvable d h hTH hp 0
      (Group.isSolvable_of_isSolvable_injective (f := j.toMonoidHom) j.injective)
  · let j : _ ≃* Matrix.PSL3.LinearThree.pointParabolic F := e.right
    exact reduced_parabolics_not_solvable d h hTH hp 1
      (Group.isSolvable_of_isSolvable_injective (f := j.toMonoidHom) j.injective)

include d h hTH in
/-- Containment in the same selected R removes the original-to-reduced Sylow gap. -/
theorem sourceS_eq_reduced_of_le_right (hs : sourceS L H ≤ R) :
    sourceS L H = ChapterF.Source.SuzukiContainment.reducedSylow ![L,R] (sourceS L H) := by
  let hf := d.hypothesisF11 h hTH
  apply le_antisymm _ (ChapterF.Source.SuzukiContainment.reducedSylow_le hf)
  have ht := ChapterF.Source.SuzukiContainment.localSylow_le_reducedSylow hf 1
  change sourceS L H ⊓ R ≤ _ at ht
  rwa [inf_eq_left.mpr hs] at ht

/-- The whole original overlap, rather than its two-core, is the middle group. -/
def sourceToOriginal : Iso (sourceParabolicAmalgam ![L,R] (sourceS L H))
    (originalAmalgam ![L,R] (sourceS L H)) where
  left := MulEquiv.refl _
  right := MulEquiv.refl _
  middle := MulEquiv.subgroupCongr (ChapterF.Source.lemma_F_1_3_6 (d.hypothesisF11 h hTH))
  left_commutes _ := rfl
  right_commutes _ := rfl

/-- Once S lies in the selected factor, the original and reduced diagrams
have the same ambient elements, with both endpoint squares retained. -/
def originalLinearComparisonOfReduced
    (F : Type) [Field F] [Finite F] [CharP F 2]
    {m : ℕ} (hm : 0 < m) (hF : Nat.card F = 2^m) (i : Bool)
    (e : Iso (reducedAmalgam ![L,R] (sourceS L H)) (LinearNative.amalgam F i)) :
    Iso (sourceParabolicAmalgam ![L,R] (sourceS L H)) (LinearNative.amalgam F i) :=
  (d.sourceToOriginal h hTH).trans
    ((NativeRestoration.originalIsoReduced (d.sourceS_eq_reduced_of_le_right h hTH
      (linear_original_core_and_containment_of_reduced_iso d h hTH F
        (d.linear_reduced_parameter h hTH hp F hm hF i e) hF i e hp).2)).trans e)

include d h hTH hp in
/-- Both orientations of every positive linear degree restore the full catalogue comparison. -/
theorem concreteComparison_of_reduced_linear
    (F : Type) [Field F] [Finite F] [CharP F 2]
    {m : ℕ} (hm : 0 < m) (hF : Nat.card F = 2^m) (i : Bool)
    (e : Iso (reducedAmalgam ![L,R] (sourceS L H)) (LinearNative.amalgam F i)) :
    ConcreteAmalgamComparison (sourceParabolicAmalgam ![L,R] (sourceS L H)) := by
  have f := d.originalLinearComparisonOfReduced h hTH hp F hm hF i e
  refine .linear F m hm hF ?_
  cases i
  · exact Or.inl ⟨f⟩
  · exact Or.inr ⟨f⟩

include d h hTH hp in
/-- The binary point endpoint is solvable in either orientation, so m > 1 is derived. -/
theorem unitaryFour_reduced_parameter (m : ℕ) (hm : 1 ≤ m) (point : Bool)
    (e : Iso (reducedAmalgam ![L,R] (sourceS L H))
      (UnitaryFourNative.amalgam m hm point)) : 1 < m := by
  by_contra hgt
  have hm1 : m = 1 := by omega
  subst m
  let := ReducedRows.binary_unitary_point_solvable
  cases point
  · let j : _ ≃* ChapterF.GreenBook.LieModels.UnitaryFour.pointParabolic 1 hm := e.right
    exact reduced_parabolics_not_solvable d h hTH hp 1
      (Group.isSolvable_of_isSolvable_injective (f := j.toMonoidHom) j.injective)
  · let j : _ ≃* ChapterF.GreenBook.LieModels.UnitaryFour.pointParabolic 1 hm := e.left
    exact reduced_parabolics_not_solvable d h hTH hp 0
      (Group.isSolvable_of_isSolvable_injective (f := j.toMonoidHom) j.injective)

include d h hTH hp in
/-- Restore both ordinary and degree-two U₄ rows without an extra degree hypothesis. -/
theorem concreteComparison_of_reduced_unitaryFour (m : ℕ) (hm : 1 ≤ m) (point : Bool)
    (e : Iso (reducedAmalgam ![L,R] (sourceS L H))
      (UnitaryFourNative.amalgam m hm point)) :
    ConcreteAmalgamComparison (sourceParabolicAmalgam ![L,R] (sourceS L H)) := by
  obtain ⟨f⟩ := exists_original_unitaryFour_marking_of_reduced_iso
    (d.hypothesisF11 h hTH) m hm (d.unitaryFour_reduced_parameter h hTH hp m hm point e) point e
  exact d.concreteComparison_of_original_unitaryFour h hTH hp m hm point f

include d h hTH hp in
/-- The binary native Ree endpoint is solvable; every surviving parameter is positive. -/
theorem ree_reduced_parameter (m : ℕ) (i : Bool)
    (e : Iso (reducedAmalgam ![L,R] (sourceS L H)) (ReeNative.amalgam m i)) : 0 < m := by
  by_contra hgt
  have hm0 : m = 0 := by omega
  subst m
  let := ReeComparison.binary_parabolic_solvable (ReeNative.side i)
  exact reduced_parabolics_not_solvable d h hTH hp 0
    (Group.isSolvable_of_isSolvable_injective (f := e.left.toMonoidHom) e.left.injective)

/-- Restore the supplied Ree marking on the original full inclusion diagram. -/
def originalReeComparisonOfReduced (m : ℕ) (i : Bool)
    (e : Iso (reducedAmalgam ![L,R] (sourceS L H)) (ReeNative.amalgam m i)) :
    Iso (sourceParabolicAmalgam ![L,R] (sourceS L H)) (ReeNative.amalgam m i) :=
  (d.sourceToOriginal h hTH).trans (ReeNative.originalIso (d.hypothesisF11 h hTH) m i e
    (d.ree_reduced_parameter h hTH hp m i e))

include d h hTH hp in
/-- The full Ree catalogue comparison retains every parameter and both orientations. -/
theorem concreteComparison_of_reduced_ree (m : ℕ) (i : Bool)
    (e : Iso (reducedAmalgam ![L,R] (sourceS L H)) (ReeNative.amalgam m i)) :
    ConcreteAmalgamComparison (sourceParabolicAmalgam ![L,R] (sourceS L H)) := by
  have f := d.originalReeComparisonOfReduced h hTH hp m i e
  refine .ree m ?_
  cases i
  · exact Or.inr ⟨f⟩
  · exact Or.inl ⟨f⟩

/-- All three linear restrictions are the supplied reduced maps. The middle
identity holds on the entire Borel, including its odd elements. -/
theorem originalLinearComparisonOfReduced_restrictions
    (F : Type) [Field F] [Finite F] [CharP F 2]
    {m : ℕ} (hm : 0 < m) (hF : Nat.card F = 2^m) (i : Bool)
    (e : Iso (reducedAmalgam ![L,R] (sourceS L H)) (LinearNative.amalgam F i)) :
    let f := (d.sourceToOriginal h hTH).symm.trans
      (d.originalLinearComparisonOfReduced h hTH hp F hm hF i e)
    (∀ x, f.left (inclusion (ChapterF.Source.SuzukiContainment.reduced_parabolic_le
      (d.hypothesisF11 h hTH) 0) x) = e.left x) ∧
    (∀ x, f.middle (inclusion (ChapterF.Source.SuzukiContainment.reduced_commonBorel_le
      (d.hypothesisF11 h hTH)) x) = e.middle x) ∧
    (∀ x, f.right (inclusion (ChapterF.Source.SuzukiContainment.reduced_parabolic_le
      (d.hypothesisF11 h hTH) 1) x) = e.right x) :=
by
  let hs := d.sourceS_eq_reduced_of_le_right h hTH
    (linear_original_core_and_containment_of_reduced_iso d h hTH F
      (d.linear_reduced_parameter h hTH hp F hm hF i e) hF i e hp).2
  let b := (NativeRestoration.originalIsoReduced hs).trans e
  have he := NativeRestoration.originalIsoReduced_trans_reduced (d.hypothesisF11 h hTH) hs e
  exact ⟨fun x => (cancel_reindex_left (d.sourceToOriginal h hTH) b _).trans (he.1 x),
    fun x => (cancel_reindex_middle (d.sourceToOriginal h hTH) b _).trans (he.2.1 x),
    fun x => (cancel_reindex_right (d.sourceToOriginal h hTH) b _).trans (he.2.2 x)⟩

/-- The restored Ree comparison preserves both supplied endpoint maps and
its full middle map on the literal reduced inclusions. -/
theorem originalReeComparisonOfReduced_restrictions (m : ℕ) (i : Bool)
    (e : Iso (reducedAmalgam ![L,R] (sourceS L H)) (ReeNative.amalgam m i)) :
    let f := (d.sourceToOriginal h hTH).symm.trans
      (d.originalReeComparisonOfReduced h hTH hp m i e)
    (∀ x, f.left (inclusion (ChapterF.Source.SuzukiContainment.reduced_parabolic_le
      (d.hypothesisF11 h hTH) 0) x) = e.left x) ∧
    (∀ x, f.middle (inclusion (ChapterF.Source.SuzukiContainment.reduced_commonBorel_le
      (d.hypothesisF11 h hTH)) x) = e.middle x) ∧
    (∀ x, f.right (inclusion (ChapterF.Source.SuzukiContainment.reduced_parabolic_le
      (d.hypothesisF11 h hTH) 1) x) = e.right x) :=
by
  let hm := d.ree_reduced_parameter h hTH hp m i e
  let b := ReeNative.originalIso (d.hypothesisF11 h hTH) m i e hm
  have he := ReeNative.originalIso_reduced (d.hypothesisF11 h hTH) m i e hm
  exact ⟨fun x => (cancel_reindex_left (d.sourceToOriginal h hTH) b _).trans (he.1 x),
    fun x => (cancel_reindex_middle (d.sourceToOriginal h hTH) b _).trans (he.2.1 x),
    fun x => (cancel_reindex_right (d.sourceToOriginal h hTH) b _).trans (he.2.2 x)⟩

include d h hTH hp in
/-- Binary DGS type data on a reduced local join are impossible. This uses
the quotient of that join, not the distinct full parabolic quotient. -/
theorem not_binary_reduced_localJoin_quotient (i : Fin 2) :
    ¬ ClassicalGroup.IsPSL
      ((![L,R] i ⊔ ChapterF.Source.SuzukiContainment.reducedSylow ![L,R] (sourceS L H)
        : Subgroup G) ⧸ pCore 2 (![L,R] i ⊔
          ChapterF.Source.SuzukiContainment.reducedSylow ![L,R] (sourceS L H) : Subgroup G)) 2 2 := by
  rintro ⟨F,_,_,hF,⟨e⟩⟩
  let P := ![L,R] i ⊔ ChapterF.Source.SuzukiContainment.reducedSylow ![L,R] (sourceS L H)
  let := Theory.PSL2.OuterSolvable.isSolvable_of_card_two hF
  let : Group.IsNilpotent (pCore 2 P) := pCore_isNilpotent
  let : Group.IsSolvable P := (Group.isSolvable_iff_subgroup_quotient (pCore 2 P)).mpr
    ⟨inferInstance,Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective⟩
  let : Group.IsSolvable (![L,R] i) := Group.isSolvable_of_isSolvable_injective
    (inclusion_injective (show ![L,R] i ≤ P from le_sup_left))
  exact d.parabolics_not_solvable h hp i
    (((d.hypothesisF11 h hTH).parabolic_solvable_iff_local_quotient i).mpr inferInstance)

include d h hTH hp in
/-- A binary quotient of the full reduced endpoint is also impossible,
without identifying any structural type with a concrete binary Ree model. -/
theorem not_binary_reduced_parabolic_quotient (i : Fin 2) :
    ¬ ClassicalGroup.IsPSL
      (ChapterF.Source.parabolic ![L,R]
        (ChapterF.Source.SuzukiContainment.reducedSylow ![L,R] (sourceS L H)) i ⧸
        pCore 2 (ChapterF.Source.parabolic ![L,R]
          (ChapterF.Source.SuzukiContainment.reducedSylow ![L,R] (sourceS L H)) i)) 2 2 := by
  rintro ⟨F,_,_,hF,⟨e⟩⟩
  let P := ChapterF.Source.parabolic ![L,R]
    (ChapterF.Source.SuzukiContainment.reducedSylow ![L,R] (sourceS L H)) i
  let := Theory.PSL2.OuterSolvable.isSolvable_of_card_two hF
  let : Group.IsNilpotent (pCore 2 P) := pCore_isNilpotent
  exact reduced_parabolics_not_solvable d h hTH hp i
    ((Group.isSolvable_iff_subgroup_quotient (pCore 2 P)).mpr
      ⟨inferInstance,Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective⟩)

end Preparation
end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
