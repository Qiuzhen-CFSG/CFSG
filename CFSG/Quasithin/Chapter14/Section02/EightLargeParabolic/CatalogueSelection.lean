module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalRecognitionCatalogue
public import Theory.SpecificGroups.PSL3.SmallCompletion.Orders
public import Theory.SpecificGroups.SymplecticFour.FlagPaths.Counts
public import Theory.AtlasPort.LinearGroups.G2.ParabolicLocalOrder
public import Theory.SpecificGroups.Triality.OuterOddSubgroups.Coverage.RootGeometry.SimpleRecognition.ParabolicIntersections
public import Theory.SpecificGroups.ReeF4.SourceCompletion.LocalGeometry
public import CFSG.Quasithin.ChapterF.Section01.GreenBook.UnitaryFive.LocalStructure.PlaneCore
public import Theory.GroupTheory.PCoreSectionCard

/-!
# Selecting binary triality from the full concrete amalgam catalogue

Full-overlap degrees nine and three distinguish the endpoints. Equal local
orders exclude linear, symplectic and G₂ models. The unitary-four plane has
an SL₂ section whose order divides neither 504 nor 42, including in the
outer extension. The unitary-five plane has degree seventeen. The Ree
local degrees and the odd Borel factor exclude all Ree parameters.

Every fixed exceptional Borel has order prime to seven, including the
whole Hall–Janko Borels. Thus even their weaker parabolic equivalences
are excluded. The remaining triality degree formula forces parameter one
and the original orientation. We retain the actual isomorphism, hence its
whole middle map and both commuting squares.

This is a selection theorem from the unchanged exhaustive comparison
contract; constructing that comparison remains with the DGS source owner.
Source: Aschbacher–Smith F.1.12 and 14.2.16(1), pp.262–264,986;
DGS (1985), Part II, Theorem A, pp.99–100, and (15.1)–(15.3), pp.225–231.
-/

public noncomputable section
open Subgroup Theory.GroupTheory RankTwoAmalgam
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter14.Section02.EightLargeParabolic.Catalogue
open ChapterF.GreenBook
variable {L B R : Type*} [Group L] [Group B] [Group R]
  [Finite L] [Finite B] [Finite R] {α : RankTwoAmalgam L B R}

private theorem relIndex_of_cards {A : Type*} [Group A] [Finite A]
    {P Q : Subgroup A} (h : Q ≤ P) {n : ℕ}
    (hc : Nat.card P = Nat.card Q * n) : Q.relIndex P = n := by
  have hh := (Q.subgroupOf P).card_mul_index
  rw [Nat.card_congr (subgroupOfEquivOfLe h).toEquiv, hc] at hh
  exact Nat.eq_of_mul_eq_mul_left (Nat.card_pos (α := Q)) hh

omit [Group L] [Group R] [Finite L] [Finite R] in
private theorem unequal_endpoints (hl : Nat.card L = Nat.card B * 9)
    (hr : Nat.card R = Nat.card B * 3) : Nat.card L ≠ Nat.card R := by
  have := Nat.card_pos (α := B)
  omega

omit [Finite B] in
private theorem no_two_group_middle (h7 : 7 ∣ Nat.card B)
    {D : Type*} [Group D] [Finite D] (e : B ≃* D) (hD : IsPGroup 2 D) : False := by
  obtain ⟨k,hk⟩ := hD.exists_card_dvd_pow
  rw [Nat.card_congr e.toEquiv] at h7
  have hd : 7 ∣ 2^k := h7.trans hk
  have := (show Nat.Prime 7 by decide).dvd_of_dvd_pow hd
  norm_num at this

omit [Finite L] [Finite B] [Finite R] in
private theorem not_exceptional (h7 : 7 ∣ Nat.card B) (c : ExceptionalModels.Case)
    (h : ExceptionalModels.ParabolicModel c α) : False := by
  cases c with
  | g2Derived =>
    obtain ⟨e⟩ := h
    exact no_two_group_middle h7 e.middle ExceptionalModels.G2.derivedS.isPGroup'
  | g2Full =>
    obtain ⟨e⟩ := h
    exact no_two_group_middle h7 e.middle ExceptionalModels.G2.fullS.isPGroup'
  | tits =>
    obtain ⟨e⟩ := h
    rw [Nat.card_congr e.middle.toEquiv, Tits.ExceptionalParabolics.overlap_card] at h7
    norm_num at h7
  | reeFull =>
    obtain ⟨e⟩ := h
    rw [Nat.card_congr e.middle.toEquiv, Tits.ExceptionalParabolics.FullRee.borel_card] at h7
    norm_num at h7
  | j2 =>
    obtain ⟨e⟩ := h
    rw [Nat.card_congr e.middle.toEquiv, HallJanko.card_j2Model_B] at h7
    norm_num at h7
  | autJ2 =>
    obtain ⟨e⟩ := h
    rw [Nat.card_congr e.middle.toEquiv, HallJanko.card_autJ2Model_B] at h7
    norm_num at h7
  | m12 =>
    obtain ⟨e⟩ := h
    apply no_two_group_middle h7 e.middle
    rw [MathieuTwelve.B_eq_S]
    exact MathieuTwelve.S.isPGroup'
  | autM12 =>
    obtain ⟨e⟩ := h
    apply no_two_group_middle h7 (e.middle.trans AutMathieuTwelve.ambientIso.middle.symm)
    rw [AutMathieuTwelve.B_eq_S]
    exact AutMathieuTwelve.S.isPGroup'

private theorem linear_equal (F : Type) [Field F] [Finite F] :
    Nat.card (Matrix.PSL3.LinearThree.pointParabolic F) =
      Nat.card (Matrix.PSL3.LinearThree.lineParabolic F) := by
  have h0 := (Matrix.PSL3.LinearThree.borel F).subgroupOf
    (Matrix.PSL3.SmallCompletion.parabolic F false) |>.card_mul_index
  have h1 := (Matrix.PSL3.LinearThree.borel F).subgroupOf
    (Matrix.PSL3.SmallCompletion.parabolic F true) |>.card_mul_index
  rw [Nat.card_congr (subgroupOfEquivOfLe
    (Matrix.PSL3.SmallCompletion.borel_le_parabolic F false)).toEquiv] at h0
  rw [Nat.card_congr (subgroupOfEquivOfLe
    (Matrix.PSL3.SmallCompletion.borel_le_parabolic F true)).toEquiv] at h1
  change _ * (Matrix.PSL3.LinearThree.borel F).relIndex
    (Matrix.PSL3.SmallCompletion.parabolic F false) = _ at h0
  change _ * (Matrix.PSL3.LinearThree.borel F).relIndex
    (Matrix.PSL3.SmallCompletion.parabolic F true) = _ at h1
  rw [Matrix.PSL3.SmallCompletion.borel_relIndex] at h0 h1
  exact h0.symm.trans h1

private theorem g2_equal (F : Type) [Field F] [Finite F] :
    Nat.card (Atlas.G2.LieParabolicSetup.parabolic₁ (F := F)) =
      Nat.card (Atlas.G2.LieParabolicSetup.parabolic₂ (F := F)) := by
  rw [Atlas.G2.ParabolicCells.short_card]
  change (Nat.card F + 1) * Nat.card (Atlas.G2.borel (K := F)) =
    Nat.card (Atlas.G2.parabolic (F := F))
  rw [Atlas.G2.card_borel, Atlas.G2.card_parabolic]
  ring


private theorem no_unitary_plane {X : Type*} [Group X] [Finite X]
    (hX : Nat.card (X ⧸ pCore 2 X) = 504 ∨ Nat.card (X ⧸ pCore 2 X) = 42)
    (m : ℕ) (hm : 1 ≤ m)
    (j : LieModels.UnitaryFour.L2 m hm →* X) (hj : Function.Injective j) : False := by
  let U := LieModels.UnitaryFour.L2 m hm
  have hd := j.card_corefree_quotient_dvd_of_embedding hj
    (QuotientGroup.mk' (pCore 2 U)) (QuotientGroup.mk'_surjective _)
    (pCore_quotient_pCore_eq_bot (G := U) 2)
  rw [Nat.card_congr (LieModels.UnitaryFour.L2QuotientEquivSL2 m hm).toEquiv,
    Atlas.card_sl_two, GaloisField.card 2 (2*m) (by omega)] at hd
  have hu : 2^(2*m) * ((2^(2*m))^2-1) ≤ 504 := by
    rcases hX with hX | hX
    · rw [hX] at hd
      exact Nat.le_of_dvd (by decide) hd
    · rw [hX] at hd
      exact (Nat.le_of_dvd (by decide) hd).trans (by decide : 42 ≤ 504)
  have hm1 : m = 1 := by
    by_contra hn
    have hp : 16 ≤ 2^(2*m) := show 2^4 ≤ 2^(2*m) from
      Nat.pow_le_pow_right (by decide) (by omega)
    have hp2 : 255 ≤ (2^(2*m))^2-1 := by
      have hh := Nat.pow_le_pow_left hp 2
      omega
    have hlo := Nat.mul_le_mul hp hp2
    omega
  subst m
  rcases hX with hX | hX <;> rw [hX] at hd <;> norm_num at hd

private def planeExtensionEmbedding (m : ℕ) (hm : 1 ≤ m) :
    LieModels.UnitaryFour.L2 m hm →* LieModels.UnitaryFour.Extension.plane m hm where
  toFun x := ⟨SemidirectProduct.inl x.val,
    (LieModels.UnitaryFour.Extension.mem_plane m hm _).mpr
      (LieModels.UnitaryFour.L2_le_planeParabolic m hm x.property)⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' x y := Subtype.ext (map_mul _ x.val y.val)

private theorem planeExtensionEmbedding_injective (m : ℕ) (hm : 1 ≤ m) :
    Function.Injective (planeExtensionEmbedding m hm) := by
  intro x y he
  exact Subtype.ext (congrArg (fun z : LieModels.UnitaryFour.Extension.plane m hm =>
    z.val.left) he)

omit [Finite L] [Finite B] [Finite R] in
private theorem triality_selected
    (hr : Nat.card R = Nat.card B * 3)
    (m : ℕ) (hm : 0 < m)
    (he : Nonempty (Iso α (LieModels.Triality.amalgam
        (_root_.Triality.Standard.binaryParameters m hm))) ∨
      Nonempty (Iso α (LieModels.Triality.amalgam
        (_root_.Triality.Standard.binaryParameters m hm)).reverse)) :
    Nonempty (Iso α (LieModels.Triality.amalgam
      (_root_.Triality.Standard.binaryParameters 1 Nat.zero_lt_one))) := by
  rcases he with he | he <;> obtain ⟨e⟩ := he
  · have hi := hr
    rw [Nat.card_congr e.right.toEquiv, Nat.card_congr e.middle.toEquiv] at hi
    have hi' := relIndex_of_cards
      (_root_.Triality.Standard.Parabolics.borel_le_parabolic _ .central) hi
    rw [_root_.Triality.Standard.OuterOdd.Coverage.RootGeometry.SimpleRecognition.borel_relIndex_parabolic] at hi'
    change 2^m + 1 = 3 at hi'
    have hm1 : m = 1 := by
      apply (Nat.pow_right_injective (by decide : 2 ≤ 2))
      change 2^m = 2
      omega
    subst m
    exact ⟨e⟩
  · have hi := hr
    rw [Nat.card_congr e.right.toEquiv, Nat.card_congr e.middle.toEquiv] at hi
    have hi' := relIndex_of_cards
      (_root_.Triality.Standard.Parabolics.borel_le_parabolic _ .arms) hi
    rw [_root_.Triality.Standard.OuterOdd.Coverage.RootGeometry.SimpleRecognition.borel_relIndex_parabolic] at hi'
    change (2^m)^3 + 1 = 3 at hi'
    have hlo : 2 ≤ 2^m := Nat.pow_le_pow_right (n := 2) (by decide) hm
    have := Nat.pow_le_pow_left hlo 3
    omega

omit [Finite L] [Finite B] [Finite R] in
private theorem not_ree
    (hr : Nat.card R = Nat.card B * 3)
    (h7 : 7 ∣ Nat.card B) (m : ℕ)
    (he : Nonempty (Iso α (LieModels.ReeFour.amalgam m)) ∨
      Nonempty (Iso α (LieModels.ReeFour.amalgam m).reverse)) : False := by
  by_cases hm : m = 0
  · subst m
    rcases he with he | he <;> obtain ⟨e⟩ := he
    all_goals
      apply no_two_group_middle h7 e.middle
      rw [LieModels.ReeFour.binary_overlap]
      exact (LieModels.ReeFour.sylow 0).isPGroup'
  · have hlo : 8 ≤ 2^(2*m+1) :=
      Nat.pow_le_pow_right (n := 2) (by decide) (by omega : 3 ≤ 2*m+1)
    rcases he with he | he <;> obtain ⟨e⟩ := he
    · have hi := hr
      rw [Nat.card_congr e.right.toEquiv, Nat.card_congr e.middle.toEquiv] at hi
      have hi' := relIndex_of_cards (ReeF4.Parabolics.borel_le_parabolic _ .linear) hi
      rw [ReeF4.SourceCompletion.borel_relIndex m (by omega), if_pos rfl] at hi'
      omega
    · have hi := hr
      rw [Nat.card_congr e.right.toEquiv, Nat.card_congr e.middle.toEquiv] at hi
      have hi' := relIndex_of_cards (ReeF4.Parabolics.borel_le_parabolic _ .suzuki) hi
      rw [ReeF4.SourceCompletion.borel_relIndex m (by omega), if_neg (by decide)] at hi'
      nlinarith

/-- The full concrete catalogue, at local degrees nine and three and the
actual core quotient orders, has only the correctly oriented binary triality row.
The conclusion retains the original comparison's middle map and both squares. -/
theorem triality_of_comparison
    (hl : Nat.card L = Nat.card B * 9) (hr : Nat.card R = Nat.card B * 3)
    (h7 : 7 ∣ Nat.card B)
    (hQL : Nat.card (L ⧸ pCore 2 L) = 504)
    (hQR : Nat.card (R ⧸ pCore 2 R) = 42)
    (hc : Chapter6.Source.RankOneGeneric.Global.ConcreteAmalgamComparison α) :
    Nonempty (Iso α (LieModels.Triality.amalgam
      (_root_.Triality.Standard.binaryParameters 1 Nat.zero_lt_one))) := by
  have hne := unequal_endpoints hl hr
  cases hc with
  | linear F m hm hF he =>
    have hh := linear_equal F
    rcases he with he | he <;> obtain ⟨e⟩ := he
    · exact (hne ((Nat.card_congr e.left.toEquiv).trans
        (hh.trans (Nat.card_congr e.right.toEquiv).symm))).elim
    · exact (hne ((Nat.card_congr e.left.toEquiv).trans
        (hh.symm.trans (Nat.card_congr e.right.toEquiv).symm))).elim
  | symplectic F m hm hF he =>
    have hh := Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.card_pointParabolic_eq_card_planeParabolic (F := F)
    rcases he with he | he <;> obtain ⟨e⟩ := he
    · exact (hne ((Nat.card_congr e.left.toEquiv).trans
        (hh.trans (Nat.card_congr e.right.toEquiv).symm))).elim
    · exact (hne ((Nat.card_congr e.left.toEquiv).trans
        (hh.symm.trans (Nat.card_congr e.right.toEquiv).symm))).elim
  | g2 F he =>
    have hh := g2_equal F
    rcases he with he | he <;> obtain ⟨e⟩ := he
    · exact (hne ((Nat.card_congr e.left.toEquiv).trans
        (hh.trans (Nat.card_congr e.right.toEquiv).symm))).elim
    · exact (hne ((Nat.card_congr e.left.toEquiv).trans
        (hh.symm.trans (Nat.card_congr e.right.toEquiv).symm))).elim
  | triality m hm he => exact triality_selected hr m hm he
  | ree m he => exact (not_ree hr h7 m he).elim
  | unitary m hm he =>
    let j := inclusion (LieModels.UnitaryFour.L2_le_planeParabolic m hm)
    have hj := inclusion_injective (LieModels.UnitaryFour.L2_le_planeParabolic m hm)
    rcases he with he | he <;> obtain ⟨e⟩ := he
    · exact (no_unitary_plane (Or.inr hQR) m hm
        (e.right.symm.toMonoidHom.comp j) (e.right.symm.injective.comp hj)).elim
    · exact (no_unitary_plane (Or.inl hQL) m hm
        (e.left.symm.toMonoidHom.comp j) (e.left.symm.injective.comp hj)).elim
  | unitaryExtension m hm he =>
    let j := planeExtensionEmbedding m hm
    have hj := planeExtensionEmbedding_injective m hm
    rcases he with he | he <;> obtain ⟨e⟩ := he
    · exact (no_unitary_plane (Or.inr hQR) m hm
        (e.right.symm.toMonoidHom.comp j) (e.right.symm.injective.comp hj)).elim
    · exact (no_unitary_plane (Or.inl hQL) m hm
        (e.left.symm.toMonoidHom.comp j) (e.left.symm.injective.comp hj)).elim
  | unitaryFive N he =>
    have hj : N.overlap.relIndex N.rightParabolic = 17 := N.overlap_rightParabolic_index
    rcases he with he | he <;> obtain ⟨e⟩ := he
    · have hi := hr
      rw [Nat.card_congr e.right.toEquiv, Nat.card_congr e.middle.toEquiv] at hi
      have hi' : N.overlap.relIndex N.rightParabolic = 3 :=
        relIndex_of_cards inf_le_right hi
      omega
    · have hi := hl
      rw [Nat.card_congr e.left.toEquiv, Nat.card_congr e.middle.toEquiv] at hi
      have hi' : N.overlap.relIndex N.rightParabolic = 9 :=
        relIndex_of_cards inf_le_right hi
      omega
  | exceptional c he =>
    rcases he with he | he
    · exact (not_exceptional h7 c he).elim
    · exact (not_exceptional h7 c he).elim

end CFSG.Quasithin.Chapter14.Section02.EightLargeParabolic.Catalogue
