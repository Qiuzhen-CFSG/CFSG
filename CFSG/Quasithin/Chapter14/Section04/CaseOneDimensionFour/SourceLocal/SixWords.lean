module
public import CFSG.Quasithin.Chapter14.Section04.CaseOneDimensionFour.SourceLocal.SixCoordinates
public import Theory.SpecificGroups.BinaryFour.SplitBlockPair.Enlarged.Words

/-!
# The finite-word obstruction in the actual enlarged action

The three representative cubics each produce an element of order seven fixing
the marked point. Conjugating an actor group by a coordinate change preserving
the marked point retains the order bound 4608; preserving the parabolic retains
the column cubic needed by the words. The same argument excludes the inverse
representatives.

Applying this to the literal six-dimensional source transport leaves only
classification of its rotating cubic. This finite normal-form assertion is
not assumed or claimed here. Its proof, local-data construction, and final
application remain with qt-d-14414-g2-source. Universal I.4.5 remains with
qt-i45-g2-recognition, and qt-d-14414-source retains the earlier-source
premises and final 14.4.14 assembly.

Source: Aschbacher–Smith, proof of 14.4.4–5, printed pp.1007–1008.
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter14.Section04.CaseOneDimensionFour
open Subgroup

/-- Coordinate changes needed by the remaining finite census. They must
preserve the parabolic and marked point simultaneously. -/
def SixCanonical (q : MulAut BinarySixSplitPair.E) : Prop :=
  ∃ d : MulAut BinarySixSplitPair.E,
    d BinarySixSplitPair.point = BinarySixSplitPair.point ∧
    BinarySixSplitPair.parabolic.map (MulAut.conj d).toMonoidHom = BinarySixSplitPair.parabolic ∧
    (BinarySixSplitPair.permAction (d*q*d⁻¹) = EnlargedSwappingTable.q1 ∨
     BinarySixSplitPair.permAction (d*q*d⁻¹) = EnlargedSwappingTable.q2 ∨
     BinarySixSplitPair.permAction (d*q*d⁻¹) = EnlargedSwappingTable.q3 ∨
     BinarySixSplitPair.permAction (d*q*d⁻¹)⁻¹ = EnlargedSwappingTable.q1 ∨
     BinarySixSplitPair.permAction (d*q*d⁻¹)⁻¹ = EnlargedSwappingTable.q2 ∨
     BinarySixSplitPair.permAction (d*q*d⁻¹)⁻¹ = EnlargedSwappingTable.q3)

/-- The finite words exclude every representative under any simultaneous
change of coordinates preserving the parabolic and marked point. -/
theorem six_no_canonical (J : Subgroup (MulAut BinarySixSplitPair.E))
    (q : MulAut BinarySixSplitPair.E) (hp : BinarySixSplitPair.parabolic ≤ J) (hq : q ∈ J)
    (hb : ∀ w ∈ J, w BinarySixSplitPair.point=BinarySixSplitPair.point → orderOf w ∣ 4608) :
    ¬ SixCanonical q := by
  rintro ⟨d,hd,hpar,he⟩
  let c := MulAut.conj d
  let J' := J.map c.toMonoidHom
  have hp' : BinarySixSplitPair.parabolic ≤ J' := by
    rw [←hpar]
    exact map_mono hp
  have hq' : d*q*d⁻¹ ∈ J' := ⟨q,hq,rfl⟩
  have hb' : ∀ w ∈ J', w BinarySixSplitPair.point=BinarySixSplitPair.point → orderOf w ∣ 4608 := by
    rintro _ ⟨w,hw,rfl⟩ hfix
    change orderOf (c w) ∣ 4608
    rw [c.orderOf_eq]
    apply hb w hw
    have hdi : d⁻¹ BinarySixSplitPair.point = BinarySixSplitPair.point := by
      apply d.injective
      simpa only [MulAut.inv_apply,MulEquiv.apply_symm_apply] using hd.symm
    have hh : d (w (d⁻¹ BinarySixSplitPair.point)) = BinarySixSplitPair.point := hfix
    rw [hdi] at hh
    exact d.injective (hh.trans hd.symm)
  let f := BinarySixSplitPair.permAction
  let K := J'.map f
  have hpk : EnlargedSwappingTable.p ∈ K := by
    rw [←EnlargedSwappingTable.parabolic_cubic_label]
    apply mem_map.mpr
    refine ⟨_,hp' ?_,rfl⟩
    exact ⟨BinaryFourSplitPair.columnCubic,subset_closure (by simp),rfl⟩
  have hbk : ∀ w ∈ K, w 2=2 → orderOf w ∣ 4608 := by
    rintro _ ⟨w,hw,rfl⟩ hfix
    rw [orderOf_injective f BinarySixSplitPair.permAction_injective]
    apply hb' w hw
    apply BinarySixSplitPair.labels.injective
    rw [←BinarySixSplitPair.permAction_apply,BinarySixSplitPair.labels_point]
    exact hfix
  obtain ⟨h1,h2,h3⟩ := EnlargedSwappingTable.no_representative K hpk hbk
  have hmem : f (d*q*d⁻¹) ∈ K := ⟨_,hq',rfl⟩
  rcases he with he | he | he | he | he | he
  · exact h1 (he ▸ hmem)
  · exact h2 (he ▸ hmem)
  · exact h3 (he ▸ hmem)
  · exact h1 (he ▸ K.inv_mem hmem)
  · exact h2 (he ▸ K.inv_mem hmem)
  · exact h3 (he ▸ K.inv_mem hmem)

/-- After the actual ambient transport and the finite words, only
classification of the displayed rotating cubics remains. -/
theorem six_noncanonical_of_source (h : SixDimensionalSwappingCase) :
    ∃ q : MulAut BinarySixSplitPair.E, BinarySixSplitPair.RotatingCubic q ∧ ¬ SixCanonical q := by
  obtain ⟨J,q,hp,hq,hr,hb⟩ := h
  exact ⟨q,hr,six_no_canonical J q hp hq hb⟩

open Theory.GroupTheory
open scoped IsMulCommutative
open Chapter12.Section02 Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter14.Section03.CaseOneSource CaseOneGeometry
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- The original local constructor reduces to classification of rotating
cubics in the fixed six-coordinate model, with the finite witnesses discharged. -/
theorem source_localData_or_noncanonical_cubic
    (d : Counterexample T L) (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (previous : EarlierSetupResults KnownSimple.IsKnownSimple.{u})
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U)
    (hZ : F.ZU = F.Vi 1) (hcard : Nat.card F.U = 32) :
    Nonempty (SourceLocalData L F) ∨
      ∃ q : MulAut BinarySixSplitPair.E, BinarySixSplitPair.RotatingCubic q ∧ ¬ SixCanonical q := by
  rcases source_localData_or_six_dimensional_swapping d earlier hq chosen previous F hne hZ hcard with
    hd | hs
  · exact Or.inl hd
  · exact Or.inr (six_noncanonical_of_source hs)

/-- Literal I.4.5 configuration application of the finite-word exclusions. -/
theorem source_configuration_or_noncanonical_cubic
    (d : Counterexample T L) (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (previous : EarlierSetupResults KnownSimple.IsKnownSimple.{u})
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U)
    (hZ : F.ZU = F.Vi 1) (hcard : Nat.card F.U = 32) :
    Nonempty (DimensionFour.G2ThreeConfiguration G) ∨
      ∃ q : MulAut BinarySixSplitPair.E, BinarySixSplitPair.RotatingCubic q ∧ ¬ SixCanonical q := by
  rcases source_localData_or_noncanonical_cubic d earlier hq chosen previous F hne hZ hcard with
    hd | hs
  · obtain ⟨localData⟩ := hd
    exact Or.inl (configuration_of_source_local d earlier hq chosen previous.structural
      previous.alternatives F hne hZ hcard localData)
  · exact Or.inr hs

end CFSG.Quasithin.Chapter14.Section04.CaseOneDimensionFour
