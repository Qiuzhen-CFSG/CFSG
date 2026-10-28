module
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.NonblockSecondaryCoreEnlargement.SourceFrameRadical
public import Theory.SpecificGroups.PSL3.RadicalPerfectFrame
public import Theory.SpecificGroups.PSL3.MovedTwoGroups
public import Theory.SpecificGroups.PSL3.OuterSolvable.Coverage

/-!
# The literal secondary radical in a projective local frame

Core movement and the explicit generation premise put the original radical
image inside the inner component. Radicality and normalizer control identify
that image with a root plane, simultaneously identifying the original perfect
secondary image with the corresponding full local subgroup.

Source: Aschbacher–Smith, original 4.3.14–16, printed pp.617–618.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock.EndgameSieve
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {c : SourceConfiguration T L} {n : ℕ}
namespace SecondaryActionData

/-- Core movement and whole-radical generation put the literal image in Inn. -/
theorem binary_linear_radical_le_inner_of_mark (s : SecondaryActionData c n)
    (hg : ActionGeneration s) {F : Type*} [Field F] [Finite F] [CharP F 2]
    {f : ℕ} (hf : 2≤f) (hF : Nat.card F = 2^f)
    (e : componentImage s ≃* PSL(3,F)) :
    radicalImage s ≤ componentImage s := by
  let := s.normal
  let := s.quasisimple
  let a := (centralQuotientEquiv s).trans e
  let k := MulAut.centralQuotientAction a
  have hi : coreImage s ≤ componentImage s := by
    rw [componentImage_eq_inner]
    have hmoved : ⁅(coreImage s).map k, (torusImage s).map k⁆ = (coreImage s).map k := by
      rw [←map_commutator,coreImage_moved]
    have hp := (SourceImages.radical_geometry c s.component s.radical_normalizer).1
    have hQ : IsPGroup 2 (coreImage s) :=
      hp.to_le (SourceImages.radical_geometry c s.component s.radical_normalizer).2.1
    have hh := Matrix.PSL3.MovedTwoGroups.moved_twoGroup_le_inner_of_coverage
      (Matrix.PSL3.OuterSolvable.standard_eq_top_of_two_power_card F (by omega) hF)
      _ _ (hQ.map k) hmoved
    intro x hx
    obtain ⟨y,hy⟩ := hh (mem_map_of_mem k hx)
    obtain ⟨z,hz⟩ := (MulAut.centralQuotientAction_inner_iff a x).mp ⟨y,hy.symm⟩
    exact ⟨z,hz.symm⟩
  rw [←hg]
  apply sup_le hi
  rw [componentImage_eq_inner]
  exact (Subgroup.commutator_mono le_top
    (by rw [←componentImage_eq_inner]
        exact secondaryImage_le_componentImage s)).trans
    (Subgroup.commutator_le_right _ _)

/-- The model predicate supplies the same inner-containment conclusion. -/
theorem binary_linear_radical_le_inner (s : SecondaryActionData c n)
    (hg : ActionGeneration s) {f : ℕ} (hf : 2≤f)
    (hm : ClassicalGroup.IsPSL (componentImage s) 3 (2^f)) :
    radicalImage s ≤ componentImage s := by
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
  let : CharP F 2 := Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card hF
  exact binary_linear_radical_le_inner_of_mark s hg hf hF e

/-- Every given inner-component marking admits one frame for the radical and
secondary image, retaining their literal inclusions in that component. -/
theorem root_local_frame (s : SecondaryActionData c n)
    (D : Chapter12.Section02.ChosenModule T L V) (hg : ActionGeneration s)
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    {f : ℕ} (hf : 1<f) (hF : Nat.card F = 2^f)
    (e : componentImage s ≃* PSL(3,F)) :
    ∃ (a : MulAut PSL(3,F)) (b : Bool),
      ((radicalImage s).subgroupOf (componentImage s)).map
        (e.trans a).toMonoidHom = Matrix.PSL3.RootPlaneGeometry.rootPlane F b ∧
      ((secondaryImage s).subgroupOf (componentImage s)).map
        (e.trans a).toMonoidHom = Matrix.PSL3.LinearThree.OuterExtensions.localFactor F b := by
  let := s.normal
  have hRI := binary_linear_radical_le_inner_of_mark s hg (by omega : 2≤f) hF e
  have hXI := secondaryImage_le_componentImage s
  let I := componentImage s
  let X := secondaryImage s
  let R := radicalImage s
  let B := (X.subgroupOf I).map e.toMonoidHom
  let W := (R.subgroupOf I).map e.toMonoidHom
  let k := (subgroupOfEquivOfLe hXI).symm.trans
    ((X.subgroupOf I).equivMapOfInjective e.toMonoidHom e.injective)
  let : Group.IsPerfect X := SourceImages.secondary_perfect c s.component
    (s.secondary_le.trans (map_subtype_le _))
  let : Group.IsPerfect B := Group.IsPerfect.ofSurjective (f:=k.toMonoidHom) k.surjective
  have hB : B ≠ ⊥ := by
    intro he
    have hc : Nat.card X = 1 := (Nat.card_congr k.toEquiv).trans (by
      change Nat.card B=1
      rw [he]
      simp)
    exact SourceImages.secondaryImage_ne_bot c s.component s.secondary_le s.secondary_model
      (X.eq_bot_of_card_eq hc)
  have hW : W.IsPRadical 2 := (inner_radical s D hRI).map_equiv e
  have hBW : B ≤ normalizer (W : Set _) := by
    rw [show W = (R.subgroupOf I).map e.toMonoidHom from rfl,←map_equiv_normalizer_eq]
    apply map_mono
    intro x hx y
    exact (SourceImages.radical_geometry c s.component s.radical_normalizer).2.2.2.1 hx y.val
  have hWB : normalizer (W : Set _) ≤ normalizer (B : Set (PSL(3,F))) := by
    rw [show W = (R.subgroupOf I).map e.toMonoidHom from rfl,
      show B = (X.subgroupOf I).map e.toMonoidHom from rfl,
      ←map_equiv_normalizer_eq,←map_equiv_normalizer_eq]
    apply map_mono
    rw [←subgroupOf_normalizer_eq hRI,←subgroupOf_normalizer_eq hXI]
    intro x hx
    exact (localImageData s D).normalizer_control
      ⟨(show I ≤ ambientImage s from le_sup_left.trans le_sup_left) x.property,hx⟩
  obtain ⟨a,b,hR,hX⟩ :=
    Matrix.PSL3.LinearThree.RadicalNormalizer.projective_radical_perfect_root_frame
      W B hW hB hBW hWB hf hF
  have he : (e.trans a).toMonoidHom = a.toMonoidHom.comp e.toMonoidHom := by
    ext x
    rfl
  refine ⟨a,b,?_,?_⟩
  · rw [he,←Subgroup.map_map]
    exact hR
  · rw [he,←Subgroup.map_map]
    exact hX

end SecondaryActionData
end CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock.EndgameSieve
