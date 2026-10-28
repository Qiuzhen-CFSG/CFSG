module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanGlobalPrimeZeroCoreSourceProfiles
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanGlobalPrimeZeroCoreExceptional
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.OriginalExtension.NativeRestoration

/-!
# The literal reduced diagram of the Cartan prime pair

The left local group DS contains all of S. The local-Sylow containment in
O₂ of the full Borel therefore makes the F.1.1 reduction stationary: its
S₀ is the original S, and both endpoints and the whole overlap agree.
The comparison below is the identity on ambient elements and preserves
both inclusion squares. In particular a bound on this literal S₀ is a
bound on S; no unrelated minimal completion or ambient Sylow is used.

Small type-only quotients are transported on the actual reduced right
endpoint. Their solvability contradicts the selected R without an
amalgam recognition or an actual-component-of-H hypothesis.
Source: Aschbacher–Smith F.1.9–12, pp.261–264, and 5.2.2, pp.647–648;
DGS (15.1), p.226. Exhaustive marked classification remains independent.
-/

public noncomputable section
open Subgroup Theory.GroupTheory RankTwoAmalgam
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Prime
open ChapterF.Source ChapterF.Source.SuzukiContainment
open ChapterF.Source.DGS85.OriginalExtension
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L W H A B D R : Subgroup G} {n p : ℕ}
  (d : LocalData T L H B D R) (h : Input KnownSimple.IsKnownSimple T L W n)
  (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
  (c : CartanPair T L H A B) (hd : CartanPrimeActor A H p D)
  (hz : (generated L H D R).pCoreIn 2 = ⊥)

include d h hH c hd hz in
/-- The reduction uses the full original Borel, so its Sylow is exactly S. -/
theorem LocalData.zeroCore_reducedSylow_eq_sourceS :
    reducedSylow ![D ⊔ Global.sourceS L H,R] (Global.sourceS L H) =
      Global.sourceS L H := by
  change (commonBorel ![D ⊔ Global.sourceS L H,R] (Global.sourceS L H)).pCoreIn 2 = _
  rw [d.zeroCore_commonBorel hz]
  exact d.zeroCore_borel_core_eq_sourceS h hH c hd hz

include d h hH c hd hz in
/-- Both reduced endpoints and the entire reduced Borel are the original
subgroups, including the original odd Hall intersection B ∩ R. -/
theorem LocalData.zeroCore_reduced_groups :
    let S₀ := reducedSylow ![D ⊔ Global.sourceS L H,R] (Global.sourceS L H)
    parabolic ![D ⊔ Global.sourceS L H,R] S₀ 0 =
      (D ⊔ Global.sourceS L H) ⊔ (B ⊓ R) ∧
    commonBorel ![D ⊔ Global.sourceS L H,R] S₀ = Global.sourceS L H ⊔ (B ⊓ R) ∧
    parabolic ![D ⊔ Global.sourceS L H,R] S₀ 1 = R ⊔ Global.sourceS L H := by
  dsimp only
  rw [d.zeroCore_reducedSylow_eq_sourceS h hH c hd hz]
  exact ⟨d.zeroCore_parabolic_zero,d.zeroCore_commonBorel hz,d.parabolic_one hz⟩

include d h hH c hd hz in
/-- The source reduction has no extra whole-Borel index on this prime pair. -/
theorem LocalData.zeroCore_reduced_borel_index :
    (commonBorel ![D ⊔ Global.sourceS L H,R]
      (reducedSylow ![D ⊔ Global.sourceS L H,R] (Global.sourceS L H))).relIndex
      (commonBorel ![D ⊔ Global.sourceS L H,R] (Global.sourceS L H)) = 1 := by
  rw [d.zeroCore_reducedSylow_eq_sourceS h hH c hd hz]
  exact relIndex_self _

include d h hH c hd hz in
/-- The complete original inclusion diagram, with both squares, transports
to the literal reduced diagram by the identity on ambient elements. -/
@[expose] def LocalData.zeroCoreReducedIso :
    Iso (zeroCoreAmalgam L H B D R)
      (reducedAmalgam ![D ⊔ Global.sourceS L H,R] (Global.sourceS L H)) :=
  let hg := d.zeroCore_reduced_groups h hH c hd hz
  NativeRestoration.subgroupCongrIso _ _ _ _ hg.1.symm hg.2.1.symm hg.2.2.symm

include d h hH c hd hz in
/-- Neither endpoint nor any element of the full middle is changed. -/
theorem LocalData.zeroCoreReducedIso_values :
    (∀ x, ((d.zeroCoreReducedIso h hH c hd hz).left x : G) = x) ∧
    (∀ x, ((d.zeroCoreReducedIso h hH c hd hz).middle x : G) = x) ∧
    (∀ x, ((d.zeroCoreReducedIso h hH c hd hz).right x : G) = x) :=
  ⟨fun _ => rfl,fun _ => rfl,fun _ => rfl⟩

include d h hH c hd hz in
/-- The original strict lower bound applies to this literal reduced Sylow. -/
theorem LocalData.zeroCore_reducedSylow_card_gt :
    2^(3*n) < Nat.card (reducedSylow ![D ⊔ Global.sourceS L H,R] (Global.sourceS L H)) := by
  rw [d.zeroCore_reducedSylow_eq_sourceS h hH c hd hz]
  exact d.sourceS_card_gt h hH c hd

include d h hH c hd hz in
/-- A solvable full reduced right quotient is impossible. This transports the
actual endpoint quotient, not the intrinsic quotient of an unrelated factor. -/
theorem LocalData.zeroCore_no_solvable_reduced_parabolic_quotient
    {X : Type*} [Group X] [Group.IsSolvable X]
    (e : (parabolic ![D ⊔ Global.sourceS L H,R]
      (reducedSylow ![D ⊔ Global.sourceS L H,R] (Global.sourceS L H)) 1 ⧸
        pCore 2 (parabolic ![D ⊔ Global.sourceS L H,R]
          (reducedSylow ![D ⊔ Global.sourceS L H,R] (Global.sourceS L H)) 1)) ≃* X) : False := by
  rw [d.zeroCore_reducedSylow_eq_sourceS h hH c hd hz] at e
  let P := parabolic ![D ⊔ Global.sourceS L H,R] (Global.sourceS L H) 1
  let : Group.IsNilpotent (pCore 2 P) := pCore_isNilpotent
  exact d.right_parabolic_not_solvable hz
    ((Group.isSolvable_iff_subgroup_quotient (pCore 2 P)).mpr
      ⟨inferInstance,Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective⟩)

include d h hH c hd hz in
/-- The small binary type clauses are eliminated using their literal right
quotient alone. No type-to-isomorphism upgrade is used. -/
theorem LocalData.zeroCore_not_reduced_small_type :
    let P := parabolic ![D ⊔ Global.sourceS L H,R]
      (reducedSylow ![D ⊔ Global.sourceS L H,R] (Global.sourceS L H)) 1
    ¬ (ClassicalGroup.IsPSL (P ⧸ pCore 2 P) 2 2 ∨
      Nonempty ((P ⧸ pCore 2 P) ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup 0) ∨
      Nonempty ((P ⧸ pCore 2 P) ≃* DihedralGroup 5)) := by
  dsimp only
  intro he
  rcases he with he | he | he
  · obtain ⟨F,_,_,hF,⟨e⟩⟩ := he
    let := Theory.PSL2.OuterSolvable.isSolvable_of_card_two hF
    exact d.zeroCore_no_solvable_reduced_parabolic_quotient h hH c hd hz e
  · let := BenderSuzuki.MatrixGroups.suzukiZero_isSolvable
    exact d.zeroCore_no_solvable_reduced_parabolic_quotient h hH c hd hz he.some
  · let := GLS3.Chapter5.dihedralGroup_isSolvable 5
    exact d.zeroCore_no_solvable_reduced_parabolic_quotient h hH c hd hz he.some

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Prime

public noncomputable section
open Subgroup Theory.GroupTheory RankTwoAmalgam
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Prime
open ChapterF.Source ChapterF.Source.SuzukiContainment
open ChapterF.Source.DGS85.OriginalExtension
variable {G X : Type*} [Group G] [Finite G] [Group X]
  {T : Sylow 2 G} {L W H A B D R : Subgroup G} {n p : ℕ}
  (d : LocalData T L H B D R) (h : Input KnownSimple.IsKnownSimple T L W n)
  (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
  (c : CartanPair T L H A B) (hd : CartanPrimeActor A H p D)
  (hz : (generated L H D R).pCoreIn 2 = ⊥)
  (f : FaithfulCompletion
    (reducedAmalgam ![D ⊔ Global.sourceS L H,R] (Global.sourceS L H)) (G := X))
  (hk : PreservesCompletionKernel (d.hypothesisF11 h hH c hd hz) f)

include d h hH c hd hz in
/-- In any compatible restored completion, the full original Borel already
acts by inner automorphisms. This is an extension restriction, independent
of recognition of the completion as a particular model. -/
theorem LocalData.zeroCore_completionAction_inner
    (ho : f.left.range ⊓ f.right.range = f.middle.range)
    (hN : ∀ i, normalizer ((completionEndpoint f i).range : Set X) =
      (completionEndpoint f i).range) :
    (completionAction (d.hypothesisF11 h hH c hd hz) f hk).range ≤
      MulAut.innerSubgroup X := by
  rintro _ ⟨b,rfl⟩
  apply (completionAction_mem_inner_iff (d.hypothesisF11 h hH c hd hz) f hk ho hN b).mpr
  rw [d.zeroCore_reducedSylow_eq_sourceS h hH c hd hz]
  exact b.property

include d h hH c hd hz in
/-- The actual restored automorphism extension has no outer enlargement;
the statement concerns the same completion and full original Borel. -/
theorem LocalData.zeroCore_automorphismExtension_eq_inner
    (ho : f.left.range ⊓ f.right.range = f.middle.range)
    (hN : ∀ i, normalizer ((completionEndpoint f i).range : Set X) =
      (completionEndpoint f i).range) :
    automorphismExtension (d.hypothesisF11 h hH c hd hz) f hk = MulAut.innerSubgroup X :=
  sup_eq_left.mpr (d.zeroCore_completionAction_inner h hH c hd hz f hk ho hN)

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Prime
