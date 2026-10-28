module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.LocalFactorEmbedding
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.ReeSource.SuzukiCoordinates

/-!
# The original Suzuki root group and its local cover

The actual quotient Sylow-normalizer cosets have degree one more than the
Sylow order. The same original endpoint marking identifies these cosets
with the split panel. Thus the canonical simple root's injective projection
onto the original quotient Sylow is surjective. For a perfect original
factor, LocalFactorEmbedding identifies its two-root-generated group with
the original Suzuki quotient, without a (2B) premise or a multiplier bound.

Perfectness excludes parameter zero by proof; simplicity and centerlessness
then make the original root group's panel action faithful. The root-count
and degree-nine exclusion themselves include parameter zero and need no
perfectness. Once source (2B) is supplied, the same literal projection
identifies the entire local permutation group and the original whole-root
cover with the Suzuki model. The representative formulas retain the
original factor lift and two-core quotient map.

Source: Fong--Seitz I (2A)--(2B), pp.7--9, and (5C), pp.25--26;
Huppert--Blackburn III, XI.3.3 and XI.3.6; AS F.1.1--3, pp.259--260.
This discharges the Suzuki local-model witness on the perfect-factor
branch. It does not prove the remaining nonlinear (2B) containment, the
nonperfect local recognition, full endpoint recognition, or row selection.
-/

public noncomputable section
open Subgroup Theory.GroupTheory BenderSuzuki.MatrixGroups
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.MarkedLocal
variable {G X : Type*} [Group G] [Group X]
  {L : Fin 2 → Subgroup G} {S : Subgroup G} {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P)
  (e : RankTwoAmalgam.Iso
    (RankTwoAmalgam.ofSubgroups (parabolic L S 0)
      (parabolic L S 0 ⊓ parabolic L S 1) (parabolic L S 1) inf_le_left inf_le_right)
    Q.standardAmalgam)
  (h : HypothesisF11 L S) (split : SplitData Q.tits) (i : Fin 2)
  [Finite (L i)] (hp : Group.IsPerfect (L i))
  (T : Sylow 2 (L i)) (hT : (T : Subgroup (L i)).map (L i).subtype = S ⊓ L i)
  {m : ℕ} (μ : ((L i) ⧸ pCore 2 (L i)) ≃* SuzukiMatrixGroup m)

def suzukiModelSylow : Sylow 2 (SuzukiMatrixGroup m) :=
  (quotientSylow T).mapSurjective (f := μ.toMonoidHom) μ.surjective

def suzukiSylowEquiv : quotientSylow T ≃* suzukiModelSylow i T μ :=
  (quotientSylow T : Subgroup ((L i) ⧸ pCore 2 (L i))).equivMapOfInjective
    μ.toMonoidHom μ.injective

include e h hT μ in
theorem suzuki_simpleRoot_card_eq_quotientSylow :
    Nat.card (simpleRoot Q split i) = Nat.card (quotientSylow T) := by
  have he := Nat.card_congr ((localBorelPanel Q e h i).symm.trans
    (localBorelModelCosetEquiv (L i) S T hT μ))
  have hindex := singleton_parabolic_root_index Q split i
  change Nat.card (Panel Q i) = 1 + Nat.card (simpleRoot Q split i) at hindex
  have hm := ReeSource.suzuki_normalizer_index m (suzukiModelSylow i T μ)
  change Nat.card (SuzukiMatrixGroup m ⧸ sylowNormalizer (suzukiModelSylow i T μ)) = _ at hm
  have hs := Nat.card_congr (suzukiSylowEquiv i T μ).toEquiv
  have he' : 1 + Nat.card (simpleRoot Q split i) =
      1 + Nat.card (suzukiModelSylow i T μ) := hindex.symm.trans (he.trans hm)
  omega

include e h hT μ in
theorem suzuki_simpleRoot_card :
    Nat.card (simpleRoot Q split i) = (2 ^ (2*m+1)) ^ 2 := by
  rw [suzuki_simpleRoot_card_eq_quotientSylow Q e h split i T hT μ,
    Nat.card_congr (suzukiSylowEquiv i T μ).toEquiv,
    Nat.card_congr ((suzukiModelSylow i T μ).equiv (ReeSource.matrixRootSylow m)).toEquiv]
  rw [ReeSource.matrixRootSylow_carrier, ReeSource.matrixRoot_card]

include e h split hT μ in
theorem suzuki_panel_card_ne_nine : Nat.card (Panel Q i) ≠ 9 := by
  have he := singleton_parabolic_root_index Q split i
  change Nat.card (Panel Q i) = 1 + Nat.card (simpleRoot Q split i) at he
  rw [suzuki_simpleRoot_card Q e h split i T hT μ] at he
  intro hnine
  rw [hnine] at he
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · norm_num at he
  · have hq : 8 ≤ 2 ^ (2*m+1) :=
      (by norm_num : 8 = (2:ℕ)^3) ▸ Nat.pow_le_pow_right (by decide) (by omega)
    nlinarith

include μ in
theorem suzuki_simpleRootSylowProjection_surjective :
    Function.Surjective (simpleRootSylowProjection Q e h split i hp T hT) :=
  ((Nat.bijective_iff_injective_and_card _).mpr
    ⟨simpleRootSylowProjection_injective Q e h split i hp T hT,
      suzuki_simpleRoot_card_eq_quotientSylow Q e h split i T hT μ⟩).2

def suzukiRankOneEquiv : rankOne Q split i ≃* SuzukiMatrixGroup m :=
  (rankOneQuotientEquiv Q e h split i hp T hT
    (suzuki_simpleRootSylowProjection_surjective Q e h split i hp T hT μ)).trans μ

@[simp] theorem suzukiRankOneEquiv_apply (r : rankOne Q split i) :
    suzukiRankOneEquiv Q e h split i hp T hT μ r =
      μ (QuotientGroup.mk' (pCore 2 (L i)) (rankOneLift Q e h split i hp r)) := by
  rw [suzukiRankOneEquiv, MulEquiv.trans_apply, rankOneQuotientEquiv_apply]

@[simp] theorem suzukiRankOneEquiv_simpleRoot (r : simpleRoot Q split i) :
    suzukiRankOneEquiv Q e h split i hp T hT μ
      (inclusion (show simpleRoot Q split i ≤ rankOne Q split i from le_sup_left) r) =
      μ (simpleRootProjection Q e h split i hp r) := by
  rw [suzukiRankOneEquiv, MulEquiv.trans_apply, rankOneQuotientEquiv_projection,
    rankOneProjection_simpleRoot]

omit [Finite (L i)] in
include hp μ in
theorem suzuki_parameter_pos : 0 < m := by
  let : Group.IsPerfect (L i) := hp
  let : Group.IsPerfect (SuzukiMatrixGroup m) :=
    Group.IsPerfect.ofSurjective (f := μ.toMonoidHom) μ.surjective
  exact suzuki_parameter_pos_of_perfect m

include e h hp hT μ in
theorem suzuki_root_local_projection_injective :
    Function.Injective (RootLocalCover.projection Q split i) := by
  let a := suzukiRankOneEquiv Q e h split i hp T hT μ
  let : IsSimpleGroup (SuzukiMatrixGroup m) :=
    (BenderSuzuki.External.huppert_blackburn_XI_3_6 m (suzuki_parameter_pos i hp μ)).1
  have hz : center (SuzukiMatrixGroup m) = ⊥ := by
    rcases (inferInstance : (center (SuzukiMatrixGroup m)).Normal).eq_bot_or_eq_top with hz | hz
    · exact hz
    · exfalso
      apply BenderSuzuki.External.suzukiMatrixGroup_not_isSolvable m (suzuki_parameter_pos i hp μ)
      exact Group.isSolvable_of_comm (fun x y => by
        have hx : x ∈ center (SuzukiMatrixGroup m) := hz ▸ mem_top x
        exact (mem_center_iff.mp hx y).symm)
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply eq_bot_iff.mpr
  intro r hr
  have hc := MulEquivClass.apply_mem_center a (RootLocalCover.projection_ker_central Q split i hr)
  change a r ∈ center (SuzukiMatrixGroup m) at hc
  rw [hz, mem_bot] at hc
  exact a.injective (hc.trans a.map_one.symm)

def suzukiLocalEquiv (hV : simpleRemainder Q split i ≤ localKernel Q i) :
    localGroup Q split i ≃* SuzukiMatrixGroup m :=
  (MulEquiv.ofBijective (RootLocalCover.projection Q split i)
    ⟨suzuki_root_local_projection_injective Q e h split i hp T hT μ,
      (RootLocalCover.central_odd_cover Q split i hV).1⟩).symm.trans
        (suzukiRankOneEquiv Q e h split i hp T hT μ)

@[simp] theorem suzukiLocalEquiv_projection
    (hV : simpleRemainder Q split i ≤ localKernel Q i) (r : rankOne Q split i) :
    suzukiLocalEquiv Q e h split i hp T hT μ hV (RootLocalCover.projection Q split i r) =
      μ (QuotientGroup.mk' (pCore 2 (L i)) (rankOneLift Q e h split i hp r)) := by
  let a := MulEquiv.ofBijective (RootLocalCover.projection Q split i)
    ⟨suzuki_root_local_projection_injective Q e h split i hp T hT μ,
      (RootLocalCover.central_odd_cover Q split i hV).1⟩
  change suzukiRankOneEquiv Q e h split i hp T hT μ (a.symm (a r)) = _
  rw [MulEquiv.symm_apply_apply, suzukiRankOneEquiv_apply]

def originalSuzukiRankOneEquiv : originalRankOne Q e split i ≃* SuzukiMatrixGroup m :=
  (originalRankOneEquiv Q e split i).trans (suzukiRankOneEquiv Q e h split i hp T hT μ)

@[simp] theorem originalSuzukiRankOneEquiv_projection
    (hV : simpleRemainder Q split i ≤ localKernel Q i) (r : originalRankOne Q e split i) :
    originalSuzukiRankOneEquiv Q e h split i hp T hT μ r =
      suzukiLocalEquiv Q e h split i hp T hT μ hV (originalRootProjection Q e split i r) := by
  have hr : originalRootProjection Q e split i r =
      RootLocalCover.projection Q split i (originalRankOneEquiv Q e split i r) := by
    apply Subtype.ext
    rw [originalRootProjection_apply, RootLocalCover.projection_apply]
  rw [hr]
  change suzukiRankOneEquiv Q e h split i hp T hT μ (originalRankOneEquiv Q e split i r) = _
  rw [suzukiLocalEquiv_projection, suzukiRankOneEquiv_apply]

include h hp hT μ in
theorem suzuki_originalRootProjection_injective :
    Function.Injective (originalRootProjection Q e split i) := by
  intro r s hrs
  apply (originalRankOneEquiv Q e split i).injective
  apply suzuki_root_local_projection_injective Q e h split i hp T hT μ
  apply Subtype.ext
  have he := congrArg Subtype.val hrs
  simpa only [originalRootProjection_apply, RootLocalCover.projection_apply] using he

include e h hp hT μ in
theorem suzuki_original_root_kernel_trivial :
    (originalPanelKernel (L := L) (S := S) i).subgroupOf
      (originalRankOne Q e split i) = ⊥ := by
  rw [← originalRootProjection_ker Q e h split i]
  exact (MonoidHom.ker_eq_bot_iff _).mpr
    (suzuki_originalRootProjection_injective Q e h split i hp T hT μ)

def originalSuzukiCoverEquiv (hV : simpleRemainder Q split i ≤ localKernel Q i) :
    letI := originalRadicalInClosure_normal Q e h split i
    (originalLocalClosure Q e split i ⧸ originalRadicalInClosure Q e split i) ≃*
      SuzukiMatrixGroup m := by
  letI := originalRadicalInClosure_normal Q e h split i
  exact (originalRootCoverEquiv Q e h split i hV).symm.trans
    (originalSuzukiRankOneEquiv Q e h split i hp T hT μ)

@[simp] theorem originalSuzukiCoverEquiv_mk
    (hV : simpleRemainder Q split i ≤ localKernel Q i) (r : originalRankOne Q e split i) :
    letI := originalRadicalInClosure_normal Q e h split i
    originalSuzukiCoverEquiv Q e h split i hp T hT μ hV
      (QuotientGroup.mk' (originalRadicalInClosure Q e split i)
        (inclusion (originalRankOne_le_localClosure Q e split i) r)) =
      μ (QuotientGroup.mk' (pCore 2 (L i))
        (rankOneLift Q e h split i hp (originalRankOneEquiv Q e split i r))) := by
  let := originalRadicalInClosure_normal Q e h split i
  rw [← originalRootCoverEquiv_apply Q e h split i hV r]
  change originalSuzukiRankOneEquiv Q e h split i hp T hT μ
    ((originalRootCoverEquiv Q e h split i hV).symm
      (originalRootCoverEquiv Q e h split i hV r)) = _
  rw [MulEquiv.symm_apply_apply]
  exact suzukiRankOneEquiv_apply Q e h split i hp T hT μ _

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.MarkedLocal
