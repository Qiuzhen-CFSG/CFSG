module
public import CFSG.Quasithin.ChapterF.Section05.ExceptionalLocal.FusionRoots
public import CFSG.Quasithin.ChapterF.Section01.GreenBook.LieModels.UnitaryFour.Sylow

/-!
# The literal Sylow subgroup of the binary graph extension

The extended upper subgroup has ordinary upper coordinates and one graph
coordinate, so its order is 128. The ambient model order makes it Sylow,
and restriction gives the same marked Sylow in the point endpoint.

For its center, a first-superdiagonal calculation excludes an outer element:
such an element would force every matrix-field scalar to be Frobenius fixed.
The remaining ordinary elements centralize the Heisenberg radical, whose
center has order two. The source completion transports this exact center
to the original point-root image, retaining the literal overlap map.

Source: Aschbacher--Smith F.4.29(7), F.4.33 and F.4.34, printed pp.290--291.
Ambient Sylow promotion and the graph-centralizer calculation are separate.
-/

@[expose] public noncomputable section
open Subgroup
namespace CFSG.Quasithin.ChapterF.Section05.ExceptionalLocal
open GreenBook.LieModels.UnitaryFour
open Theory.SpecificGroups.ClassicalUnitary
local notation "hn" => Nat.le_refl 1
local notation "U" => Extension.extendedUpper 1 hn
local notation "X" => Extension.ProjectiveExtension 1 hn

theorem extendedUpper_mem (a : X) : a ∈ U ↔ a.left ∈ upperProjective 1 hn := by
  constructor
  · rintro ⟨a,ha,rfl⟩
    exact ⟨a.left,ha,rfl⟩
  · rintro ⟨b,hb,he⟩
    refine ⟨⟨b,a.right⟩,hb,?_⟩
    exact SemidirectProduct.ext he rfl

def extendedUpperEquivProd : U ≃ upperProjective 1 hn × UnitaryFourOuter.C2 where
  toFun a := (⟨a.val.left,(extendedUpper_mem a.val).mp a.property⟩,a.val.right)
  invFun a := ⟨⟨a.1.val,a.2⟩,(extendedUpper_mem _).mpr a.1.property⟩
  left_inv _ := Subtype.ext (SemidirectProduct.ext rfl rfl)
  right_inv _ := rfl

theorem extendedUpper_card : Nat.card U = 128 := by
  rw [Nat.card_congr extendedUpperEquivProd, Nat.card_prod, upperProjective_card]
  change (2 ^ 1) ^ 6 * Nat.card (ZMod 2) = 128
  norm_num

def extendedUpperSylow : Sylow 2 X :=
  (IsPGroup.of_card (n := 7) extendedUpper_card).toSylow (by
    have he := (U).card_mul_index
    rw [extendedUpper_card, Extension.binary_extension_card] at he
    have hi : (U).index = 405 := by omega
    rw [hi]; decide)

theorem extendedUpper_le_overlap : U ≤ Extension.overlap 1 hn := by
  intro a ha
  exact (Extension.binary_mem_overlap a).mpr
    (upperProjective_le_overlap 1 hn ((extendedUpper_mem a).mp ha))

theorem extendedUpper_le_point : U ≤ Extension.point 1 hn := by
  have h := extendedUpper_le_overlap
  rw [← Extension.exact_overlap] at h
  exact le_trans h inf_le_left

def extendedPointSylow : Sylow 2 (Extension.point 1 hn) :=
  extendedUpperSylow.subtype extendedUpper_le_point

local notation "F" => MatrixField 1
local notation "σ" => fieldConj 1
local notation "hσ" => fieldConj_involutive 1 hn
local notation "UM" => UnitaryFourOuter.extendedUpper F σ hσ
open UnitaryFourFlag UnitaryFourPointLocal UnitaryFourSylow

private theorem matrix_center_right_one (a : UM) (ha : a ∈ center UM) :
    a.val.right = 1 := by
  rcases UnitaryFourOuter.c2_cases a.val.right with hh | hh
  · exact hh
  exfalso
  obtain ⟨t,ht⟩ := PointLocal.fieldConj_nontrivial 1 hn
  let r : RadicalCoordinates F σ := ⟨0,t,0,by simp⟩
  let b : UM := ⟨SemidirectProduct.inl (radicalElement F σ hσ r),
    radicalElement_mem_upper F σ hσ r⟩
  have he := congrArg (fun x : UM => x.val.left.val.val 0 1)
    (mem_center_iff.mp ha b)
  have haU : a.val.left ∈ upper F σ hσ := a.property
  obtain ⟨htri,hdiag⟩ := (mem_upper_iff_entries F σ hσ _).mp haU
  simp only [Subgroup.coe_mul, SemidirectProduct.mul_left] at he
  simp only [b, SemidirectProduct.left_inl, SemidirectProduct.right_inl,
    hh, map_one, MulAut.one_apply, UnitaryFourOuter.action_generator] at he
  change ((radicalElement F σ hσ r).val.val * a.val.left.val.val) 0 1 =
    (a.val.left.val.val * (UnitaryFourOuter.matrixAut F σ hσ
      (radicalElement F σ hσ r)).val.val) 0 1 at he
  simp only [radicalElement, radicalMatrix, r, Matrix.mul_apply,
    Fin.sum_univ_succ, UnitaryFourOuter.matrixAut_apply] at he
  simp [hdiag, htri] at he
  rw [hσ t] at he
  exact ht (add_left_cancel (he.trans (add_comm _ _)))

private theorem matrix_center_centralizes_radical (a : UM) (ha : a ∈ center UM) :
    a.val.left ∈ centralizer
      (UnitaryFourConverse.PointParabolic.ambientRadical F σ hσ : Set (SU F (form F σ hσ))) := by
  intro b hb
  have hbU : b ∈ upper F σ hσ := by
    obtain ⟨b,hb,rfl⟩ := hb
    exact ⟨b,radical_le_localUpper F σ hσ hb,rfl⟩
  let bU : UM := ⟨SemidirectProduct.inl b,hbU⟩
  have he := congrArg (fun x : UM => x.val.left) (mem_center_iff.mp ha bU)
  simpa [bU, SemidirectProduct.mul_left, matrix_center_right_one a ha] using he

private def matrixCenterEmbedding : center UM ↪
    center (UnitaryFourConverse.PointParabolic.ambientRadical F σ hσ) where
  toFun a := ⟨⟨a.val.val.left,
    UnitaryFourConverse.PointParabolic.centralizer_ambientRadical_le F σ hσ
      (matrix_center_centralizes_radical a.val a.property)⟩,
    mem_center_iff.mpr (fun b => Subtype.ext
      (matrix_center_centralizes_radical a.val a.property b.val b.property))⟩
  inj' := by
    intro a b he
    apply Subtype.ext
    apply Subtype.ext
    apply SemidirectProduct.ext
    · exact congrArg (fun x : center
        (UnitaryFourConverse.PointParabolic.ambientRadical F σ hσ) => x.val.val) he
    · rw [matrix_center_right_one a.val a.property,
        matrix_center_right_one b.val b.property]

private theorem matrix_center_card_le : Nat.card (center UM) ≤ 2 := by
  have hc : Nat.card (center
      (UnitaryFourConverse.PointParabolic.ambientRadical F σ hσ)) = 2 := by
    let e := (radical F σ hσ).equivMapOfInjective
      (localSU F (form F σ hσ)).subtype (localSU F (form F σ hσ)).subtype_injective
    exact (Nat.card_congr (centerCongr e.symm).toEquiv).trans
      ((UnitaryFourPointLocal.center_radical_card F σ hσ
        (PointLocal.fieldConj_nontrivial 1 hn)).trans (by
          simpa using PointLocal.fixedField_card 1 hn))
  exact (Nat.card_le_card_of_injective matrixCenterEmbedding
    matrixCenterEmbedding.injective).trans hc.le

/-- The center of the exact extended upper subgroup has order two. -/
theorem extendedUpper_center_card : Nat.card (center U) = 2 := by
  let e := (UnitaryFourOuter.extendedUpper F σ hσ).equivMapOfInjective
    (Extension.extensionProjection 1 hn) (Extension.extensionProjection_injective 1 hn)
  have hle : Nat.card (center U) ≤ 2 := by
    exact (Nat.card_congr (centerCongr e.symm).toEquiv).le.trans matrix_center_card_le
  let : Nontrivial U := Finite.one_lt_card_iff_nontrivial.mp (by
    rw [extendedUpper_card]; decide)
  let : Nontrivial (center U) :=
    (IsPGroup.of_card (p := 2) (n := 7) extendedUpper_card).center_nontrivial
  have hlo : 1 < Nat.card (center U) := Finite.one_lt_card
  omega

variable {G G0 : Type*} [Group G] [Group G0]
variable (c : Theory.GroupTheory.RankTwoAmalgam.FaithfulCompletion
    (Extension.amalgam 1 hn) (G := G0)) (i : G0 →* G)

theorem source_sylowImage_card (hi : Function.Injective i) :
    Nat.card (Source.sylowImage c i) = 128 := by
  have hinj : Function.Injective (i.comp c.middle) :=
    fun _ _ he => c.middle_injective (hi he)
  rw [Source.sylowImage, card_map_of_injective hinj,
    Nat.card_congr (subgroupOfEquivOfLe extendedUpper_le_overlap).toEquiv,
    extendedUpper_card]

/-- The literal overlap marking carries the same Sylow as the point endpoint. -/
theorem source_sylowImage_eq_pointSylow :
    Source.sylowImage c i =
      (extendedPointSylow : Subgroup (Extension.point 1 hn)).map (i.comp c.left) := by
  apply le_antisymm
  · rintro x ⟨b,hb,rfl⟩
    exact ⟨(Extension.amalgam 1 hn).left b,hb,rfl⟩
  · rintro x ⟨a,ha,rfl⟩
    refine ⟨⟨a.val,extendedUpper_le_overlap ha⟩,ha,?_⟩
    rfl

/-- The actual marked image is a two-group independently of ambient Sylow promotion. -/
theorem source_sylowImage_isTwoGroup : IsPGroup 2 (Source.sylowImage c i) := by
  rw [source_sylowImage_eq_pointSylow]
  exact extendedPointSylow.isPGroup'.map _

/-- The center calculation retains the source overlap map in every faithful completion. -/
theorem source_sylowImage_center_card (hi : Function.Injective i) :
    Nat.card (center (Source.sylowImage c i)) = 2 := by
  let e : U ≃* Source.sylowImage c i :=
    (subgroupOfEquivOfLe extendedUpper_le_overlap).symm.trans
      (((U).subgroupOf (Extension.overlap 1 hn)).equivMapOfInjective (i.comp c.middle)
        (fun _ _ he => c.middle_injective (hi he)))
  exact (Nat.card_congr (centerCongr e.symm).toEquiv).trans extendedUpper_center_card

/-- The source residual root belongs to the same chosen upper subgroup. -/
theorem source_root_mem_sylowImage (z : pointParabolic 1 hn)
    (h : Source.Hypotheses c i z) : rootElement c i z ∈ Source.sylowImage c i := by
  have hzcore : z ∈ pCore 2 (pointParabolic 1 hn) := by
    obtain ⟨a,ha,he⟩ := sourceRoot_le_pointCoreCenter h.root_mem
    exact he ▸ a.property
  let S := (projectiveSylow 1 hn).subtype (projectiveSylow_le_parabolics 1 hn).1
  have hzU : z.val ∈ upperProjective 1 hn :=
    pCore_isPGroup.le_sylow_of_normal S hzcore
  rw [source_sylowImage_eq_pointSylow]
  refine ⟨Source.pointInclusion z,?_,rfl⟩
  exact (extendedUpper_mem _).mpr hzU

/-- The center of the source Sylow candidate is exactly the marked point-root image. -/
theorem source_sylowImage_center_eq_pointRoot [Finite G]
    (z : pointParabolic 1 hn) (h : Source.Hypotheses c i z) :
    (center (Source.sylowImage c i)).map (Source.sylowImage c i).subtype =
      Source.pointRootImage c i := by
  rw [pointRootImage_eq_zpowers c i z h]
  have hzS := source_root_mem_sylowImage c i z h
  have hzC : (⟨rootElement c i z,hzS⟩ : Source.sylowImage c i) ∈
      center (Source.sylowImage c i) := by
    apply mem_center_iff.mpr
    intro a
    apply Subtype.ext
    have haM : a.val ∈ M c i false := by
      have ha := (source_sylowImage_eq_pointSylow c i).le a.property
      obtain ⟨b,hb,he⟩ := ha
      exact ⟨b,he⟩
    exact mem_centralizer_singleton_iff.mp
      ((source_root_centralizer c i z h).symm ▸ haM)
  apply (eq_of_le_of_card_ge (zpowers_le.mpr
    (mem_map_of_mem (Source.sylowImage c i).subtype hzC)) ?_).symm
  rw [card_map_of_injective (Source.sylowImage c i).subtype_injective,
    source_sylowImage_center_card c i h.embedding_injective,
    Nat.card_zpowers]
  exact (source_root_order c i z h).ge

end CFSG.Quasithin.ChapterF.Section05.ExceptionalLocal
