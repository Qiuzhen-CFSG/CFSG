module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanGlobalPrimeZeroCoreLieModels
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanGlobalPrimeZeroCoreUnitary
public import CFSG.Quasithin.ChapterF.Section01.GreenBook.LieModels.UnitaryFourExtension.BinaryOrders
public import CFSG.Quasithin.ChapterF.Section01.GreenBook.UnitaryFive.LocalStructure

/-!
# Unitary exclusions for the original zero-core prime pair

The source pair has a solvable left endpoint. Above field two, the U₄
point and plane endpoints have nonsolvable SL₂ quotients over the literal
fixed and quadratic fields, respectively. The same subgroups embed in the
actual degree-two extension. The binary ordinary U₄ row is already excluded
by the original source-Sylow size bound.

For the binary extension the whole overlap has order 384, and its marked
U⟨σ⟩ has order 128 and index three. It is therefore Sylow and is not normal.
The source Sylow is normal in its whole overlap, since it is the entire
Sylow intersection of the left local group DS. Transporting that normal
Sylow along the overlap equivalence contradicts Sylow conjugacy. This
uses the actual source Sylow and does not assert the false printed identity
O₂(overlap) = U⟨σ⟩.

The U₅(4) endpoints have nonsolvable SU₃(4) and PSL₂(16) quotients. Thus all
three unitary rows are excluded in both orientations by raw parabolic
equivalence, retaining the whole overlap and every model's own field degree.
These are catalogue filters, not exhaustive recognition of the source pair.
Source: Aschbacher–Smith 5.2.2, pp.647–648, and F.1.12(I)(6–7), pp.263–264
(`refs/quasithin.pdf`).
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Prime
open ChapterF.GreenBook
variable {G : Type*} [Group G] [Finite G]

private theorem sl2_not_solvable {F : Type*} [Field F] [Finite F] [CharP F 2]
    (hF : 2 < Nat.card F) : ¬ Group.IsSolvable SL(2,F) := by
  let := Theory.SpecificGroups.SymplecticFour.NaturalExtension.model_perfect hF
  let := Theory.SpecificGroups.SymplecticFour.NaturalExtension.model_simple hF
  intro hs
  exact Group.IsPerfect.not_isSolvable SL(2,F) hs

open LieModels.UnitaryFour in
private theorem unitary_point_not_solvable (m : ℕ) (hm : 1 < m) :
    ¬ Group.IsSolvable (pointParabolic m hm.le) := by
  intro hs
  let := hs
  let : Group.IsSolvable (PointLocal.ProjectiveLocal m hm.le) :=
    Group.isSolvable_of_isSolvable_injective
      (f := inclusion (PointLocal.projectiveLocal_le_pointParabolic m hm.le))
      (inclusion_injective _)
  let : Group.IsSolvable (PointLocal.MatrixLocal m hm.le) :=
    Group.isSolvable_of_isSolvable_injective
      (f := (PointLocal.localEquiv m hm.le).toMonoidHom)
      (PointLocal.localEquiv m hm.le).injective
  have hsl := Group.isSolvable_of_surjective
    (f := (PointLocal.quotientEquivSL m hm.le).toMonoidHom)
    (PointLocal.quotientEquivSL m hm.le).surjective
  apply sl2_not_solvable (F := PointLocal.FixedField m) _ hsl
  rw [PointLocal.fixedField_card m hm.le]
  exact Nat.pow_lt_pow_right (by decide : 1 < 2) hm

open LieModels.UnitaryFour in
private theorem unitary_plane_not_solvable (m : ℕ) (hm : 1 ≤ m) :
    ¬ Group.IsSolvable (planeParabolic m hm) := by
  intro hs
  let := hs
  let : Group.IsSolvable (L2 m hm) := Group.isSolvable_of_isSolvable_injective
    (f := inclusion (L2_le_planeParabolic m hm)) (inclusion_injective _)
  have hsl := Group.isSolvable_of_surjective
    (f := (Extension.L2QuotientEquivMatrixSL2 m hm).toMonoidHom)
    (Extension.L2QuotientEquivMatrixSL2 m hm).surjective
  apply sl2_not_solvable (F := MatrixField m) _ hsl
  rw [matrixField_card m hm, ← pow_mul]
  exact Nat.pow_lt_pow_right (by decide : 1 < 2) (by omega : 1 < m*2)

open LieModels.UnitaryFour in
/-- Both orientations of U₄ are excluded at every actual positive field degree. -/
theorem LocalData.zeroCore_not_unitaryFour_parabolic
    {T : Sylow 2 G} {L W H A B D R : Subgroup G} {n p : ℕ}
    (d : LocalData T L H B D R) (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (c : CartanPair T L H A B) (hd : CartanPrimeActor A H p D)
    (hz : (generated L H D R).pCoreIn 2 = ⊥) (m : ℕ) (hm : 1 ≤ m) :
    ¬ Nonempty (RankTwoAmalgam.ParabolicEquiv (zeroCoreAmalgam L H B D R)
      (amalgam m hm)) ∧
      ¬ Nonempty (RankTwoAmalgam.ParabolicEquiv (zeroCoreAmalgam L H B D R)
        (amalgam m hm).reverse) := by
  by_cases hm1 : m = 1
  · subst m
    exact d.zeroCore_not_binaryUnitary_parabolic h hH c hd
  · have hs := (d.zeroCore_mixed_solvability h hH c hd hz).1
    let := hs
    constructor
    · rintro ⟨e⟩
      exact unitary_point_not_solvable m (by omega)
        (Group.isSolvable_of_surjective (f := e.left.toMonoidHom) e.left.surjective)
    · rintro ⟨e⟩
      exact unitary_plane_not_solvable m hm
        (Group.isSolvable_of_surjective (f := e.left.toMonoidHom) e.left.surjective)

private theorem unitary_five_left_not_solvable (M : UnitaryFive.Model 4) :
    ¬ Group.IsSolvable M.leftParabolic := by
  intro hs
  let := hs
  have hq := Group.isSolvable_of_surjective
    (f := M.leftLocalQuotientEquiv.toMonoidHom) M.leftLocalQuotientEquiv.surjective
  exact Group.IsPerfect.not_isSolvable M.LocalUnitaryGroup hq

private theorem unitary_five_right_not_solvable (M : UnitaryFive.Model 4) :
    ¬ Group.IsSolvable M.rightParabolic := by
  intro hs
  let := hs
  let : Group.IsSolvable M.LocalLinearGroup := Group.isSolvable_of_surjective
    (f := M.rightLocalQuotientEquiv.toMonoidHom) M.rightLocalQuotientEquiv.surjective
  have hsl := Group.isSolvable_of_isSolvable_injective
    (f := (Theory.PSL2.sl2QuotientEquiv M.F).toMonoidHom)
    (Theory.PSL2.sl2QuotientEquiv M.F).injective
  exact sl2_not_solvable (by rw [M.local_field_card]; decide) hsl

/-- Neither endpoint of the literal U₅(4) model can be the solvable source endpoint. -/
theorem LocalData.zeroCore_not_unitaryFive_parabolic
    {T : Sylow 2 G} {L W H A B D R : Subgroup G} {n p : ℕ}
    (d : LocalData T L H B D R) (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (c : CartanPair T L H A B) (hd : CartanPrimeActor A H p D)
    (hz : (generated L H D R).pCoreIn 2 = ⊥) (M : UnitaryFive.Model 4) :
    ¬ Nonempty (RankTwoAmalgam.ParabolicEquiv (zeroCoreAmalgam L H B D R)
      M.amalgam) ∧
      ¬ Nonempty (RankTwoAmalgam.ParabolicEquiv (zeroCoreAmalgam L H B D R)
        M.amalgam.reverse) := by
  have hs := (d.zeroCore_mixed_solvability h hH c hd hz).1
  let := hs
  constructor
  · rintro ⟨e⟩
    exact unitary_five_left_not_solvable M
      (Group.isSolvable_of_surjective (f := e.left.toMonoidHom) e.left.surjective)
  · rintro ⟨e⟩
    exact unitary_five_right_not_solvable M
      (Group.isSolvable_of_surjective (f := e.left.toMonoidHom) e.left.surjective)


open LieModels.UnitaryFour Theory.SpecificGroups.ClassicalUnitary in
private theorem binary_extension_no_normal_sylow
    (P : Sylow 2 (Extension.overlap 1 (by decide))) : ¬ P.Normal := by
  let U := UnitaryFourOuter.extendedUpper (MatrixField 1) (fieldConj 1)
    (fieldConj_involutive 1 (by decide))
  let a : U ≃ upperMatrix 1 (by decide) × UnitaryFourOuter.C2 :=
    { toFun := fun x => (⟨x.val.left,x.property⟩,x.val.right)
      invFun := fun x => ⟨⟨x.1.val,x.2⟩,x.1.property⟩
      left_inv := fun _ => Subtype.ext (SemidirectProduct.ext rfl rfl)
      right_inv := fun _ => rfl }
  have hU : Nat.card U = 128 := by
    rw [Nat.card_congr a,Nat.card_prod,upperMatrix_card]
    change (2^1)^6 * Nat.card (ZMod 2) = 128
    norm_num
  have hle : Extension.extendedUpper 1 (by decide) ≤ Extension.overlap 1 (by decide) := by
    apply map_mono
    intro x hx
    exact upperMatrix_le_overlap 1 (by decide) hx
  let K := (Extension.extendedUpper 1 (by decide)).subgroupOf
    (Extension.overlap 1 (by decide))
  have hK : Nat.card K = 128 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hle).toEquiv]
    exact (card_map_of_injective (Extension.extensionProjection_injective 1 (by decide))).trans hU
  have hi : K.index = 3 := by
    have hh := K.card_mul_index
    rw [hK, Extension.binary_overlap_card] at hh
    omega
  let Q : Sylow 2 (Extension.overlap 1 (by decide)) :=
    (IsPGroup.of_card (p := 2) (n := 7) hK).toSylow (by rw [hi]; decide)
  intro hn
  let := Sylow.unique_of_normal P hn
  exact Extension.extendedUpper_not_normal 1 (by decide) (Sylow.normal_of_subsingleton Q)

private theorem LocalData.zeroCore_overlap_normal_sylow
    {T : Sylow 2 G} {L W H A B D R : Subgroup G} {n p : ℕ}
    (d : LocalData T L H B D R) (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (c : CartanPair T L H A B) (hd : CartanPrimeActor A H p D)
    (hz : (generated L H D R).pCoreIn 2 = ⊥) :
    ∃ P : Sylow 2 (Global.sourceS L H ⊔ (B ⊓ R) : Subgroup G), P.Normal := by
  let S := Global.sourceS L H
  let C := S ⊔ (B ⊓ R)
  have hf := d.hypothesisF11 h hH c hd hz
  have hsyl : ∃ P : Sylow 2 C, (P : Subgroup C).map C.subtype = S := by
    have hB := d.zeroCore_commonBorel hz
    change ChapterF.Source.commonBorel ![D ⊔ S,R] S = C at hB
    rw [← hB]
    exact hf.sylow_commonBorel
  obtain ⟨P,hP⟩ := hsyl
  have hn : C ≤ normalizer (S : Set G) := by
    have hh := hf.commonBorel_normalizes_localSylow 0
    change ChapterF.Source.commonBorel ![D ⊔ S,R] S ≤ normalizer ((S ⊓ (D ⊔ S) : Subgroup G) : Set G) at hh
    rw [inf_eq_left.mpr (show S ≤ D ⊔ S from le_sup_right),d.zeroCore_commonBorel hz] at hh
    exact hh
  have hPe : (P : Subgroup C) = S.subgroupOf C := by
    apply map_injective C.subtype_injective
    rw [hP,map_subgroupOf_eq_of_le le_sup_left]
  refine ⟨P,?_⟩
  change (P : Subgroup C).Normal
  rw [hPe]
  exact normal_subgroupOf_of_le_normalizer hn

open LieModels.UnitaryFour in
private theorem LocalData.zeroCore_binary_extension_overlap_contradiction
    {T : Sylow 2 G} {L W H A B D R : Subgroup G} {n p : ℕ}
    (d : LocalData T L H B D R) (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (c : CartanPair T L H A B) (hd : CartanPrimeActor A H p D)
    (hz : (generated L H D R).pCoreIn 2 = ⊥)
    (e : (Global.sourceS L H ⊔ (B ⊓ R) : Subgroup G) ≃*
      Extension.overlap 1 (by decide)) : False := by
  obtain ⟨P,hP⟩ := d.zeroCore_overlap_normal_sylow h hH c hd hz
  let Q := P.mapSurjective (f := e.toMonoidHom) e.surjective
  apply binary_extension_no_normal_sylow Q
  exact hP.map e.toMonoidHom e.surjective

open LieModels.UnitaryFour in
/-- The actual degree-two extension is excluded in both orientations, including
the binary endpoint, by transporting the normal Sylow of the whole source overlap. -/
theorem LocalData.zeroCore_not_unitaryFourExtension_parabolic
    {T : Sylow 2 G} {L W H A B D R : Subgroup G} {n p : ℕ}
    (d : LocalData T L H B D R) (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (c : CartanPair T L H A B) (hd : CartanPrimeActor A H p D)
    (hz : (generated L H D R).pCoreIn 2 = ⊥) (m : ℕ) (hm : 1 ≤ m) :
    ¬ Nonempty (RankTwoAmalgam.ParabolicEquiv (zeroCoreAmalgam L H B D R)
      (Extension.amalgam m hm)) ∧
      ¬ Nonempty (RankTwoAmalgam.ParabolicEquiv (zeroCoreAmalgam L H B D R)
        (Extension.amalgam m hm).reverse) := by
  by_cases hm1 : m = 1
  · subst m
    constructor <;> rintro ⟨e⟩ <;>
      exact d.zeroCore_binary_extension_overlap_contradiction h hH c hd hz e.middle
  · have hs := (d.zeroCore_mixed_solvability h hH c hd hz).1
    let := hs
    let f : ProjectiveGroup m hm →* Extension.ProjectiveExtension m hm := SemidirectProduct.inl
    constructor
    · rintro ⟨e⟩
      let : Group.IsSolvable (Extension.point m hm) :=
        Group.isSolvable_of_surjective (f := e.left.toMonoidHom) e.left.surjective
      let j : pointParabolic m hm →* Extension.point m hm :=
        (f.comp (pointParabolic m hm).subtype).codRestrict _
          (fun x => (Extension.mem_point m hm _).mpr x.property)
      exact unitary_point_not_solvable m (by omega)
        (Group.isSolvable_of_isSolvable_injective (f := j) (by
          intro x y he
          apply Subtype.ext
          exact congrArg (fun a : Extension.point m hm => a.val.left) he))
    · rintro ⟨e⟩
      let : Group.IsSolvable (Extension.plane m hm) :=
        Group.isSolvable_of_surjective (f := e.left.toMonoidHom) e.left.surjective
      let j : planeParabolic m hm →* Extension.plane m hm :=
        (f.comp (planeParabolic m hm).subtype).codRestrict _
          (fun x => (Extension.mem_plane m hm _).mpr x.property)
      exact unitary_plane_not_solvable m hm
        (Group.isSolvable_of_isSolvable_injective (f := j) (by
          intro x y he
          apply Subtype.ext
          exact congrArg (fun a : Extension.plane m hm => a.val.left) he))

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Prime
