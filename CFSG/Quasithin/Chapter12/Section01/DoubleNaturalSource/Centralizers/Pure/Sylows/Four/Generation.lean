module
public import CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.Centralizers.Pure.Core.LocalComponent
public import Theory.SpecificGroups.BinaryLinear.SylowFlagOvergroups.FourOuter
public import Theory.GroupTheory.PGroup.NormalSupplementKernel

/-!
# Generation by the pure-point residual and the original Sylow

In dimension four a proper full-Sylow overgroup preserved by an outer
SL₄(2) automorphism is solvable. The pure stabilizer has the nonsolvable
SL₃(2) quotient, so together with the original Sylow it generates the full
source action group. The kernel on LT is a two-group: its restriction to
L is exactly O₂(L). It lies in T, giving the literal equality ⟨L_w,T⟩=LT.

This supplies the generation step in the MS3 argument without assuming an
ambient Sylow statement or dimension-four weak closure.
Source: Aschbacher--Smith 12.1.4, printed p.790; binary flag geometry as in
A.3.12. The original pure-vector assembly owner is
`qt-d-double-natural-pure-fusion`.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterH.NaturalDual.SourceSetup
open BinaryLinear.OuterCyclic BinaryLinear.InvariantNodeActions
variable {M E : Type*} [Group M] [AddCommGroup E] [Module (ZMod 2) E]
  (S : SourceSetup 4 M E)

private theorem model_group_eq_componentAction (m : M) :
    S.model.group m = componentAction (componentLayer M) S.layer m := by
  apply MulEquiv.ext
  intro x
  have he := congrArg S.model.group (show
    ((MulAut.conjNormal m (S.layer.symm x) : componentLayer M) : M) =
      m * (S.layer.symm x : M) * m⁻¹ from rfl)
  rw [map_mul,map_mul,map_inv,S.model.on_layer,S.model.on_layer,S.layer.apply_symm_apply] at he
  have hc : MulAut.conj (S.model.group m x) =
      S.model.group m * MulAut.conj x * (S.model.group m)⁻¹ := by
    ext y
    simp only [MulAut.conj_apply, MulAut.mul_apply, MulAut.inv_apply, map_mul, map_inv,
      MulEquiv.apply_symm_apply]
  have hj : Function.Injective (MulAut.conj : LinearGroup 4 →* MulAut (LinearGroup 4)) := by
    exact MulAut.conj_injective_of_center_eq_bot
      (BinaryNaturalDual.ModelOrbits.AutomorphismModel.linear_center_eq_bot (by decide))
  exact hj (hc.trans he.symm)

private theorem pure_not_solvable (u : S.natural) (hu : (u : E) ≠ 0) :
    ¬ Group.IsSolvable (S.stabilizer u) := by
  let e := S.purePointEquiv u hu
  let x := S.naturalCoordinates u
  have hx := S.naturalCoordinates_ne_zero u hu
  let f := (BinaryNaturalDual.VectorStabilizers.Pure.quotientGroupCoordinates hx).toMonoidHom.comp
    ((BinaryNaturalDual.VectorStabilizers.Pure.pointQuotientAction x).comp e.toMonoidHom)
  have hf : Function.Surjective f :=
    (BinaryNaturalDual.VectorStabilizers.Pure.quotientGroupCoordinates hx).surjective.comp
      ((Theory.LinearAlgebra.BinaryFivePointStabilizer.quotientAction_surjective x).comp e.surjective)
  let := BinaryLinear.linearGroup_isPerfect 3 (by decide)
  let : IsSimpleGroup (Matrix.ProjectiveSpecialLinearGroup (Fin 3) (ZMod 2)) :=
    Atlas.psl_simple_high_rank (F := ZMod 2) 3 (by decide)
  let : IsSimpleGroup (LinearGroup 3) :=
    (projectiveEquivLinear (by decide : 0 < 3)).symm.isSimpleGroup
  intro hs
  let := hs
  exact Group.IsPerfect.not_isSolvable (LinearGroup 3)
    (Group.isSolvable_of_surjective hf)

theorem four_pure_stabilizer_sup_sylow (T : Sylow 2 M)
    (u : S.natural) (hu : (u : E) ≠ 0) :
    S.stabilizer u ⊔ (T : Subgroup M) = ⊤ := by
  let := S.finite_group
  let J := S.stabilizer u ⊔ (T : Subgroup M)
  let K := componentLayer M
  let C := J ⊓ K
  have hCK : C ≤ K := inf_le_right
  have hXK : S.stabilizer u ≤ K := (S.pure_stabilizer_eq_residual u hu).2
  have hXC : S.stabilizer u ≤ C := le_inf le_sup_left hXK
  obtain ⟨P,hP⟩ := T.exists_subgroupOf_eq_of_normal K
  let Q := P.mapSurjective (f := S.layer.toMonoidHom) S.layer.surjective
  let R := (C.subgroupOf K).map S.layer.toMonoidHom
  have hQR : (Q : Subgroup (LinearGroup 4)) ≤ R := by
    apply map_mono
    rw [hP]
    intro x hx
    exact ⟨(show (T : Subgroup M) ≤ J from le_sup_right) hx,x.property⟩
  have hns : ¬ Group.IsSolvable R := by
    intro hr
    let := hr
    let f : S.stabilizer u →* R :=
      (S.layer.subgroupMap (C.subgroupOf K)).toMonoidHom.comp
        (((subgroupOfEquivOfLe hCK).symm.toMonoidHom).comp (inclusion hXC))
    have hf : Function.Injective f :=
      (S.layer.subgroupMap _).injective.comp
        ((subgroupOfEquivOfLe hCK).symm.injective.comp (inclusion_injective hXC))
    exact S.pure_not_solvable u hu (Group.isSolvable_of_isSolvable_injective hf)
  have hTK : ¬ (T : Subgroup M) ≤ K := by
    intro ht
    apply T.not_dvd_index
    have hh := index_dvd_of_le ht
    rwa [BinaryNaturalDual.ModelOrbits.SourceComparison.componentLayer_index S.degree S.projective] at hh
  obtain ⟨t,ht,htK⟩ := SetLike.not_le_iff_exists.mp hTK
  have hTC : (T : Subgroup M) ≤ normalizer (C : Set M) := by
    apply le_trans _ inf_normalizer_le_normalizer_inf
    exact le_inf (le_sup_right.trans J.le_normalizer) (by rw [normalizer_eq_top]; exact le_top)
  have hTP : (T : Subgroup M) ≤ normalizer ((T : Subgroup M) ⊓ K : Set M) := by
    apply le_trans _ inf_normalizer_le_normalizer_inf
    exact le_inf (T : Subgroup M).le_normalizer (by rw [normalizer_eq_top]; exact le_top)
  have hsub : ((T : Subgroup M) ⊓ K).subgroupOf K = (P : Subgroup K) := by
    rw [hP]
    ext x
    exact and_iff_left x.property
  have ha : S.model.group t ∉ MulAut.innerSubgroup (LinearGroup 4) :=
    fun hh => htK ((S.model.inner_iff t).mp hh)
  have hQ : (Q : Subgroup _).map (S.model.group t).toMonoidHom = Q := by
    rw [S.model_group_eq_componentAction]
    have hh := componentAction_map_subgroup K S.layer ((T : Subgroup M) ⊓ K)
      inf_le_right t (hTP ht)
    change ((P : Subgroup K).map S.layer.toMonoidHom).map
      (componentAction K S.layer t).toMonoidHom = (P : Subgroup K).map S.layer.toMonoidHom
    simpa only [hsub] using hh
  have hR : R.map (S.model.group t).toMonoidHom = R := by
    rw [S.model_group_eq_componentAction]
    exact componentAction_map_subgroup K S.layer C hCK t (hTC ht)
  have htop : R = ⊤ := by
    by_contra hn
    exact hns (BinaryLinear.SylowFlagOvergroups.solvable_of_outer_invariant_four Q R hQR hn
      (S.model.group t) ha hQ hR)
  have hKC : K ≤ C := by
    have hh := congrArg (Subgroup.comap S.layer.toMonoidHom) htop
    rw [comap_map_eq_self_of_injective S.layer.injective,comap_top] at hh
    exact subgroupOf_eq_top.mp hh
  have hKJ : K ≤ J := hKC.trans inf_le_left
  have hJ : K ⊔ (T : Subgroup M) = ⊤ := by
    have hi : K.index = 2 :=
      BinaryNaturalDual.ModelOrbits.SourceComparison.componentLayer_index S.degree S.projective
    have hd : (K ⊔ (T : Subgroup M)).index ∣ 2 := by
      simpa only [hi] using index_dvd_of_le (show K ≤ K ⊔ (T : Subgroup M) from le_sup_left)
    have hn : ¬ 2 ∣ (K ⊔ (T : Subgroup M)).index :=
      fun hh => T.not_dvd_index (hh.trans (index_dvd_of_le le_sup_right))
    exact index_eq_one.mp (((Nat.dvd_prime Nat.prime_two).mp hd).resolve_right (fun hh => hn (by rw [hh])))
  apply top_unique
  rw [← hJ]
  exact sup_le hKJ le_sup_right

end CFSG.Quasithin.ChapterH.NaturalDual.SourceSetup

namespace CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.DoubledBranch.SourceModel
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {B : DoubledBranch T L V 4}
  [IsElementaryAbelian 2 (componentOrbit V (T : Subgroup G))]
  (S : B.SourceModel)

include S in
theorem four_pure_residual_sup_sylow
    (hTM : (T : Subgroup G) ≤ normalizer (L : Set G))
    (w : componentOrbit V (T : Subgroup G)) (hw : w ≠ 1)
    (hp : (B.coordinates w).toAdd.2 = 0) :
    B.pointResidual w ⊔ (T : Subgroup G) = L ⊔ (T : Subgroup G) := by
  let M := normalizer (L : Set G)
  let J := L ⊔ (T : Subgroup G)
  let H := B.pointResidual w ⊔ (T : Subgroup G)
  have hJM : J ≤ M := sup_le L.le_normalizer hTM
  have hXJ : B.pointResidual w ≤ J := ((B.pointResidual_le w).trans inf_le_left).trans le_sup_left
  have hHJ : H ≤ J := sup_le hXJ le_sup_right
  let f : J →* B.ActionQuotient := B.actionProjection.comp (inclusion hJM)
  let Lj := L.subgroupOf J
  let Tj := T.subtype (show (T : Subgroup G) ≤ J from le_sup_right)
  let Hj := H.subgroupOf J
  let Xj := (B.pointResidual w).subgroupOf J
  let P := (T.subtype hTM).mapSurjective B.actionProjection_surjective
  have hT : (Tj : Subgroup J).map f = (P : Subgroup B.ActionQuotient) := by
    ext a
    constructor <;> rintro ⟨t,ht,rfl⟩
    · exact ⟨⟨t,hJM t.property⟩,ht,rfl⟩
    · exact ⟨⟨t,(show (T : Subgroup G) ≤ J from le_sup_right) ht⟩,ht,rfl⟩
  have hX : Xj.map f = S.setup.stabilizer (Additive.ofMul w) := by
    rw [(S.setup.pure_stabilizer_eq_residual
      ⟨Additive.ofMul w,(S.natural_marking w).mpr hp⟩ hw).1]
    rw [← S.pointResidual_image w]
    ext a
    constructor <;> rintro ⟨x,hx,rfl⟩
    · change (x : G) ∈ (B.pointResidualInComponent w).map L.subtype at hx
      obtain ⟨l,hl,he⟩ := hx
      exact ⟨l,hl,congrArg B.actionProjection (Subtype.ext he)⟩
    · have hx' : (x : G) ∈ B.pointResidual w := mem_map_of_mem L.subtype hx
      exact ⟨⟨x,hXJ hx'⟩,hx',rfl⟩
  have hmap : Hj.map f = ⊤ := by
    have he : Xj ⊔ (Tj : Subgroup J) = Hj :=
      (subgroupOf_sup hXJ le_sup_right).symm
    rw [← he,Subgroup.map_sup,hX,hT]
    exact S.setup.four_pure_stabilizer_sup_sylow P
      ⟨Additive.ofMul w,(S.natural_marking w).mpr hp⟩ hw
  let : Lj.Normal := normal_subgroupOf_of_le_normalizer (sup_le L.le_normalizer hTM)
  have hgen : Lj ⊔ (Tj : Subgroup J) = ⊤ := by
    change L.subgroupOf J ⊔ (T : Subgroup G).subgroupOf J = ⊤
    rw [← subgroupOf_sup le_sup_left le_sup_right,subgroupOf_self]
  let e : Lj ≃* L := subgroupOfEquivOfLe le_sup_left
  have hk : IsPGroup 2 (f.comp Lj.subtype).ker := by
    have he : f.comp Lj.subtype = B.componentToActionQuotient.comp e.toMonoidHom := rfl
    rw [he,← MonoidHom.comap_ker,B.componentToActionQuotient_ker]
    exact pCore_isPGroup.comap_of_injective e.toMonoidHom e.injective
  have hfk := f.kernel_isPGroup_of_normal_supplement Lj Tj Tj.isPGroup' hgen hk
  have hker : f.ker ≤ Hj := (hfk.le_sylow_of_normal Tj).trans (comap_mono le_sup_right)
  have htop : Hj = ⊤ := by
    have he := congrArg (Subgroup.comap f) hmap
    rwa [comap_map_eq_self hker,comap_top] at he
  exact le_antisymm hHJ (subgroupOf_eq_top.mp htop)

end CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.DoubledBranch.SourceModel
