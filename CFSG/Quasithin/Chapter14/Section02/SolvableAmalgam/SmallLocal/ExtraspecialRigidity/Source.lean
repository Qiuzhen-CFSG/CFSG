module
public import CFSG.Quasithin.Chapter14.Section02.SolvableAmalgam.SmallLocal.ExtraspecialRigidity
public import CFSG.Quasithin.Chapter14.Section02.SolvableAmalgam.SmallLocal.Parabolics.Transport
public import CFSG.Quasithin.ChapterF.Section01.GreenBook.ExceptionalModels.G2
public import CFSG.Quasithin.ChapterF.Section01.GreenBook.ExceptionalModels.M12

/-!
# The full G₂(2) and M₁₂ source rows of cubic rigidity

A genuine isomorphism of the inclusion amalgams transports the embedded
quaternion core and the elementary eight in the second parabolic. Its
compatibility on the whole intersection gives the actual Sylow subgroup
and preserves its centralizer of the eight. These literal transported
subgroups satisfy the quaternion rigidity theorem.

The two final theorems take exactly the oriented model predicates already
produced by cubic recognition and the original source context. They have
no additional marking, residual-enlargement, or automorphism assumptions.

Source: Aschbacher--Smith, Lemma 14.2.21, printed p.988 (PDF p.1005).
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section02.SolvableAmalgam.SmallLocal.ExtraspecialRigidity
open Chapter15.Section03 SourcePreliminaries

variable {G F : Type*} [Group G] [Finite G] [Group F]

/-- Transport the actual quaternion geometry through compatible parabolic isomorphisms. -/
theorem rigidity_of_pair
    (T : Sylow 2 G) (M Mc H : Subgroup G) (c : CubicSourceContext T M Mc H)
    (A B U E : Subgroup F) (hUA : U ≤ A) (hUB : U ≤ B)
    (d : QuaternionCentralProductData (A.pCoreIn 2))
    (hA : Nat.card A = 192) (hU : Nat.card U = 64)
    [IsElementaryAbelian 2 E] (hE : Nat.card E = 8)
    (hEQ : E ≤ A.pCoreIn 2) (hEU : E ≤ U)
    [(E.subgroupOf B).Normal]
    (hcentral : U ⊓ centralizer (E : Set F) = E)
    (eA : A ≃* H) (eB : B ≃* ↥(sourceResidual M Mc ⊔ (T : Subgroup G)))
    (hcompat : ∀ u : U, (eA ⟨u,hUA u.property⟩ : G) =
      (eB ⟨u,hUB u.property⟩ : G))
    (hUmap : ((U.subgroupOf B).map eB.toMonoidHom).map
      (sourceResidual M Mc ⊔ (T : Subgroup G)).subtype = (T : Subgroup G)) : H = Mc := by
  let X := sourceResidual M Mc ⊔ (T : Subgroup G)
  let f : B →* G := X.subtype.comp eB.toMonoidHom
  have hf : Function.Injective f := X.subtype_injective.comp eB.injective
  let E' := (E.subgroupOf B).map f
  have hEdef : E' = ((E.subgroupOf B).map eB.toMonoidHom).map X.subtype := by
    exact (map_map _ _ _).symm
  let eQ : A.pCoreIn 2 ≃* H.pCoreIn 2 :=
    ((pCore 2 A).equivMapOfInjective A.subtype A.subtype_injective).symm.trans
      (((eA.subgroupMap (pCore 2 A)).trans (MulEquiv.subgroupCongr (pCore_map_iso 2 eA))).trans
        ((pCore 2 H).equivMapOfInjective H.subtype H.subtype_injective))
  let : IsElementaryAbelian 2 (E.subgroupOf B) :=
    IsElementaryAbelian.subgroupOf (hEU.trans hUB)
  let : IsElementaryAbelian 2 E' := IsElementaryAbelian.map f
  have hE' : Nat.card E' = 8 := by
    rw [card_map_of_injective hf,Nat.card_congr (subgroupOfEquivOfLe (hEU.trans hUB)).toEquiv]
    exact hE
  have hT : Nat.card (T : Subgroup G) = 64 := by
    rw [← hUmap,card_map_of_injective X.subtype_injective,
      card_map_of_injective eB.injective,
      Nat.card_congr (subgroupOfEquivOfLe hUB).toEquiv]
    exact hU
  have hQ : E' ≤ H.pCoreIn 2 := by
    rw [hEdef]
    exact pair_map_le_two_core A B U H X hUA hUB eA eB hcompat E hEU hEQ
  have hEX : E' ≤ X := by rw [hEdef]; exact map_subtype_le _
  have hnormal : (E'.subgroupOf X).Normal := by
    rw [hEdef]
    change (((E.subgroupOf B).map eB.toMonoidHom).map X.subtype |>.comap X.subtype).Normal
    rw [comap_map_eq_self_of_injective X.subtype_injective]
    exact Normal.map inferInstance eB.toMonoidHom eB.surjective
  have hXE : X ≤ normalizer (E' : Set G) :=
    (normal_subgroupOf_iff_le_normalizer hEX).mp hnormal
  have hEU' : E' ≤ (T : Subgroup G) := by
    rw [← hUmap,map_map]
    exact map_mono (fun x hx => hEU hx)
  have hcentral' : (T : Subgroup G) ⊓ centralizer (E' : Set G) = E' := by
    apply le_antisymm
    · rintro x ⟨hx,hxc⟩
      rw [← hUmap,map_map] at hx
      obtain ⟨u,hu,rfl⟩ := hx
      refine ⟨u,?_,rfl⟩
      apply hcentral.le
      refine ⟨hu,?_⟩
      intro y hy
      have he := hxc (f ⟨y,hEU.trans hUB hy⟩) ⟨⟨y,hEU.trans hUB hy⟩,hy,rfl⟩
      have hh : (⟨y,hEU.trans hUB hy⟩ : B) * u = u * ⟨y,hEU.trans hUB hy⟩ := by
        apply hf
        simpa only [map_mul] using he
      exact congrArg Subtype.val hh
    · exact le_inf hEU' E'.le_centralizer
  exact rigidity_of_geometry T M Mc H c (d.map eQ)
    ((Nat.card_congr eA.toEquiv).symm.trans hA) hT E' hE' hQ hXE hcentral'

/-- A literal isomorphism of the two inclusion amalgams supplies every
compatibility and Sylow-image premise of the quaternion geometry transport. -/
theorem rigidity_of_pair_iso
    (T : Sylow 2 G) (M Mc H : Subgroup G) (c : CubicSourceContext T M Mc H)
    (A B U E : Subgroup F) (hUA : U ≤ A) (hUB : U ≤ B)
    (d : QuaternionCentralProductData (A.pCoreIn 2))
    (hA : Nat.card A = 192) (hU : Nat.card U = 64)
    [IsElementaryAbelian 2 E] (hE : Nat.card E = 8)
    (hEQ : E ≤ A.pCoreIn 2) (hEU : E ≤ U)
    [(E.subgroupOf B).Normal]
    (hcentral : U ⊓ centralizer (E : Set F) = E)
    (a : RankTwoAmalgam.Iso (RankTwoAmalgam.ofSubgroups A U B hUA hUB)
      (RankTwoAmalgam.ofSubgroups H (H ⊓ (sourceResidual M Mc ⊔ (T : Subgroup G)))
        (sourceResidual M Mc ⊔ (T : Subgroup G)) inf_le_left inf_le_right)) : H = Mc := by
  let X := sourceResidual M Mc ⊔ (T : Subgroup G)
  have hTM : (T : Subgroup G) ≤ M := c.H_inf_M ▸ inf_le_right
  have hXM : X ≤ M := sup_le (sourceResidual_le _ _) hTM
  have hHX : H ⊓ X = (T : Subgroup G) := le_antisymm
    ((inf_le_inf_left H hXM).trans c.H_inf_M.le)
    (le_inf c.sylow_le_H le_sup_right)
  apply rigidity_of_pair T M Mc H c A B U E hUA hUB d hA hU hE hEQ hEU hcentral
    a.left a.right
  · intro u
    exact (congrArg Subtype.val (a.left_commutes u)).trans
      (congrArg Subtype.val (a.right_commutes u)).symm
  · ext x
    constructor
    · rintro ⟨_,⟨u,hu,rfl⟩,rfl⟩
      have he := congrArg Subtype.val (a.right_commutes (⟨u,hu⟩ : U))
      change (a.right u : G) = (a.middle ⟨u,hu⟩ : G) at he
      change (a.right u : G) ∈ (T : Subgroup G)
      rw [he]
      exact hHX.le (a.middle ⟨u,hu⟩).property
    · intro hx
      obtain ⟨u,hu⟩ := a.middle.surjective (⟨x,hHX.symm ▸ hx⟩ : ↥(H ⊓ X))
      refine ⟨a.right ⟨u,hUB u.property⟩,⟨⟨u,hUB u.property⟩,u.property,rfl⟩,?_⟩
      exact (congrArg Subtype.val (a.right_commutes u)).trans (congrArg Subtype.val hu)


/-- The full binary G₂ row of the original oriented cubic amalgam. -/
theorem g2_rigidity
    (T : Sylow 2 G) (M Mc H : Subgroup G) (c : CubicSourceContext T M Mc H)
    (hmodel : ChapterF.GreenBook.ExceptionalModels.G2.IsFullAmalgam
      (RankTwoAmalgam.ofSubgroups H (H ⊓ (sourceResidual M Mc ⊔ (T : Subgroup G)))
        (sourceResidual M Mc ⊔ (T : Subgroup G)) inf_le_left inf_le_right)) : H = Mc := by
  obtain ⟨a⟩ := hmodel
  open Atlas.G2 Atlas.G2.BinaryCore Atlas.G2.BinaryParabolicPair in
    exact rigidity_of_pair_iso T M Mc H c firstParabolic secondParabolic commonSylow elementary
      commonSylow_le_first commonSylow_le_second
      (Parabolics.g2_core_factors.map (MulEquiv.subgroupCongr firstParabolic_pCore.symm))
      Parabolics.g2_pair_orders.1 Parabolics.g2_pair_orders.2.2.1
      card_elementary (firstParabolic_pCore.symm ▸ elementary_le_core)
      (elementary_le_core.trans core_le_unipotent)
      Parabolics.g2_elementary_normal_and_centralizer.2.2 a.symm

/-- The actual M₁₂ inclusion-amalgam row of cubic rigidity. -/
theorem m12_rigidity
    (T : Sylow 2 G) (M Mc H : Subgroup G) (c : CubicSourceContext T M Mc H)
    (hmodel : ChapterF.GreenBook.MathieuTwelve.IsM12Amalgam
      (RankTwoAmalgam.ofSubgroups H (H ⊓ (sourceResidual M Mc ⊔ (T : Subgroup G)))
        (sourceResidual M Mc ⊔ (T : Subgroup G)) inf_le_left inf_le_right)) : H = Mc := by
  obtain ⟨a⟩ := hmodel
  open Sporadic.Mathieu Sporadic.Mathieu.M12SmallPair in
    exact rigidity_of_pair_iso T M Mc H c firstParabolic secondParabolic sylowCandidate elementary
      inf_le_left inf_le_right
      (Parabolics.m12_core_factors.map (MulEquiv.subgroupCongr mapped_pCore_eq_core.symm))
      Parabolics.m12_parabolic_orders.1 Parabolics.m12_parabolic_orders.2.2
      card_elementary (by
        change elementary ≤ (pCore 2 firstParabolic).map firstParabolic.subtype
        rw [mapped_pCore_eq_core]
        exact elementary_le_core)
      elementary_le_sylowCandidate Parabolics.m12_elementary_normal_and_centralizer.2.2
      (a.trans ChapterF.GreenBook.MathieuTwelve.concreteIso).symm


end CFSG.Quasithin.Chapter14.Section02.SolvableAmalgam.SmallLocal.ExtraspecialRigidity
