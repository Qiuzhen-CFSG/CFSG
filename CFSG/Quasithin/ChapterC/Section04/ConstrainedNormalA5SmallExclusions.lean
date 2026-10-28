module

public import CFSG.Quasithin.ChapterC.Section04.ConstrainedNormalSeedPlacement
public import CFSG.Quasithin.ChapterC.Section02.SourceExtraction.C27.StarModels
public import Theory.GroupTheory.GeneralizedFitting.PerfectCoreTwoImages
public import Theory.GroupTheory.PCoreSurjective.OddExtension
public import Theory.SpecificGroups.PSL3.LinearThreeSylow.DefiningSylow
public import Theory.AtlasPort.LinearGroups.G2.DerivedEvenOrder
public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple

/-!
# Small star rows excluded by the original normal A5 seed

The original normal seed lies in the selected constrained component. Its
literal star image retains the A5 two-core quotient: the star kernel is
solvable, so its intersection with this perfect seed lies in the seed's
two-core. Hence sixty divides the order of the original star component.
This excludes its binary SL3 and derived binary G2 markings.

Source: Aschbacher--Smith, C.4.5--8, printed pp.152--154, applied to the
original A5 point residual in 12.7.5, printed p.840.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterC.HypothesisC28
open Chapter1.RadicalExclusions.ModelReduction FullSieve.SourceInterface
variable {G : Type*} [Group G] [Finite G] {H M L R V : Subgroup G}

private theorem subgroupMap_kernel_solvable
    {X Y : Type*} [Group X] [Group Y] (f : X →* Y)
    [Group.IsSolvable f.ker] (A : Subgroup X) :
    Group.IsSolvable (f.subgroupMap A).ker := by
  let j : (f.subgroupMap A).ker →* f.ker :=
    { toFun := fun x => ⟨x.val.val,congrArg Subtype.val x.property⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  apply Group.isSolvable_of_isSolvable_injective (f := j)
  intro x y he
  have hxy : x.val.val = y.val.val := congrArg (fun z : f.ker => z.val) he
  exact Subtype.ext (Subtype.ext hxy)

/-- The actual image of the normal seed in the original star component
retains its entire A5 two-core quotient. -/
theorem constrained_normal_a5_star_seed_quotient
    (h : HypothesisC28 KnownSimple.IsKnownSimple H M L R V)
    (hn : (L.subgroupOf M).Normal)
    (a : L ⧸ pCore 2 L ≃* alternatingGroup (Fin 5))
    (J : Subgroup H) (hJ : J.IsCComponent)
    (hq : IsQuasisimple (J ⧸ pCore 2 J)) (hout : ¬ J ≤ M.subgroupOf H)
    (hf : generalizedFitting J = pCore 2 J) :
    let Jg := J.map H.subtype
    let P := (L.subgroupOf Jg).map (toStarImage Jg R)
    Nonempty (P ⧸ pCore 2 P ≃* alternatingGroup (Fin 5)) := by
  let Jg := J.map H.subtype
  let I := L.subgroupOf Jg
  let π := toStarImage Jg R
  let P := I.map π
  have hLJ : L ≤ Jg := by
    have hm := map_mono (f := H.subtype)
      (h.constrained_normal_seed_le hn J hJ hq hout hf)
    rwa [map_subgroupOf_eq_of_le (h.component_le.trans h.local_le)] at hm
  let e : I ≃* L := subgroupOfEquivOfLe hLJ
  let eQ : I ⧸ pCore 2 I ≃* alternatingGroup (Fin 5) :=
    (QuotientGroup.congr _ _ e (pCore_map_iso 2 e)).trans a
  let : Group.IsPerfect (L.subgroupOf M) := h.component.perfect
  let : Group.IsPerfect L := Group.IsPerfect.ofSurjective
    (f := (subgroupOfEquivOfLe h.component_le).toMonoidHom)
    (subgroupOfEquivOfLe h.component_le).surjective
  let : Group.IsPerfect I := Group.IsPerfect.ofSurjective
    (f := e.symm.toMonoidHom) e.symm.surjective
  let : IsSimpleGroup (alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup (by simp)
  let : IsSimpleGroup (I ⧸ pCore 2 I) := eQ.isSimpleGroup
  let f : I →* P := π.subgroupMap I
  let : Group.IsSolvable π.ker := C27Source.toStarImage_ker_solvable_from_source
    (h.constrained_source_input J hJ hq hout hf)
  let : Group.IsSolvable f.ker := subgroupMap_kernel_solvable π I
  have hk : IsPGroup 2 f.ker := pCore_isPGroup.to_le
    (PerfectCoreTwoExtension.solvable_ker_le_core f)
  exact ⟨(MonoidHom.quotientPCoreEquivOfSurjective f (π.subgroupMap_surjective I) hk).symm.trans eQ⟩

/-- The same literal seed image is a normal C-component of the actual
marked star intersection; no abstract parabolic is substituted. -/
theorem constrained_normal_star_seed_component
    (h : HypothesisC28 KnownSimple.IsKnownSimple H M L R V)
    (hn : (L.subgroupOf M).Normal)
    (J : Subgroup H) (hJ : J.IsCComponent)
    (hq : IsQuasisimple (J ⧸ pCore 2 J)) (hout : ¬ J ≤ M.subgroupOf H)
    (hf : generalizedFitting J = pCore 2 J) :
    let Jg := J.map H.subtype
    let C := starImage Jg R Jg
    let P := (L.subgroupOf Jg).map (toStarImage Jg R)
    let B := (starM Jg R M).subgroupOf C
    P ≤ B ∧ (P.subgroupOf B).Normal ∧ (P.subgroupOf B).IsCComponent := by
  let Jg := J.map H.subtype
  let I := L.subgroupOf Jg
  let B := M.subgroupOf Jg
  let D := M ⊓ Jg
  let π := toStarImage Jg R
  let P := I.map π
  have hLJ : L ≤ Jg := by
    have hm := map_mono (f := H.subtype)
      (h.constrained_normal_seed_le hn J hJ hq hout hf)
    rwa [map_subgroupOf_eq_of_le (h.component_le.trans h.local_le)] at hm
  have hIB : I ≤ B := subgroupOf_mono Jg h.component_le
  let e : D ≃* B :=
    { toFun := fun x => ⟨⟨x,x.property.2⟩,x.property.1⟩
      invFun := fun x => ⟨x.val,⟨x.property,x.val.property⟩⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_mul' := fun _ _ => rfl }
  have hcomp : (I.subgroupOf B).IsCComponent := by
    have hh := (h.component.subgroupOf_of_le (le_inf h.component_le hLJ) inf_le_left).map_equiv e
    have he : (L.subgroupOf D).map e.toMonoidHom = I.subgroupOf B := by
      ext x
      constructor
      · rintro ⟨y,hy,rfl⟩; exact hy
      · intro hx; exact ⟨e.symm x,hx,e.apply_symm_apply x⟩
    exact he ▸ hh
  let : (I.subgroupOf B).Normal := by
    apply normal_subgroupOf_of_le_normalizer
    intro b hb i
    exact (normal_subgroupOf_iff_le_normalizer h.component_le).mp hn hb (i : G)
  let : Group.IsSolvable π.ker := C27Source.toStarImage_ker_solvable_from_source
    (h.constrained_source_input J hJ hq hout hf)
  let f := π.subgroupMap B
  let : Group.IsSolvable f.ker := subgroupMap_kernel_solvable π B
  have heP : (I.subgroupOf B).map f = P.subgroupOf (B.map π) := by
    ext x
    constructor
    · rintro ⟨y,hy,rfl⟩; exact mem_map_of_mem π hy
    · rintro ⟨y,hy,he⟩
      exact ⟨⟨y,hIB hy⟩,hy,Subtype.ext he⟩
  have hc : (P.subgroupOf (B.map π)).IsCComponent := heP ▸
    cComponent_map_of_solvable_ker hcomp f (π.subgroupMap_surjective B)
  have hnormal : (P.subgroupOf (B.map π)).Normal := heP ▸
    (inferInstance : (I.subgroupOf B).Normal).map f (π.subgroupMap_surjective B)
  have heB : B.map π = (starM Jg R M).subgroupOf (starImage Jg R Jg) := by
    ext x
    constructor
    · rintro ⟨y,hy,rfl⟩
      exact ⟨⟨y,mem_sup_left y.property⟩,⟨hy,y.property⟩,rfl⟩
    · rintro ⟨y,hy,he⟩
      exact ⟨⟨y,hy.2⟩,hy.1,Subtype.ext he⟩
  change P ≤ (starM Jg R M).subgroupOf (starImage Jg R Jg) ∧ _
  rw [← heB]
  exact ⟨map_mono hIB,hnormal,hc⟩

/-- Sixty divides the unchanged star component, through the actual seed image. -/
theorem constrained_normal_a5_star_card_dvd
    (h : HypothesisC28 KnownSimple.IsKnownSimple H M L R V)
    (hn : (L.subgroupOf M).Normal)
    (a : L ⧸ pCore 2 L ≃* alternatingGroup (Fin 5))
    (J : Subgroup H) (hJ : J.IsCComponent)
    (hq : IsQuasisimple (J ⧸ pCore 2 J)) (hout : ¬ J ≤ M.subgroupOf H)
    (hf : generalizedFitting J = pCore 2 J) :
    60 ∣ Nat.card (starImage (J.map H.subtype) R (J.map H.subtype)) := by
  let Jg := J.map H.subtype
  let P := (L.subgroupOf Jg).map (toStarImage Jg R)
  obtain ⟨e⟩ := h.constrained_normal_a5_star_seed_quotient hn a J hJ hq hout hf
  have hd := (card_quotient_dvd_card (pCore 2 P)).trans (card_subgroup_dvd_card P)
  have hc : Nat.card (P ⧸ pCore 2 P) = 60 := by
    rw [Nat.card_congr e.toEquiv,nat_card_alternatingGroup]
    norm_num [Nat.factorial]
  exact hc ▸ hd

/-- The actual binary SL3 star row cannot contain the original normal A5 seed. -/
theorem no_constrained_normal_a5_star_linear_three_two
    (h : HypothesisC28 KnownSimple.IsKnownSimple H M L R V)
    (hn : (L.subgroupOf M).Normal)
    (a : L ⧸ pCore 2 L ≃* alternatingGroup (Fin 5))
    (J : Subgroup H) (hJ : J.IsCComponent)
    (hq : IsQuasisimple (J ⧸ pCore 2 J)) (hout : ¬ J ≤ M.subgroupOf H)
    (hf : generalizedFitting J = pCore 2 J)
    (e : starImage (J.map H.subtype) R (J.map H.subtype) ≃* SL(3,ZMod 2)) : False := by
  have hd := h.constrained_normal_a5_star_card_dvd hn a J hJ hq hout hf
  rw [Nat.card_congr e.toEquiv,Matrix.PSL3.LinearThree.DefiningSylow.card_specialLinear] at hd
  norm_num at hd

/-- The actual derived binary G2 star row cannot contain the original normal A5 seed. -/
theorem no_constrained_normal_a5_star_g2_derived_two
    (h : HypothesisC28 KnownSimple.IsKnownSimple H M L R V)
    (hn : (L.subgroupOf M).Normal)
    (a : L ⧸ pCore 2 L ≃* alternatingGroup (Fin 5))
    (J : Subgroup H) (hJ : J.IsCComponent)
    (hq : IsQuasisimple (J ⧸ pCore 2 J)) (hout : ¬ J ≤ M.subgroupOf H)
    (hf : generalizedFitting J = pCore 2 J)
    (e : starImage (J.map H.subtype) R (J.map H.subtype) ≃*
      commutator (Atlas.G2.Model (ZMod 2))) : False := by
  have hd := h.constrained_normal_a5_star_card_dvd hn a J hJ hq hout hf
  rw [Nat.card_congr e.toEquiv,Atlas.G2.DerivedEvenOrder.card_derived_binary (by simp)] at hd
  norm_num at hd

end CFSG.Quasithin.ChapterC.HypothesisC28
