module
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry.FirstFlagSmallImages
public import CFSG.Quasithin.ChapterB.Section03.Offenders.SixCoreSylowImages
public import Theory.GroupTheory.SylowActionCore
public import Theory.GroupTheory.SylowNormalRestriction

/-!
# The original first-core image and Sylow preimages in both covering rows

The common Sylow maps onto the full two-core of the first action image.
The two actions have the same kernel, so this gives the exact permutation
image of R₁. Its kernel intersection is the prescribed Sylow of the full
action kernel. Thus R₁ is Sylow in the full preimage of its image and the
Frattini image trichotomy applies, with the covered central three retained.
The literal centralizer Sylow premise of B.2.19 on LR₁ is also proved.

The covered consumer combines the established small-image bounds with
this trichotomy: an escaping Baumann normalizer forces a constructed S₆
action whose Thompson, Baumann and R₁ images coincide with the full point
radical. The alpha decomposition, subsequent full-image normalizer bound
and covered residual classification remain source obligations; this does
not assert full 13.2.2(7) or 13.4.1.
Source: Aschbacher--Smith Notation 13.2.1, 13.2.2(7), B.2.19 and
B.3.4(2)(v), printed pp.877--878,81--82,84--85.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry
open Chapter12.Section02 Solvable Nonsolvable
open scoped IsMulCommutative
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- The actual first action core maps onto the full two-core of the point
stabilizer image in both quotient rows. -/
theorem firstFlagCore_permutation_image
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (D : ChosenModule T L V) (m : CoreMarking D)
    (z : V) (hz : z.val ∈ omegaOneCenterAmbient (T : Subgroup G))
    (hzL : z.val ∉ centralizer (L : Set G))
    (q : (L ⊔ (T : Subgroup G) : Subgroup G) →* Equiv.Perm (Fin 6))
    (hq : ∀ (x : (L ⊔ (T : Subgroup G) : Subgroup G)) (v : V),
      (m.coordinate (V.normalizerMonoidHom
        ⟨x.val,(sup_le D.normalizes ((structural G T L h).2.2 V D).1) x.property⟩ v)).toAdd =
        BinaryPermutation.coreRepresentation (Fin 6) (q x) (m.coordinate v).toAdd) :
    ((firstFlagCore h structural D m).subgroupOf (L ⊔ (T : Subgroup G))).map q =
      (BinaryPermutation.SixCorePoint.stabilizer (m.coordinate z).toAdd ⊓ q.range).pCoreIn 2 := by
  let X := L ⊔ (T : Subgroup G)
  let P := firstFlagNormalizer T L V
  have hPX : P ≤ X := inf_le_left
  let f := firstFlagAction h structural D m
  let g := q.comp (inclusion hPX)
  have hfg : f.ker = g.ker := by
    ext p
    change f p = 1 ↔ g p = 1
    constructor
    · intro hp
      apply BinaryPermutation.SixCoreNormalizer.action_injective
      apply LinearMap.ext
      intro w
      obtain ⟨v,rfl⟩ := m.coordinate.surjective (Multiplicative.ofAdd w)
      have he := hq (inclusion hPX p) v
      change (m.coordinate (f p v)).toAdd =
        BinaryPermutation.coreRepresentation (Fin 6) (g p) (m.coordinate v).toAdd at he
      rw [hp] at he
      exact he.symm
    · intro hp
      apply MulEquiv.ext
      intro v
      apply m.coordinate.injective
      apply Multiplicative.toAdd.injective
      have he := hq (inclusion hPX p) v
      change _ = BinaryPermutation.coreRepresentation (Fin 6) (g p) _ at he
      rw [hp,map_one,Module.End.one_apply] at he
      exact he
  have hPr : g.range =
      BinaryPermutation.SixCorePoint.stabilizer (m.coordinate z).toAdd ⊓ q.range := by
    have hP := first_flag_normalizer_eq_centralizer h structural D m z hz hzL
    change P = X ⊓ centralizer ({z.val} : Set G) at hP
    let U := V.subgroupOf X
    have hVX : V ≤ X := D.le_sylow.trans le_sup_right
    let : U.Normal := normal_subgroupOf_of_le_normalizer
      (sup_le D.normalizes ((structural G T L h).2.2 V D).1)
    let eu : U ≃* V := subgroupOfEquivOfLe hVX
    let e := eu.trans m.coordinate
    let zi := eu.symm z
    have he (x : X) (v : U) : (e (MulAut.conjNormal x v)).toAdd =
        BinaryPermutation.coreRepresentation (Fin 6) (q x) (e v).toAdd := hq x (eu v)
    have hg : g.range = (centralizer ({zi.val} : Set X)).map q := by
      apply le_antisymm
      · rintro a ⟨p,rfl⟩
        refine ⟨inclusion hPX p,?_,rfl⟩
        apply mem_centralizer_singleton_iff.mpr
        exact Subtype.ext (mem_centralizer_singleton_iff.mp ((hP.le p.property).2))
      · rintro a ⟨x,hx,rfl⟩
        have hxp : x.val ∈ P := hP.symm ▸ ⟨x.property,
          mem_centralizer_singleton_iff.mpr
            (congrArg Subtype.val (mem_centralizer_singleton_iff.mp hx))⟩
        exact ⟨⟨x.val,hxp⟩,rfl⟩
    rw [hg,ChapterB.Offenders.SixCorePoint.point_image U q e he zi]
    rfl
  let S := T.subtype (show (T : Subgroup G) ≤ P from sylow_le_firstFlagNormalizer)
  have hh := sylow_actionCore_image f g hfg S
  rw [hPr] at hh
  rw [←hh]
  ext a
  constructor
  · rintro ⟨x,⟨t,ht,htx⟩,rfl⟩
    let s : (S : Subgroup P) := ⟨⟨t.val,sylow_le_firstFlagNormalizer t.property⟩,t.property⟩
    refine ⟨s.val,⟨s,ht,rfl⟩,?_⟩
    exact congrArg q (Subtype.ext htx)
  · rintro ⟨p,⟨s,hs,rfl⟩,rfl⟩
    refine ⟨inclusion hPX s.val,?_,rfl⟩
    exact ⟨⟨s.val.val,s.property⟩,hs,rfl⟩

/-- The full permutation kernel has the prescribed Sylow intersection in R₁. -/
theorem firstFlagCore_kernel_sylow
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (D : ChosenModule T L V) (m : CoreMarking D)
    (q : (L ⊔ (T : Subgroup G) : Subgroup G) →* Equiv.Perm (Fin 6))
    (hq : ∀ (x : (L ⊔ (T : Subgroup G) : Subgroup G)) (v : V),
      (m.coordinate (V.normalizerMonoidHom
        ⟨x.val,(sup_le D.normalizes ((structural G T L h).2.2 V D).1) x.property⟩ v)).toAdd =
        BinaryPermutation.coreRepresentation (Fin 6) (q x) (m.coordinate v).toAdd) :
    ∃ S : Sylow 2 q.ker, (S : Subgroup q.ker).map q.ker.subtype =
      (firstFlagCore h structural D m).subgroupOf (L ⊔ (T : Subgroup G)) ⊓ q.ker := by
  let X := L ⊔ (T : Subgroup G)
  let U := V.subgroupOf X
  let R := firstFlagCore h structural D m
  let Ri := R.subgroupOf X
  have hVX : V ≤ X := D.le_sylow.trans le_sup_right
  have hRT : R ≤ T := map_subtype_le _
  have hRX : R ≤ X := hRT.trans le_sup_right
  let : U.Normal := normal_subgroupOf_of_le_normalizer
    (sup_le D.normalizes ((structural G T L h).2.2 V D).1)
  let eu : U ≃* V := subgroupOfEquivOfLe hVX
  let e := eu.trans m.coordinate
  have he (x : X) (v : U) : (e (MulAut.conjNormal x v)).toAdd =
      BinaryPermutation.coreRepresentation (Fin 6) (q x) (e v).toAdd := hq x (eu v)
  have hk := ChapterB.Offenders.SixCorePoint.kernel_centralizer U q e he
  let Ti := T.subtype (show (T : Subgroup G) ≤ X from le_sup_right)
  obtain ⟨S,hS⟩ := Ti.exists_sylow_map_eq_inf_of_normal q.ker
  refine ⟨S,hS.trans ?_⟩
  apply map_injective X.subtype_injective
  rw [hk,←map_inf_centralizer_of_injective X.subtype X.subtype_injective,
    ←map_inf_centralizer_of_injective X.subtype X.subtype_injective,
    map_subgroupOf_eq_of_le hRX,map_subgroupOf_eq_of_le hVX,
    Sylow.coe_subtype,map_subgroupOf_eq_of_le (show (T : Subgroup G) ≤ X from le_sup_right)]
  exact (RecognitionSource.chosen_sylow_centralizer_eq_core h D structural).trans
    (firstFlagCore_kernel h structural D m).2.symm

/-- R₁ is Sylow in the full preimage of its actual permutation image.
The preimage is permitted to retain the central three. -/
theorem firstFlagCore_sylow_preimage
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (D : ChosenModule T L V) (m : CoreMarking D)
    (q : (L ⊔ (T : Subgroup G) : Subgroup G) →* Equiv.Perm (Fin 6))
    (hq : ∀ (x : (L ⊔ (T : Subgroup G) : Subgroup G)) (v : V),
      (m.coordinate (V.normalizerMonoidHom
        ⟨x.val,(sup_le D.normalizes ((structural G T L h).2.2 V D).1) x.property⟩ v)).toAdd =
        BinaryPermutation.coreRepresentation (Fin 6) (q x) (m.coordinate v).toAdd) :
    let R := (firstFlagCore h structural D m).subgroupOf (L ⊔ (T : Subgroup G))
    ∃ S : Sylow 2 ((R.map q).comap q),
      (S : Subgroup ((R.map q).comap q)) = R.subgroupOf ((R.map q).comap q) := by
  obtain ⟨S,hS⟩ := firstFlagCore_kernel_sylow h structural D m q hq
  exact exists_sylow_preimage_of_kernel_intersection _
    ((T.isPGroup'.to_le (show firstFlagCore h structural D m ≤ T from map_subtype_le _)).comap_subtype)
    q S hS

open Theory.SpecificGroups.SymmetricSix.BinaryFlags (pointCore)
/-- The original first action core has two small Baumann images or the full
point-radical image, in both ordinary and covered rows. -/
theorem firstFlagCore_baumann_images
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (D : ChosenModule T L V) (m : CoreMarking D)
    (z : V) (hz : z.val ∈ omegaOneCenterAmbient (T : Subgroup G))
    (hzL : z.val ∉ centralizer (L : Set G))
    (q : (L ⊔ (T : Subgroup G) : Subgroup G) →* Equiv.Perm (Fin 6))
    (hq : ∀ (x : (L ⊔ (T : Subgroup G) : Subgroup G)) (v : V),
      (m.coordinate (V.normalizerMonoidHom
        ⟨x.val,(sup_le D.normalizes ((structural G T L h).2.2 V D).1) x.property⟩ v)).toAdd =
        BinaryPermutation.coreRepresentation (Fin 6) (q x) (m.coordinate v).toAdd)
    (hLq : (L.subgroupOf (L ⊔ (T : Subgroup G))).map q = alternatingGroup (Fin 6)) :
    let X := L ⊔ (T : Subgroup G)
    let R := firstFlagCore h structural D m
    (((ChapterB.baumann R).subgroupOf X).map q = ⊥ ∨
      ∃ r : Equiv.Perm (Fin 6), r.IsSwap ∧
        ((ChapterB.baumann R).subgroupOf X).map q = zpowers r) ∨
      (Function.Surjective q ∧ ∃ a : alternatingGroup (Fin 6),
        ((elementaryAbelianMaxJ R).subgroupOf X).map q = pointCore.map (MulAut.conj a.val).toMonoidHom ∧
        ((ChapterB.baumann R).subgroupOf X).map q = pointCore.map (MulAut.conj a.val).toMonoidHom ∧
        (R.subgroupOf X).map q = pointCore.map (MulAut.conj a.val).toMonoidHom) := by
  let X := L ⊔ (T : Subgroup G)
  let U := V.subgroupOf X
  let R := firstFlagCore h structural D m
  let Ri := R.subgroupOf X
  have hVX : V ≤ X := D.le_sylow.trans le_sup_right
  have hRT : R ≤ T := map_subtype_le _
  have hRX : R ≤ X := hRT.trans le_sup_right
  let : U.Normal := normal_subgroupOf_of_le_normalizer
    (sup_le D.normalizes ((structural G T L h).2.2 V D).1)
  let := D.elementary
  let : IsElementaryAbelian 2 U := IsElementaryAbelian.subgroupOf hVX
  let eu : U ≃* V := subgroupOfEquivOfLe hVX
  let e := eu.trans m.coordinate
  let zi := eu.symm z
  have he (x : X) (v : U) : (e (MulAut.conjNormal x v)).toAdd =
      BinaryPermutation.coreRepresentation (Fin 6) (q x) (e v).toAdd := hq x (eu v)
  have hY : alternatingGroup (Fin 6) ≤ q.range := hLq ▸ map_le_range q (L.subgroupOf X)
  have hz' : ¬ ∀ a : alternatingGroup (Fin 6),
      BinaryPermutation.alternatingCoreRepresentation (Fin 6) a (e zi).toAdd = (e zi).toAdd := by
    intro ha
    apply hzL
    apply (m.mem_fixed_iff z).mpr
    apply (BinaryPermutation.core_fixed_iff_constant (by simp) _).mp
    change ∀ a : alternatingGroup (Fin 6),
      BinaryPermutation.coreRepresentation (Fin 6) a.val (e zi).toAdd = (e zi).toAdd at ha
    simpa only [e,zi,MulEquiv.trans_apply,eu.apply_symm_apply] using ha
  obtain ⟨hQR,hRC⟩ := firstFlagCore_kernel h structural D m
  have hQRi : pCore 2 X ≤ Ri := fun x hx => hQR (mem_map_of_mem X.subtype hx)
  have hVR : U ≤ Ri := comap_mono (D.le_core.trans hQR)
  have hcore : Ri ⊓ centralizer (U : Set X) = pCore 2 X := by
    apply map_injective X.subtype_injective
    rw [←map_inf_centralizer_of_injective X.subtype X.subtype_injective,
      map_subgroupOf_eq_of_le hRX,map_subgroupOf_eq_of_le hVX]
    exact hRC
  have hRP : Ri ≤ centralizer ({zi.val} : Set X) := by
    intro r hr
    apply mem_centralizer_singleton_iff.mpr
    exact Subtype.ext (mem_centralizer_singleton_iff.mp
      (original_sylow_le_centralizer hz (hRT hr)))
  have hRm : Ri.map q =
      (BinaryPermutation.SixCorePoint.stabilizer (e zi).toAdd ⊓ q.range).pCoreIn 2 := by
    simpa only [e,zi,MulEquiv.trans_apply,eu.apply_symm_apply] using
      firstFlagCore_permutation_image h structural D m z hz hzL q hq
  have hJi : elementaryAbelianMaxJ Ri = (elementaryAbelianMaxJ R).subgroupOf X := by
    have hm : (elementaryAbelianMaxJ Ri).map X.subtype = elementaryAbelianMaxJ R := by
      rw [←elementaryAbelianMaxJ_map_injective X.subtype X.subtype_injective,
        map_subgroupOf_eq_of_le hRX]
    rw [←hm]
    ext x
    exact (mem_map_iff_mem X.subtype_injective).symm
  have hBi : ChapterB.baumann Ri = (ChapterB.baumann R).subgroupOf X := by
    have hm : (ChapterB.baumann Ri).map X.subtype = ChapterB.baumann R := by
      rw [ChapterC.RankOne.SymmetricSix.baumann_map X X.subtype X.subtype_injective Ri,
        map_subgroupOf_eq_of_le hRX]
    rw [←hm]
    ext x
    exact (mem_map_iff_mem X.subtype_injective).symm
  have hh := ChapterB.Offenders.SixCorePoint.point_baumann_alternative_of_kernel_sylow
    U q e he Ri hVR hQRi hcore ((T.isPGroup'.to_le hRT).comap_subtype)
    (firstFlagCore_kernel_sylow h structural D m q hq) hY zi hz' hRP hRm
  rw [hJi,hBi] at hh
  exact hh

/-- The literal centralizer Sylow premise of B.2.19 on LR₁, with no
assumption that the whole centralizer is a two-group. -/
theorem firstFlagCore_centralizer_sylow
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (D : ChosenModule T L V) (m : CoreMarking D) :
    let R := firstFlagCore h structural D m
    IsSylowSubgroupIn (R ⊓ centralizer (V : Set G))
      ((L ⊔ R) ⊓ centralizer (V : Set G)) := by
  let X := L ⊔ (T : Subgroup G)
  let U := V.subgroupOf X
  let R := firstFlagCore h structural D m
  have hVX : V ≤ X := D.le_sylow.trans le_sup_right
  have hRT : R ≤ T := map_subtype_le _
  let : U.Normal := normal_subgroupOf_of_le_normalizer
    (sup_le D.normalizes ((structural G T L h).2.2 V D).1)
  let Ti := T.subtype (show (T : Subgroup G) ≤ X from le_sup_right)
  have hs : Chapter1.IsSylowIn 2 ((Ti : Subgroup X) ⊓ centralizer (U : Set X))
      (centralizer (U : Set X)) := Ti.exists_sylow_map_eq_inf_of_normal _
  have hm := (Chapter1.IsSylowIn.map_iff X.subtype X.subtype_injective).mpr hs
  have hCm : (centralizer (U : Set X)).map X.subtype = X ⊓ centralizer (V : Set G) := by
    have hh := map_inf_centralizer_of_injective X.subtype X.subtype_injective
      (⊤ : Subgroup X) U
    have hUm : U.map X.subtype = V := map_subgroupOf_eq_of_le hVX
    simpa only [top_inf_eq,←MonoidHom.range_eq_map,range_subtype,
      hUm] using hh.symm
  rw [←map_inf_centralizer_of_injective X.subtype X.subtype_injective,
    hCm,map_subgroupOf_eq_of_le hVX,Sylow.coe_subtype,
    map_subgroupOf_eq_of_le (show (T : Subgroup G) ≤ X from le_sup_right)] at hm
  have hRC : R ⊓ centralizer (V : Set G) = (T : Subgroup G) ⊓ centralizer (V : Set G) :=
    (firstFlagCore_kernel h structural D m).2.trans
      (RecognitionSource.chosen_sylow_centralizer_eq_core h D structural).symm
  rw [←hRC] at hm
  exact hm.restrict (inf_le_inf_right _ le_sup_right)
    (inf_le_inf_right _ (sup_le le_sup_left (hRT.trans le_sup_right)))

/-- If the covered Baumann normalizer escapes M, the actual first-core
Thompson, Baumann and radical images are all the same full point radical.
The action and its even conjugator are constructed from the source marking. -/
theorem covered_firstFlagCore_full_image_of_escape
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (D : ChosenModule T L V) (m : CoreMarking D)
    (hc : Section08.SolvableExclusion.IsTripleCoverSix (L ⧸ pCore 2 L))
    (z : V) (hz : z.val ∈ omegaOneCenterAmbient (T : Subgroup G))
    (hzL : z.val ∉ centralizer (L : Set G))
    (hescape : ¬ normalizer (ChapterB.baumann (firstFlagCore h structural D m) : Set G) ≤
      normalizer (L : Set G)) :
    let X := L ⊔ (T : Subgroup G)
    let R := firstFlagCore h structural D m
    ∃ q : X →* Equiv.Perm (Fin 6),
      (∀ (x : X) (v : V),
        (m.coordinate (V.normalizerMonoidHom
          ⟨x.val,(sup_le D.normalizes ((structural G T L h).2.2 V D).1) x.property⟩ v)).toAdd =
          BinaryPermutation.coreRepresentation (Fin 6) (q x) (m.coordinate v).toAdd) ∧
      (L.subgroupOf X).map q = alternatingGroup (Fin 6) ∧
      Function.Surjective q ∧ ∃ a : alternatingGroup (Fin 6),
        ((elementaryAbelianMaxJ R).subgroupOf X).map q = pointCore.map (MulAut.conj a.val).toMonoidHom ∧
        ((ChapterB.baumann R).subgroupOf X).map q = pointCore.map (MulAut.conj a.val).toMonoidHom ∧
        (R.subgroupOf X).map q = pointCore.map (MulAut.conj a.val).toMonoidHom := by
  obtain ⟨q,hq,hLq,_⟩ := firstFlagCore_permutation_marking h structural D m z hz hzL
  rcases firstFlagCore_baumann_images h structural D m z hz hzL q hq hLq with hs | hf
  · exact (hescape (covered_firstFlagCore_small_baumann_normalizer h structural D m hc
      q hq hLq hs)).elim
  · exact ⟨q,hq,hLq,hf⟩

end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry
