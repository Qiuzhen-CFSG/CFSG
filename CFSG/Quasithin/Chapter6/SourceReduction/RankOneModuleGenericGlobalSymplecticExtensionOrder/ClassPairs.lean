module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalSymplecticExtensionOrder.OuterDegree
public import Theory.SpecificGroups.SymplecticFour.SourceFusionOrder.ClassPairs

/-!
# Three-class coverage through the original symplectic amalgam

A pure comparison restricts to the original inner Sylow and transports
compatible parabolic conjugators. It therefore gives simultaneous source
and native class paths for a fixed pure comparison, retaining its literal
map on the whole Borel. These paths cover the original ambient involutions
by three marked elements of its Sylow center. The native Sylow in the same
full extension gives coverage by the three corresponding native images.

These are coverage results. Their irredundance and class-predicate
preservation inside all three full centralizers are still needed before
applying the Thompson order formula.

Source: Aschbacher--Smith F.4.27,30,35,38,43, printed pp.288--296,
through 5.3.2--3, pp.658--659 of refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Theory.SpecificGroups.SymplecticFour
open Representation.OneCohomology.SymplecticFour
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
open Theory.SpecificGroups.SymplecticFour.SourceFusionOrder
variable {G : Type*} [Group G] [Finite G]

private theorem marked_sylow_equiv {F : Type*} [Field F] [Finite F] [CharP F 2]
    {m : ℕ} (hm : 0<m) (hF : Nat.card F=2^m)
    {S C : Subgroup G} (hSC : S≤C) (hs : Chapter1.IsSylowIn 2 S C)
    (e : C ≃* borel (F := F)) :
    ∃ eS : S ≃* unipotent (F := F),
      ∀ s : S, (e (inclusion hSC s)).val=(eS s).val := by
  obtain ⟨R,hR⟩ := hs
  have hRS : (R : Subgroup C)=S.subgroupOf C := by
    apply map_injective C.subtype_injective
    rw [hR,map_subgroupOf_eq_of_le hSC]
  let U := (unipotentSylow hF hm).subtype unipotent_le_borel
  let : (U : Subgroup (borel (F := F))).Normal := unipotent_normal_in_borel
  let := Sylow.unique_of_normal U (inferInstance : U.Normal)
  have hSU : (S.subgroupOf C).map e.toMonoidHom=unipotent.subgroupOf borel := by
    rw [←hRS]
    exact congrArg Sylow.toSubgroup (Subsingleton.elim
      (R.mapSurjective (f := e.toMonoidHom) e.surjective) U)
  let eS : S ≃* unipotent (F := F) := (subgroupOfEquivOfLe hSC).symm.trans
    ((e.subgroupMap (S.subgroupOf C)).trans
      ((MulEquiv.subgroupCongr hSU).trans (subgroupOfEquivOfLe unipotent_le_borel)))
  exact ⟨eS,fun _ => rfl⟩


/-- A pure amalgam comparison gives the same three source/native class paths
and retains its literal Sylow restriction through the whole Borel. -/
theorem symplectic_amalgam_class_pairs
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    {m : ℕ} (hm : 0<m) (hF : Nat.card F=2^m)
    {S C P Q : Subgroup G} (hSC : S≤C) (hCP : C≤P) (hCQ : C≤Q)
    (hs : Chapter1.IsSylowIn 2 S C)
    (e : RankTwoAmalgam.Iso (RankTwoAmalgam.ofSubgroups P C Q hCP hCQ)
      (SourceNormalizerExtension.diagram F)) :
    ∃ a : S≃*unipotent (F := F),
      (∀ x, (e.middle (inclusion hSC x)).val=(a x).val) ∧
      ∀ x : S, orderOf x=2 → ∃ i : Fin 3,
        IsConj (a.symm (centralRepresentative i)).val x.val ∧
          IsConj (centralRepresentative i).val (a x).val := by
  obtain ⟨a,ha⟩ := marked_sylow_equiv hm hF hSC hs e.middle
  refine ⟨a,ha,?_⟩
  let f : pointParabolic (F := F)→*G := P.subtype.comp e.left.symm.toMonoidHom
  let g : planeParabolic (F := F)→*G := Q.subtype.comp e.right.symm.toMonoidHom
  have hl (b : borel (F := F)) : f (inclusion inf_le_left b)=(e.middle.symm b).val := by
    change (e.left.symm (inclusion inf_le_left b)).val=(e.middle.symm b).val
    have hh : e.left.symm (inclusion inf_le_left b)=inclusion hCP (e.middle.symm b) := by
      apply e.left.injective
      exact (e.left.apply_symm_apply _).trans
        ((e.left_commutes (e.middle.symm b)).trans
          (congrArg (inclusion inf_le_left) (e.middle.apply_symm_apply b))).symm
    exact congrArg Subtype.val hh
  have hr (b : borel (F := F)) : g (inclusion inf_le_right b)=(e.middle.symm b).val := by
    change (e.right.symm (inclusion inf_le_right b)).val=(e.middle.symm b).val
    have hh : e.right.symm (inclusion inf_le_right b)=inclusion hCQ (e.middle.symm b) := by
      apply e.right.injective
      exact (e.right.apply_symm_apply _).trans
        ((e.right_commutes (e.middle.symm b)).trans
          (congrArg (inclusion inf_le_right) (e.middle.apply_symm_apply b))).symm
    exact congrArg Subtype.val hh
  have hag (b : borel (F := F)) := (hl b).trans (hr b).symm
  have hxmap (x : S) : f (inclusion (unipotent_le_borel.trans inf_le_left) (a x))=x.val := by
    have hb : inclusion unipotent_le_borel (a x)=e.middle (inclusion hSC x) :=
      Subtype.ext (ha x).symm
    exact (hl (inclusion unipotent_le_borel (a x))).trans
      ((congrArg (fun b : borel (F := F) => (e.middle.symm b).val) hb).trans
        (congrArg Subtype.val (e.middle.symm_apply_apply (inclusion hSC x))))
  have hrmap (i : Fin 3) : f (inclusion inf_le_left (borelRepresentative (F := F) i))=
      (a.symm (centralRepresentative i)).val := by
    have hh := hxmap (a.symm (centralRepresentative i))
    change f (inclusion (unipotent_le_borel.trans inf_le_left) (centralRepresentative i))=_
    simpa only [a.apply_symm_apply] using hh
  intro x hx
  obtain ⟨i,hi,hi'⟩ := compatible_class_pair f g hag (a x) ((a.orderOf_eq x).trans hx)
  exact ⟨i,by rwa [hrmap,hxmap] at hi,hi'⟩

variable {T : Sylow 2 G} {L W H A B : Subgroup G} {n : ℕ}
    (d : Preparation T L H A B (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hp : Group.IsPerfect (residual H))
    (F : Type) [Field F] [Finite F] [CharP F 2]
    {m : ℕ} (hm : 0<m) (hF : Nat.card F=2^m)
    (he : Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
      (ChapterF.GreenBook.LieModels.SymplecticFour.amalgam F)) ∨
      Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
      (ChapterF.GreenBook.LieModels.SymplecticFour.amalgam F).reverse))
include d h hH hp hm hF he

/-- Three pinned involutions in the original Sylow center cover every
ambient involution. This asserts coverage, with irredundance still separate. -/
theorem Preparation.symplectic_three_class_cover :
    ∃ a : sourceS L H≃*unipotent (F := F),
      (∀ i : Fin 3, orderOf (a.symm (centralRepresentative i)).val=2 ∧
        a.symm (centralRepresentative i)∈center (sourceS L H)) ∧
      ∀ x : G, orderOf x=2 → ∃ i : Fin 3,
        IsConj (a.symm (centralRepresentative i)).val x := by
  let P := ChapterF.Source.parabolic ![L,residual H] (sourceS L H)
  let C := P 0⊓P 1
  have hSC : sourceS L H≤C :=
    le_inf (le_sup_right.trans le_sup_left) (le_sup_right.trans le_sup_left)
  have hf := d.hypothesisF11 h hH.1.1.2
  have hs : Chapter1.IsSylowIn 2 (sourceS L H) C := by
    change Chapter1.IsSylowIn 2 (sourceS L H) (P 0⊓P 1)
    rw [show P 0⊓P 1=ChapterF.Source.commonBorel ![L,residual H] (sourceS L H) from
      ChapterF.Source.lemma_F_1_3_6 hf]
    exact hf.sylow_commonBorel
  have hc : ∃ a : sourceS L H≃*unipotent (F := F),
      ∀ x : sourceS L H, orderOf x=2 → ∃ i : Fin 3,
        IsConj (a.symm (centralRepresentative i)).val x.val := by
    rcases he with he | he <;> obtain ⟨e⟩ := he
    · obtain ⟨a,_,ha⟩ := symplectic_amalgam_class_pairs hm hF hSC inf_le_left inf_le_right hs e
      exact ⟨a,fun x hx => (ha x hx).imp (fun _ hh => hh.1)⟩
    · obtain ⟨a,_,ha⟩ := symplectic_amalgam_class_pairs hm hF hSC inf_le_right inf_le_left hs e.reverse
      exact ⟨a,fun x hx => (ha x hx).imp (fun _ hh => hh.1)⟩
  obtain ⟨a,ha⟩ := hc
  refine ⟨a,?_,?_⟩
  · intro i
    exact ⟨(Subgroup.orderOf_coe _).trans
      ((a.symm.orderOf_eq _).trans (centralRepresentative_order i)),
      (centerCongr a.symm ⟨_,centralRepresentative_center i⟩).property⟩
  · intro x hx
    obtain ⟨y,hy,hxy⟩ := d.symplectic_involution_fused_into_sourceS h hH hp F hm hF he x hx
    have hy2 : orderOf (⟨y,hy⟩ : sourceS L H)=2 := by
      rw [←Subgroup.orderOf_coe]
      change orderOf y=2
      obtain ⟨c,hc⟩ := isConj_iff.mp hxy
      rw [←hc]
      exact ((MulAut.conj c).orderOf_eq x).trans hx
    obtain ⟨i,hi⟩ := ha ⟨y,hy⟩ hy2
    exact ⟨i,hi.trans hxy.symm⟩

/-- The same full extension is covered by the images of the three pinned
native involutions; its odd outer part introduces no additional classes. -/
theorem Preparation.symplectic_extension_three_class_cover
    (a : SymplecticNormalizerMarking L (residual H) (sourceS L H) F) :
    ∀ x : a.extension.carrier, orderOf x=2 → ∃ i : Fin 3,
      IsConj (a.extension.innerMap (centralRepresentative i).val) x := by
  obtain ⟨Q,hQ⟩ := d.symplectic_extension_native_sylow h hH hp hm hF he a
  intro x hx
  obtain ⟨y,hxy⟩ := Q.exists_isConj_of_orderOf_eq_prime_pow
    (x := x) (n := 1) (by simpa using hx)
  obtain ⟨z,hz,hzy⟩ := (show y.val∈(unipotent (F := F)).map a.extension.innerMap from hQ ▸ y.property)
  let u : unipotent (F := F) := ⟨z,hz⟩
  have hu : orderOf u=2 := by
    rw [←Subgroup.orderOf_coe,←orderOf_injective a.extension.innerMap a.extension.innerMap_injective,
      hzy]
    obtain ⟨c,hc⟩ := isConj_iff.mp hxy
    rw [←hc]
    exact ((MulAut.conj c).orderOf_eq x).trans hx
  obtain ⟨i,g,_,hg⟩ := involution_parabolic_conjugate_representative u hu
  have hc : IsConj (centralRepresentative i).val u.val := (isConj_iff.mpr ⟨g,hg⟩).symm
  refine ⟨i,(a.extension.innerMap.map_isConj hc).trans ?_⟩
  change IsConj (a.extension.innerMap z) x
  rw [hzy]
  exact hxy.symm

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
