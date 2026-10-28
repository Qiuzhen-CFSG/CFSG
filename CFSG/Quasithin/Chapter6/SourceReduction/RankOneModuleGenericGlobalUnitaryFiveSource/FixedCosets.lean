module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalUnitaryFiveSource.EndpointFusion
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalUnitaryFiveSource.CommonCentralizers
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalUnitaryFiveSource.FullLongCentralizers
public import Theory.GroupTheory.UniqueFixedCosetCounting
public import Theory.GroupTheory.UniqueFixedCosetQuotient
-- Internal proof split: retain the existing literal residual-center transport.
import all CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalUnitaryFiveSource.FullLongCentralizers

/-!
# Unique fixed cosets in the original U₅(4) short centralizer

The same endpoint maps identify the full long centralizer and the local
short centralizer with their full centralizers in the selected extension.
Whole-endpoint fusion identifies both commuting-class fibers. Double counting
therefore gives exactly one fixed coset on average for the ambient long class.
The Thompson subgroup supplies an ambient centralizer Sylow inside the plane
normalizer, so every long-class involution fixes a coset and hence exactly one.

The final application retains the original short root, both endpoint maps,
the entire middle action and all range equations. It removes the initial
unique-fixed-coset premise of F.4.42; the two subsequent quotient arguments
and full ambient short-centralizer containment remain separate obligations.
Source: Aschbacher–Smith F.4.40,42, printed pp.294–295 of refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
open ChapterF.GreenBook.UnitaryFive ChapterF.SourceCompletion.UnitaryNonbinary
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L W H A C : Subgroup G} {n : ℕ}

namespace UnitaryFiveFusion
omit [Finite G] in
private theorem local_centralizer_equiv {E : Type*} [Group E]
    (N : Subgroup G) (f : N →* E) (hf : Function.Injective f) (t : N)
    (hfull : centralizer ({f t} : Set E) ≤ f.range) :
    ∃ k : N.subgroupOf (centralizer ({t.val} : Set G)) ≃ centralizer ({f t} : Set E),
      ∀ x, (k x).val = f ⟨x.val.val,x.property⟩ := by
  let g : N.subgroupOf (centralizer ({t.val} : Set G)) → centralizer ({f t} : Set E) :=
    fun x => ⟨f ⟨x.val.val,x.property⟩, mem_centralizer_singleton_iff.mpr (by
      rw [←map_mul,←map_mul]
      exact congrArg f (Subtype.ext (mem_centralizer_singleton_iff.mp x.val.property)))⟩
  have hginj : Function.Injective g := by
    intro x y he
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun v : N => v.val) (hf (congrArg Subtype.val he))
  have hgsurj : Function.Surjective g := by
    intro y
    obtain ⟨x,hx⟩ := hfull y.property
    have hxc : x.val ∈ centralizer ({t.val} : Set G) := by
      apply mem_centralizer_singleton_iff.mpr
      exact congrArg (fun v : N => v.val) (hf (show f (x*t)=f (t*x) from by
        simpa only [map_mul,hx] using mem_centralizer_singleton_iff.mp y.property))
    exact ⟨⟨⟨x.val,hxc⟩,x.property⟩,Subtype.ext hx⟩
  exact ⟨Equiv.ofBijective g ⟨hginj,hgsurj⟩,fun _ => rfl⟩

variable
    (d : Preparation T L H A C (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hp : Group.IsPerfect (residual H)) (U : Model 4)
    (hc : Nonempty (RankTwoAmalgam.Iso
        (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) U.amalgam) ∨
      Nonempty (RankTwoAmalgam.Iso
        (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) U.amalgam.reverse))
    (r : UnitaryFiveNormalizerMarking L (residual H) ((T : Subgroup G) ⊓ L) U)
    (a : UnitarySource.MarkedMiddleAction L (residual H) ((T : Subgroup G) ⊓ L) U.amalgam.reverse)
    (F : RankTwoAmalgam.Iso (UnitaryCompletion.normalizerDiagram L (residual H)) r.extension.amalgam.reverse)
    (h0 : ∀ x, (F.left (inclusion r.left_le x)).val = MulAut.conj (a.comparison.left x).val)
    (h1 : ∀ x, (F.right (inclusion r.right_le x)).val = MulAut.conj (a.comparison.right x).val)
include d h hH hp hc h0 h1

omit h0 in
private theorem marked_long_full (z : normalizer (residual H : Set G))
    (hz : z.val ∈ (center (residual H)).map (residual H).subtype)
    (hz2 : orderOf z.val=2) :
    centralizer ({markedRightHom r F z} : Set r.extension.carrier) ≤ (markedRightHom r F).range := by
  let P := ChapterF.Source.parabolic ![L,residual H] ((T : Subgroup G) ⊓ L) 1
  have hKP : residual H ≤ P := le_sup_left.trans le_sup_left
  let zP : P := ⟨z.val,hKP (map_subtype_le _ hz)⟩
  have hR : ((residual H).subgroupOf P).map
      (U.leftParabolic.subtype.comp a.comparison.right.toMonoidHom) = U.leftLocalImage := by
    have hres : (residual H).subgroupOf P = solvableResidual P := by
      have he : (solvableResidual P).map P.subtype = residual H :=
        d.reduced_parabolic_residuals h hH.1.1.2 hp (.unitaryFive U hc) 1
      rw [←he]
      exact comap_map_eq_self_of_injective P.subtype_injective _
    rw [hres,←map_map,map_solvableResidual_eq a.comparison.right.toMonoidHom
      a.comparison.right.surjective]
    rfl
  have hzn := center_image_transport hKP a.comparison.right hR zP hz
  have hzne : (a.comparison.right zP).val ≠ 1 := by
    intro hh
    have he : a.comparison.right zP = 1 := Subtype.ext hh
    have hzp : zP = 1 := a.comparison.right.map_eq_one_iff.mp he
    have hez : z.val = 1 := congrArg Subtype.val hzp
    simp [hez] at hz2
  have hbase : markedRightHom r F z = r.extension.baseHom (a.comparison.right zP).val :=
    Subtype.ext (h1 zP)
  intro x hx
  rw [hbase] at hx
  have hxL := FiveExtension.long_root_centralizer_le U r.extension _ hzn hzne hx
  refine ⟨F.right.symm ⟨x.val,hxL⟩,?_⟩
  apply Subtype.ext
  change (F.right (F.right.symm ⟨x.val,hxL⟩)).val=x.val
  exact congrArg (fun v : r.extension.left => v.val) (F.right.apply_symm_apply _)

private theorem class_count
    (t : normalizer (L : Set G))
    (ht : t.val ∈ (center (L.pCoreIn 2)).map (L.pCoreIn 2).subtype)
    (ht2 : orderOf t.val=2)
    (htshort : markedLeftHom r F t = r.extension.baseHom U.shortInvolution.val)
    (z : normalizer (residual H : Set G))
    (hz : z.val ∈ (center (residual H)).map (residual H).subtype)
    (hz2 : orderOf z.val=2) :
    let M := centralizer ({t.val} : Set G)
    let X := (normalizer (L : Set G)).subgroupOf M
    Nat.card {x : M // IsConj z.val x.val} * Nat.card X =
      Nat.card M * Nat.card {x : X // IsConj z.val x.val.val} := by
  let M := centralizer ({t.val} : Set G)
  let X := (normalizer (L : Set G)).subgroupOf M
  let t' := markedLeftHom r F t
  let z' := markedRightHom r F z
  have htfull : centralizer ({t'} : Set r.extension.carrier) ≤ (markedLeftHom r F).range := by
    intro x hx
    rw [show t'=r.extension.baseHom U.shortInvolution.val from htshort] at hx
    have hxR := FiveExtension.shortInvolution_centralizer_le U r.extension hx
    refine ⟨F.left.symm ⟨x.val,hxR⟩,?_⟩
    apply Subtype.ext
    change (F.left (F.left.symm ⟨x.val,hxR⟩)).val=x.val
    exact congrArg (fun v : r.extension.right => v.val) (F.left.apply_symm_apply _)
  obtain ⟨kt,hkt⟩ := local_centralizer_equiv _ (markedLeftHom r F)
    ((inclusion_injective r.extension.right_le).comp F.left.injective) t htfull
  have hzN : centralizer ({z.val} : Set G) ≤ normalizer (residual H : Set G) :=
    d.unitaryFive_central_involution_centralizers h hH hp U hc 1 z hz hz2
  obtain ⟨kz₀,hkz₀⟩ := local_centralizer_equiv _ (markedRightHom r F)
    ((inclusion_injective r.extension.left_le).comp F.right.injective) z
    (marked_long_full d h hH hp U hc r a F h1 z hz hz2)
  let i : centralizer ({z.val} : Set G) ≃
      (normalizer (residual H : Set G)).subgroupOf (centralizer ({z.val} : Set G)) := {
    toFun x := ⟨x,hzN x.property⟩
    invFun x := x.val
    left_inv _ := rfl
    right_inv _ := rfl }
  let kz := i.trans kz₀
  have hkz (x : centralizer ({z.val} : Set G)) :
      (kz x).val=markedRightHom r F ⟨x.val,hzN x.property⟩ := hkz₀ _
  have hzV : z.val ∈ (center (L.pCoreIn 2)).map (L.pCoreIn 2).subtype := by
    rw [←d.unitaryFive_inner_fixed_plane_center_eq_right_center h hH hp U hc] at hz
    exact hz.1
  have hzL : z.val ∈ normalizer (L : Set G) :=
    L.le_normalizer (pCoreIn_le 2 L (map_subtype_le _ hzV))
  let zD : (normalizer (L : Set G) ⊓ normalizer (residual H : Set G) : Subgroup G) := ⟨z.val,hzL,z.property⟩
  have hze : markedLeftHom r F ⟨z.val,hzL⟩ = z' := marked_overlap U r F zD
  have hAX : Nat.card {x : X // IsConj z.val x.val.val} =
      Nat.card (CommutingClassIncidence.Fiber t' z') := by
    apply Nat.card_congr (kt.subtypeEquiv ?_)
    intro x
    change IsConj z.val x.val.val ↔ IsConj z' (kt x).val
    rw [hkt,←hze]
    exact marked_left_class d h hH hp U hc r a F h0 ⟨z.val,hzL⟩ hzV hz2 ⟨x.val.val,x.property⟩
  have hB : Nat.card (CommutingClassIncidence.Fiber z.val t.val) =
      Nat.card (CommutingClassIncidence.Fiber z' t') := by
    apply Nat.card_congr (kz.subtypeEquiv ?_)
    intro x
    change IsConj t.val x.val ↔ IsConj t' (kz x).val
    rw [hkz]
    exact marked_right_class d h hH hp U hc r a F h0 t ht ht2 ⟨x.val,hzN x.property⟩
  have hC : Nat.card X = Nat.card (centralizer ({t'} : Set r.extension.carrier)) := Nat.card_congr kt
  have hZ := Nat.card_congr kz
  have hb := CommutingClassIncidence.balance z.val t.val
  have hb' := CommutingClassIncidence.balance z' t'
  change Nat.card {x : M // IsConj z.val x.val} * Nat.card X =
    Nat.card M * Nat.card {x : X // IsConj z.val x.val.val}
  apply Nat.eq_of_mul_eq_mul_left (Nat.card_pos (α := centralizer ({z.val} : Set G)))
  change Nat.card (centralizer ({z.val} : Set G)) *
    (Nat.card (CommutingClassIncidence.Fiber t.val z.val) * Nat.card X) = _
  calc
    _ = (Nat.card M * Nat.card (CommutingClassIncidence.Fiber z.val t.val)) * Nat.card X := by
      rw [←mul_assoc,hb]
    _ = Nat.card M * (Nat.card (centralizer ({z'} : Set r.extension.carrier)) *
        Nat.card (CommutingClassIncidence.Fiber t' z')) := by
      rw [hC,hB]
      rw [mul_assoc,mul_comm (Nat.card (CommutingClassIncidence.Fiber z' t')),←hb']
    _ = _ := by rw [←hAX,←hZ]; ring

/-- Every original long-class element in the marked short centralizer fixes
exactly one coset of its intersection with the full plane normalizer. -/
theorem marked_short_unique_fixed
    (t : normalizer (L : Set G))
    (ht : t.val ∈ (center (L.pCoreIn 2)).map (L.pCoreIn 2).subtype)
    (ht2 : orderOf t.val=2)
    (htshort : markedLeftHom r F t = r.extension.baseHom U.shortInvolution.val)
    (z : G) (hz : z ∈ (center (residual H)).map (residual H).subtype)
    (hz2 : orderOf z=2) :
    ∀ x : centralizer ({t.val} : Set G), IsConj z x.val →
      ∃! q : centralizer ({t.val} : Set G) ⧸
        (normalizer (L : Set G)).subgroupOf (centralizer ({t.val} : Set G)), x • q=q := by
  let M := centralizer ({t.val} : Set G)
  let X := (normalizer (L : Set G)).subgroupOf M
  let p : M → Prop := fun x => IsConj z x.val
  let V := (center (L.pCoreIn 2)).map (L.pCoreIn 2).subtype
  let : IsElementaryAbelian 2 V :=
    ((d.unitaryFive_plane_core_structure h hH hp U hc).2.1).map (L.pCoreIn 2).subtype
  have htJ : t.val ∈ centralizer (Stellmacher.elementaryAbelianMaxJ (T : Subgroup G) : Set G) := by
    rw [d.unitaryFive_thompson h hH hp U hc]
    exact V.le_centralizer ht
  obtain ⟨R,hR⟩ := Stellmacher.exists_centralizer_sylow_le_maxJ_normalizer T t.val htJ
  rw [d.unitaryFive_thompson_normalizer h hH hp U hc] at hR
  have hRX : (R : Subgroup M) ≤ X := fun x hx => hR (mem_map_of_mem M.subtype hx)
  apply UniqueFixedCoset.unique_of_class_count X p
  · intro g x
    have hc : IsConj x.val (g*x*g⁻¹).val := isConj_iff.mpr ⟨g.val,rfl⟩
    exact ⟨fun hh => hh.trans hc.symm,fun hh => hh.trans hc⟩
  · intro x hx
    have hx2 : orderOf x=2 := by
      obtain ⟨g,hg⟩ := isConj_iff.mp hx
      have he := (MulAut.conj g).orderOf_eq z
      change orderOf (g*z*g⁻¹)=orderOf z at he
      rw [hg] at he
      exact (Subgroup.orderOf_coe x).symm.trans (he.trans hz2)
    obtain ⟨w,hw⟩ := R.exists_isConj_of_orderOf_eq_prime_pow
      (x := x) (n := 1) (by simpa using hx2)
    obtain ⟨g,hg⟩ := isConj_iff.mp hw
    refine ⟨QuotientGroup.mk g⁻¹,(UniqueFixedCoset.fixed_iff X x g⁻¹).mpr ?_⟩
    simp only [inv_inv]
    change g*x*g⁻¹ ∈ X
    rw [show g*x*g⁻¹=w.val from hg]
    exact hRX w.property
  · exact class_count d h hH hp U hc r a F h0 h1 t ht ht2 htshort
      ⟨z,(residual H).le_normalizer (map_subtype_le _ hz)⟩ hz hz2

end UnitaryFiveFusion
/-- The original chosen short root has the actual F.4.42 unique fixed cosets,
retaining the complete marking and every full-extension range equation. -/
theorem Preparation.unitaryFive_marked_short_unique_cosets
    (d : Preparation T L H A C (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hp : Group.IsPerfect (residual H)) (U : Model 4)
    (hc : Nonempty (RankTwoAmalgam.Iso
        (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) U.amalgam) ∨
      Nonempty (RankTwoAmalgam.Iso
        (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) U.amalgam.reverse))
    (r : UnitaryFiveNormalizerMarking L (residual H) ((T : Subgroup G) ⊓ L) U) :
    ∃ a : UnitarySource.MarkedMiddleAction L (residual H) ((T : Subgroup G) ⊓ L) U.amalgam.reverse,
    ∃ ell : UnitaryNativeLift.Five.LiftReverse U a,
    ∃ F : RankTwoAmalgam.Iso (UnitaryCompletion.normalizerDiagram L (residual H))
        r.extension.amalgam.reverse,
      (∀ x, (F.left (inclusion r.left_le x)).val = MulAut.conj (a.comparison.left x).val) ∧
      (∀ x, (F.right (inclusion r.right_le x)).val = MulAut.conj (a.comparison.right x).val) ∧
      (∀ z, (F.middle z).val = (ell.action z).val) ∧
      r.extension.carrier = inner U.Carrier ⊔
        ((Chapter5.UnitaryNativeLift.Five.flagAutomorphisms U).subtype.comp ell.action).range ∧
      r.extension.left = U.leftParabolic.map MulAut.conj ⊔
        ((Chapter5.UnitaryNativeLift.Five.flagAutomorphisms U).subtype.comp ell.action).range ∧
      r.extension.right = U.rightParabolic.map MulAut.conj ⊔
        ((Chapter5.UnitaryNativeLift.Five.flagAutomorphisms U).subtype.comp ell.action).range ∧
      r.extension.middle =
        ((Chapter5.UnitaryNativeLift.Five.flagAutomorphisms U).subtype.comp ell.action).range ∧
      ∃ t : (normalizerAmalgam L (residual H)).M₁₂,
        t.val ∈ (center (L.pCoreIn 2)).map (L.pCoreIn 2).subtype ∧
        orderOf t.val=2 ∧ t.val ∈ sourceS L H ∧
        (F.middle t).val = MulAut.conj U.shortInvolution.val ∧
        ∀ z : G, z ∈ (center (residual H)).map (residual H).subtype → orderOf z=2 →
        ∀ x : centralizer ({t.val} : Set G), IsConj z x.val →
          ∃! q : centralizer ({t.val} : Set G) ⧸
            (normalizer (L : Set G)).subgroupOf (centralizer ({t.val} : Set G)), x • q=q := by
  obtain ⟨a,ell,F,h0,h1,hD,hE,hl,hr,hm,t,ht,ht2,htS,_,_,hshort,_⟩ :=
    d.unitaryFive_marked_short_root_control h hH hp U hc r
  refine ⟨a,ell,F,h0,h1,hD,hE,hl,hr,hm,t,ht,ht2,htS,hshort,?_⟩
  intro z hz hz2
  apply UnitaryFiveFusion.marked_short_unique_fixed d h hH hp U hc r a F h0 h1
    (inclusion inf_le_left t) ht ht2 ?_ z hz hz2
  apply Subtype.ext
  exact (congrArg Subtype.val (F.left_commutes t)).trans hshort

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
