module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalTrialityExtensionOrder
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalTrialityExtremality
import all CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalTrialityRootPair
import all CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalTrialityExtremality
import all CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalTrialityCompletionFusion

/-!
# Paired involution classes through the fixed triality normalizer maps

The local root reductions provide simultaneous conjugacy paths in the native
triality group and the original ambient group. Sylow conjugacy in each full
normalizer extends this paired catalogue from the original S=T to every
involution of that normalizer. The left-hand transport uses agreement of the
full-normalizer maps on their whole common subgroup; the original reversed
comparison and pinned roots are retained throughout.

Once the two extension roots are known to be nonconjugate, this paired
catalogue proves both directions of ambient class membership under each
full-normalizer map, including for elements which are not involutions.
The companion Thompson comparison derives that nonfusion from the designated
short-root extremality and marked centralizer supplied by its separate owner.

Source: Aschbacher--Smith F.4.35, F.4.38 and F.4.43, printed pp.292,294,296,
and 5.3.3, p.659 (`refs/quasithin.pdf`). Internal imports reuse the proved
local root paths and order calculations without changing their public APIs.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open Triality.Standard Triality.Standard.Parabolics
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
open ChapterF.SourceCompletion.TrialityNonbinary
open TrialityCompletionFusion

private theorem pair_from_sylow {X Y : Type*} [Group X] [Finite X] [Group Y]
    (T : Sylow 2 X) (N : Subgroup X) (hTN : (T : Subgroup X) ≤ N)
    (f : N →* Y) (z v : X) (z' v' : Y)
    (hs : ∀ u : N, u.val ∈ (T : Subgroup X) → orderOf u = 2 →
      (IsConj z u.val ∧ IsConj z' (f u)) ∨ (IsConj v u.val ∧ IsConj v' (f u)))
    (u : N) (hu : orderOf u = 2) :
    (IsConj z u.val ∧ IsConj z' (f u)) ∨ (IsConj v u.val ∧ IsConj v' (f u)) := by
  obtain ⟨w,hw⟩ := (T.subtype hTN).exists_isConj_of_orderOf_eq_prime_pow
    (x := u) (n := 1) (by simpa using hu)
  have hw2 : orderOf (w.val : N) = 2 := by
    obtain ⟨g,hg⟩ := isConj_iff.mp hw
    rw [←hg]
    exact ((MulAut.conj g).orderOf_eq u).trans hu
  rcases hs w.val w.property hw2 with ⟨h1,h2⟩ | ⟨h1,h2⟩
  · exact Or.inl ⟨h1.trans (N.subtype.map_isConj hw).symm,
      h2.trans (f.map_isConj hw).symm⟩
  · exact Or.inr ⟨h1.trans (N.subtype.map_isConj hw).symm,
      h2.trans (f.map_isConj hw).symm⟩

variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
/-- Simultaneous source and native class paths for the fixed comparison. -/
private theorem comparison_class_pair {L K S : Subgroup G}
    (m : ℕ) (hm : 0 < m)
    (e : RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,K] S) (nativeAmalgam m hm).reverse)
    (x : parabolic (binaryParameters m hm) .arms)
    (hx : x.val ∈ unipotent (binaryParameters m hm)) (hx2 : orderOf x = 2) :
    let P := binaryParameters m hm
    (IsConj (e.right.symm (longElement P rfl)).val (e.right.symm x).val ∧
      IsConj (longElement P rfl).val x.val) ∨
    (IsConj (e.right.symm (shortElement P rfl)).val (e.right.symm x).val ∧
      IsConj (shortElement P rfl).val x.val) := by
  let P := binaryParameters m hm
  let Y := ChapterF.Source.parabolic ![L,K] S 1
  let X := ChapterF.Source.parabolic ![L,K] S 0
  let f : parabolic P .arms →* G := Y.subtype.comp e.right.symm.toMonoidHom
  let l : parabolic P .central →* G := X.subtype.comp e.left.symm.toMonoidHom
  exact TrialityExtremality.compatible_class_pair m hm f l
    (fun a ha hu hv => TrialityExtremality.inclusion_amalgam_inverse_agree X Y
      (parabolic P .central) (borel P) (parabolic P .arms)
      (borel_le_parabolic P .central) (borel_le_parabolic P .arms) e a ha hu hv) x hx hx2

/-- The original right full-normalizer map preserves the paired class labels. -/
theorem Preparation.triality_right_normalizer_class_pair
    {T : Sylow 2 G} {L W H A B : Subgroup G} {n : ℕ}
    (d : Preparation T L H A B (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hp : Group.IsPerfect (residual H)) (m : ℕ) (hm : 0 < m)
    (e : RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) (nativeAmalgam m hm).reverse)
    (a : TrialityNormalizerMarking L (residual H) (sourceS L H) m hm e)
    (x : normalizer (residual H : Set G)) (hx : orderOf x = 2) :
    let P := binaryParameters m hm
    let f := (inclusion a.extension.left_le).comp a.comparison.right.toMonoidHom
    (IsConj (e.right.symm (longElement P rfl)).val x.val ∧
      IsConj (a.extension.baseHom (longElement P rfl).val) (f x)) ∨
    (IsConj (e.right.symm (shortElement P rfl)).val x.val ∧
      IsConj (a.extension.baseHom (shortElement P rfl).val) (f x)) := by
  let P := binaryParameters m hm
  let Y := ChapterF.Source.parabolic ![L,residual H] (sourceS L H) 1
  let f := (inclusion a.extension.left_le).comp a.comparison.right.toMonoidHom
  have hTY : (T : Subgroup G) ≤ Y := by
    rw [←d.triality_sourceS_eq_sylow h hH hp m hm (Or.inr ⟨e⟩)]
    exact le_sup_right.trans le_sup_left
  apply pair_from_sylow T _ (hTY.trans a.right_le) f _ _ _ _ ?_ x hx
  intro u hu hu2
  let y : Y := ⟨u.val,hTY hu⟩
  have hy : (e.right y).val ∈ unipotent P := by
    have hU := (d.triality_right_unipotent_image h hH.1.1.2 P rfl e).trans
      (d.triality_sourceS_eq_sylow h hH hp m hm (Or.inr ⟨e⟩))
    obtain ⟨w,hw,he⟩ := hU.ge hu
    have hyw : e.right.symm w = y := Subtype.ext he
    rw [←hyw,e.right.apply_symm_apply]
    exact hw
  have hy2 : orderOf (e.right y) = 2 := by
    rw [e.right.orderOf_eq,←Subgroup.orderOf_coe]
    exact (Subgroup.orderOf_coe u).trans hu2
  have hf : f u = a.extension.baseHom (e.right y).val := by
    apply Subtype.ext
    exact a.right_marked y
  have huval : (e.right.symm (e.right y)).val = u.val := by
    rw [e.right.symm_apply_apply]
  rcases comparison_class_pair m hm e (e.right y) hy hy2 with
    ⟨h1,h2⟩ | ⟨h1,h2⟩
  · exact Or.inl ⟨huval ▸ h1,hf.symm ▸ a.extension.baseHom.map_isConj h2⟩
  · exact Or.inr ⟨huval ▸ h1,hf.symm ▸ a.extension.baseHom.map_isConj h2⟩

omit [Finite G] in
/-- Both full-normalizer maps agree on the literal common subgroup. -/
theorem TrialityNormalizerMarking.homs_agree
    {L K S : Subgroup G} {m : ℕ} {hm : 0 < m}
    {e : RankTwoAmalgam.Iso (sourceParabolicAmalgam ![L,K] S) (nativeAmalgam m hm).reverse}
    (a : TrialityNormalizerMarking L K S m hm e)
    (x : (normalizer (L : Set G) ⊓ normalizer (K : Set G) : Subgroup G)) :
    inclusion a.extension.right_le (a.comparison.left (inclusion inf_le_left x)) =
      inclusion a.extension.left_le (a.comparison.right (inclusion inf_le_right x)) := by
  apply Subtype.ext
  exact (congrArg Subtype.val (a.comparison.left_commutes x)).trans
    (congrArg Subtype.val (a.comparison.right_commutes x)).symm

/-- The original left full-normalizer map preserves the same paired class labels. -/
theorem Preparation.triality_left_normalizer_class_pair
    {T : Sylow 2 G} {L W H A B : Subgroup G} {n : ℕ}
    (d : Preparation T L H A B (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hp : Group.IsPerfect (residual H)) (m : ℕ) (hm : 0 < m)
    (e : RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) (nativeAmalgam m hm).reverse)
    (a : TrialityNormalizerMarking L (residual H) (sourceS L H) m hm e)
    (x : normalizer (L : Set G)) (hx : orderOf x = 2) :
    let P := binaryParameters m hm
    let f := (inclusion a.extension.right_le).comp a.comparison.left.toMonoidHom
    (IsConj (e.right.symm (longElement P rfl)).val x.val ∧
      IsConj (a.extension.baseHom (longElement P rfl).val) (f x)) ∨
    (IsConj (e.right.symm (shortElement P rfl)).val x.val ∧
      IsConj (a.extension.baseHom (shortElement P rfl).val) (f x)) := by
  let P := binaryParameters m hm
  let f := (inclusion a.extension.right_le).comp a.comparison.left.toMonoidHom
  have hTD : (T : Subgroup G) ≤ normalizer (L : Set G) ⊓ normalizer (residual H : Set G) := by
    rw [←d.triality_sourceS_eq_sylow h hH hp m hm (Or.inr ⟨e⟩)]
    exact le_inf ((le_sup_right.trans le_sup_left).trans a.left_le)
      ((le_sup_right.trans le_sup_left).trans a.right_le)
  apply pair_from_sylow T _ (hTD.trans inf_le_left) f _ _ _ _ ?_ x hx
  intro u hu hu2
  let b : (normalizer (L : Set G) ⊓ normalizer (residual H : Set G) : Subgroup G) := ⟨u.val,hTD hu⟩
  let w := inclusion (inf_le_right : normalizer (L : Set G) ⊓
    normalizer (residual H : Set G) ≤ normalizer (residual H : Set G)) b
  have hw2 : orderOf w = 2 := by
    rw [←Subgroup.orderOf_coe]
    exact (Subgroup.orderOf_coe u).trans hu2
  have hf : f u = inclusion a.extension.left_le (a.comparison.right w) := a.homs_agree b
  rcases d.triality_right_normalizer_class_pair h hH hp m hm e a w hw2 with
    ⟨h1,h2⟩ | ⟨h1,h2⟩
  · exact Or.inl ⟨h1,hf.symm ▸ h2⟩
  · exact Or.inr ⟨h1,hf.symm ▸ h2⟩

/-- All ambient involutions are covered by the roots of the supplied comparison. -/
theorem Preparation.triality_pinned_ambient_involution_classes
    {T : Sylow 2 G} {L W H A B : Subgroup G} {n : ℕ}
    (d : Preparation T L H A B (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hp : Group.IsPerfect (residual H)) (m : ℕ) (hm : 0 < m)
    (e : RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) (nativeAmalgam m hm).reverse)
    (x : G) (hx : orderOf x = 2) :
    let P := binaryParameters m hm
    IsConj (e.right.symm (longElement P rfl)).val x ∨
      IsConj (e.right.symm (shortElement P rfl)).val x := by
  let a := d.trialityNormalizerMarking h hH hp m hm e
  obtain ⟨w,hw⟩ := T.exists_isConj_of_orderOf_eq_prime_pow (x := x) (n := 1)
    (by simpa using hx)
  have hTN : (T : Subgroup G) ≤ normalizer (residual H : Set G) := by
    rw [←d.triality_sourceS_eq_sylow h hH hp m hm (Or.inr ⟨e⟩)]
    exact (le_sup_right.trans le_sup_left).trans a.right_le
  let u : normalizer (residual H : Set G) := ⟨w.val,hTN w.property⟩
  have hu2 : orderOf u = 2 := by
    rw [←Subgroup.orderOf_coe]
    obtain ⟨g,hg⟩ := isConj_iff.mp hw
    change orderOf w.val = 2
    rw [←hg]
    exact ((MulAut.conj g).orderOf_eq x).trans hx
  rcases d.triality_right_normalizer_class_pair h hH hp m hm e a u hu2 with
    ⟨h1,_⟩ | ⟨h1,_⟩
  · exact Or.inl (h1.trans hw.symm)
  · exact Or.inr (h1.trans hw.symm)

/-- The fixed long and short representatives have order two. -/
theorem triality_pinned_root_orders (m : ℕ) (hm : 0 < m) :
    let P := binaryParameters m hm
    orderOf (longElement P rfl) = 2 ∧ orderOf (shortElement P rfl) = 2 :=
  ⟨triality_longElement_order _ rfl,TrialityRootPair.short_order _ rfl 1 one_ne_zero⟩

private theorem conjugate_order {X : Type*} [Group X] {x y : X} (h : IsConj x y) :
    orderOf x = orderOf y := by
  obtain ⟨g,rfl⟩ := isConj_iff.mp h
  exact ((MulAut.conj g).orderOf_eq x).symm

private theorem fusion_of_class_pair {X Y : Type*} [Group X] [Group Y]
    (N : Subgroup X) (f : N →* Y) (hf : Function.Injective f)
    (z v : X) (z' v' : Y)
    (hz : orderOf z = 2) (hv : orderOf v = 2)
    (hz' : orderOf z' = 2) (hv' : orderOf v' = 2)
    (hn : ¬ IsConj z v) (hn' : ¬ IsConj z' v')
    (hpair : ∀ x : N, orderOf x = 2 →
      (IsConj z x.val ∧ IsConj z' (f x)) ∨ (IsConj v x.val ∧ IsConj v' (f x)))
    (x : N) :
    (IsConj z x.val ↔ IsConj z' (f x)) ∧ (IsConj v x.val ↔ IsConj v' (f x)) := by
  by_cases hx : orderOf x = 2
  · rcases hpair x hx with ⟨h1,h2⟩ | ⟨h1,h2⟩
    · exact ⟨iff_of_true h1 h2,iff_of_false (fun h3 => hn (h1.trans h3.symm))
        (fun h3 => hn' (h2.trans h3.symm))⟩
    · exact ⟨iff_of_false (fun h3 => hn (h3.trans h1.symm))
        (fun h3 => hn' (h3.trans h2.symm)),iff_of_true h1 h2⟩
  · have hX (u : X) (hu : orderOf u = 2) : ¬ IsConj u x.val := by
      intro hc
      exact hx ((Subgroup.orderOf_coe x).symm.trans ((conjugate_order hc).symm.trans hu))
    have hY (u : Y) (hu : orderOf u = 2) : ¬ IsConj u (f x) := by
      intro hc
      exact hx ((orderOf_injective f hf x).symm.trans ((conjugate_order hc).symm.trans hu))
    exact ⟨iff_of_false (hX z hz) (hY z' hz'),iff_of_false (hX v hv) (hY v' hv')⟩

/-- If the two extension roots are distinct classes, both original whole-normalizer
maps preserve and reflect ambient membership in those same two classes. -/
theorem Preparation.triality_full_normalizer_fusion
    {T : Sylow 2 G} {L W H A B : Subgroup G} {n : ℕ}
    (d : Preparation T L H A B (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hp : Group.IsPerfect (residual H)) (m : ℕ) (hm : 0 < m)
    (e : RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) (nativeAmalgam m hm).reverse)
    (a : TrialityNormalizerMarking L (residual H) (sourceS L H) m hm e)
    (hnon : ¬ IsConj (a.extension.baseHom (longElement (binaryParameters m hm) rfl).val)
      (a.extension.baseHom (shortElement (binaryParameters m hm) rfl).val)) :
    let P := binaryParameters m hm
    let z := (e.right.symm (longElement P rfl)).val
    let v := (e.right.symm (shortElement P rfl)).val
    let z' := a.extension.baseHom (longElement P rfl).val
    let v' := a.extension.baseHom (shortElement P rfl).val
    (∀ x : normalizer (L : Set G),
      (IsConj z x.val ↔ IsConj z' (inclusion a.extension.right_le (a.comparison.left x))) ∧
      (IsConj v x.val ↔ IsConj v' (inclusion a.extension.right_le (a.comparison.left x)))) ∧
    (∀ x : normalizer (residual H : Set G),
      (IsConj z x.val ↔ IsConj z' (inclusion a.extension.left_le (a.comparison.right x))) ∧
      (IsConj v x.val ↔ IsConj v' (inclusion a.extension.left_le (a.comparison.right x)))) := by
  let P := binaryParameters m hm
  let z := (e.right.symm (longElement P rfl)).val
  let v := (e.right.symm (shortElement P rfl)).val
  let z' := a.extension.baseHom (longElement P rfl).val
  let v' := a.extension.baseHom (shortElement P rfl).val
  have hroot := triality_pinned_root_orders m hm
  have hz : orderOf z = 2 := (Subgroup.orderOf_coe _).trans
    ((e.right.symm.orderOf_eq _).trans hroot.1)
  have hv : orderOf v = 2 := (Subgroup.orderOf_coe _).trans
    ((e.right.symm.orderOf_eq _).trans hroot.2)
  have hz' : orderOf z' = 2 :=
    (orderOf_injective a.extension.baseHom (a.extension.baseHom_injective (conj_injective m hm)) _).trans
      ((Subgroup.orderOf_coe _).trans hroot.1)
  have hv' : orderOf v' = 2 :=
    (orderOf_injective a.extension.baseHom (a.extension.baseHom_injective (conj_injective m hm)) _).trans
      ((Subgroup.orderOf_coe _).trans hroot.2)
  have hn := d.triality_comparison_involution_nonfusion h hH hp m hm e
  constructor
  · exact fusion_of_class_pair _ ((inclusion a.extension.right_le).comp a.comparison.left.toMonoidHom)
      ((inclusion_injective a.extension.right_le).comp a.comparison.left.injective) z v z' v' hz hv hz' hv' hn hnon
      (fun x hx => d.triality_left_normalizer_class_pair h hH hp m hm e a x hx)
  · exact fusion_of_class_pair _ ((inclusion a.extension.left_le).comp a.comparison.right.toMonoidHom)
      ((inclusion_injective a.extension.left_le).comp a.comparison.right.injective) z v z' v' hz hv hz' hv' hn hnon
      (fun x hx => d.triality_right_normalizer_class_pair h hH hp m hm e a x hx)


end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
