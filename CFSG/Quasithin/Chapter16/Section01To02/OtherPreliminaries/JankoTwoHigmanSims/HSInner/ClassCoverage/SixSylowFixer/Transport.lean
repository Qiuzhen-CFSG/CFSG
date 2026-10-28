module
public import CFSG.Quasithin.Chapter16.Section01To02.OtherPreliminaries.JankoTwoHigmanSims.HSInner.ClassCoverage.SixSylowFixer
public import CFSG.Quasithin.Chapter16.Section01To02.OtherPreliminaries.JankoTwoHigmanSims.HSInner.ClassCoverage
public import Theory.GroupTheory.GeneralizedFitting.RelativeComponent
/-!
# The marked HS product centralizer and arbitrary component Sylow fixers

Multiplication identifies the actual centralizer of t with its cyclic factor
and H. Its unique component is the original D. The checked base-Sylow
certificate transports inside D to every Sylow subgroup: a nontrivial
involution other than t fixing that Sylow is in the central class, or becomes
so after multiplication by t.

Source: Aschbacher–Smith E.6.23, printed p.254, and 16.1.5(10), p.1172.
-/
public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter16.OtherPreliminaries.JankoTwoHigmanSims.HSInner.ClassCoverage.ProductEmbedding.SylowFixerCertificate
open Sporadic.LeechRelated.HS
local notation "C" => centralizer (Set.singleton t : Set Carrier)

theorem cyclic_inter_complement : Disjoint (zpowers t) H := by
  apply disjoint_def.mpr
  intro x hx hh
  have hc : x ∈ centralizer (D : Set Carrier) := by
    have ht : t ∈ centralizer (D : Set Carrier) := by
      intro d hd
      exact mem_centralizer_singleton_iff.mp (D_le_centralizer hd)
    exact zpowers_le.mpr ht hx
  exact mem_bot.mp (H_inf_centralizer_D ▸ ⟨hh, hc⟩)

def product : zpowers t × H →* C :=
  (inclusion (zpowers_le.mpr (mem_centralizer_singleton_iff.mpr rfl))).noncommCoprod
    (inclusion H_le_centralizer) (by
      intro z h
      apply Subtype.ext
      change (z : Carrier) * h = (h : Carrier) * z
      obtain ⟨n,hn⟩ := mem_zpowers_iff.mp z.property
      rw [← hn]
      exact ((show Commute t (h : Carrier) from
        (mem_centralizer_singleton_iff.mp (H_le_centralizer h.property)).symm).zpow_left n).eq)

theorem product_injective : Function.Injective product := by
  intro x y he
  exact mul_injective_of_disjoint cyclic_inter_complement (congrArg Subtype.val he)

theorem product_surjective : Function.Surjective product := by
  apply (product_injective.bijective_of_nat_card_le ?_).surjective
  rw [Nat.card_prod, Nat.card_zpowers, t_order, H_card]
  obtain ⟨e⟩ := product_centralizer_equiv
  exact (Nat.card_congr e.toEquiv).trans product_card |>.le

theorem centralizer_element (x : Carrier) (hx : x ∈ C) :
    ∃ h ∈ H, x = h ∨ x = t * h := by
  obtain ⟨⟨z,h⟩,he⟩ := product_surjective ⟨x,hx⟩
  have he' : (z : Carrier) * h = x := congrArg Subtype.val he
  have hz : (z : Carrier) = 1 ∨ (z : Carrier) = t := by
    have hm := z.property
    rw [mem_zpowers_iff_mem_range_orderOf, t_order] at hm
    obtain ⟨n,hn,he⟩ := Finset.mem_image.mp hm
    have hn2 := Finset.mem_range.mp hn
    interval_cases n
    · left; simpa using he.symm
    · right; simpa using he.symm
  refine ⟨h,h.property,?_⟩
  rcases hz with hz | hz
  · exact Or.inl (by simpa [hz] using he'.symm)
  · exact Or.inr (by simpa [hz] using he'.symm)


theorem centralizer_le_normalizer_D : C ≤ normalizer (D : Set Carrier) := by
  intro x hx
  obtain ⟨h, hh, rfl | rfl⟩ := centralizer_element x hx
  · exact H_le_normalizer hh
  · apply (normalizer (D : Set Carrier)).mul_mem _ (H_le_normalizer hh)
    apply centralizer_le_normalizer
    intro y hy
    exact mem_centralizer_singleton_iff.mp (D_le_centralizer hy)

theorem centralizer_D_le_cyclic : C ⊓ centralizer (D : Set Carrier) ≤ zpowers t := by
  intro x hx
  obtain ⟨h, hh, he | he⟩ := centralizer_element x hx.1
  · have hh1 : h = 1 := mem_bot.mp (H_inf_centralizer_D ▸ ⟨hh, he ▸ hx.2⟩)
    rw [he, hh1]; exact one_mem _
  · have ht : t ∈ centralizer (D : Set Carrier) := by
      intro d hd
      exact mem_centralizer_singleton_iff.mp (D_le_centralizer hd)
    have hc : h ∈ centralizer (D : Set Carrier) := by
      have hmem := (centralizer (D : Set Carrier)).mul_mem
        ((centralizer (D : Set Carrier)).inv_mem ht) hx.2
      simpa only [he, inv_mul_cancel_left] using hmem
    have hh1 : h = 1 := mem_bot.mp (H_inf_centralizer_D ▸ ⟨hh, hc⟩)
    rw [he, hh1, mul_one]; exact mem_zpowers _

theorem component_eq_D (S : Subgroup Carrier) (hS : IsComponentIn S C) : S = D := by
  let D' := D.subgroupOf C
  let : D'.Normal := (normal_subgroupOf_iff_le_normalizer D_le_centralizer).mpr
    centralizer_le_normalizer_D
  obtain ⟨e⟩ := D_equiv_A6
  let : IsQuasisimple A6 := GLS3.Chapter5.SchurPresentation.alternatingGroup_isQuasisimple 1
  let : IsQuasisimple D := IsQuasisimple.of_mulEquiv e.symm
  have hD' : IsComponent C D' := ⟨(inferInstance : D'.Normal).isSubnormal,
    IsQuasisimple.of_mulEquiv (subgroupOfEquivOfLe D_le_centralizer).symm⟩
  rcases hS.2.normal_dichotomy D' with hl | hc
  · have he := hS.2.eq_of_le hD' hl
    have he' := congrArg (Subgroup.map (C).subtype) he
    have hDC : D ≤ C := D_le_centralizer
    simpa only [map_subgroupOf_eq_of_le hS.1, D',
      map_subgroupOf_eq_of_le hDC] using he'
  · have hle : S ≤ zpowers t := by
      intro x hx
      apply centralizer_D_le_cyclic
      refine ⟨hS.1 hx, ?_⟩
      intro y hy
      have hh := (commutator_eq_bot_iff_le_centralizer.mp hc)
        (show (⟨x,hS.1 hx⟩ : C) ∈ S.subgroupOf C from hx)
        (⟨y,D_le_centralizer hy⟩ : C) hy
      exact congrArg Subtype.val hh
    let : IsQuasisimple S := hS.quasisimple
    let : CommGroup (zpowers t) := IsCyclic.commGroup
    let : Nontrivial S := (nontrivial_iff_ne_bot S).mpr hS.ne_bot
    let : Group.IsSolvable S := Group.isSolvable_of_isSolvable_injective
      (inclusion_injective hle)
    exact (Group.IsPerfect.not_isSolvable S inferInstance).elim

theorem fixer_central_class (x : Carrier) (hx : x ∈ C)
    (hc : ∀ i, Commute x (sylowGenerator i))
    (hx2 : orderOf x = 2) (hnt : x ≠ t) :
    IsConj EvenLocalCandidates.e0 x ∨ IsConj EvenLocalCandidates.e0 (x * t) := by
  obtain ⟨h, hh, he | he⟩ := centralizer_element x hx
  · exact he ▸ complement_fixer_central_class h hh (he ▸ hc) (he ▸ hx2)
  · have hct : Commute t h :=
      (mem_centralizer_singleton_iff.mp (H_le_centralizer hh)).symm
    have hn : h ≠ 1 := by intro hz; exact hnt (by simp only [he,hz,mul_one])
    have ht2 := pow_orderOf_eq_one t
    rw [t_order] at ht2
    have hh2 : h ^ 2 = 1 := by
      have hv := pow_orderOf_eq_one x
      rw [hx2,he,hct.mul_pow,ht2,one_mul] at hv
      exact hv
    have hc' : ∀ i, Commute h (sylowGenerator i) := by
      intro i
      have ht := mem_centralizer_singleton_iff.mp (D_le_centralizer (sylowGenerator_mem_D i))
      have hv := (hc i).eq
      rw [he] at hv
      change h * sylowGenerator i = sylowGenerator i * h
      apply mul_left_cancel (a := t)
      calc
        t * (h * sylowGenerator i) = (t * h) * sylowGenerator i := (mul_assoc _ _ _).symm
        _ = sylowGenerator i * (t * h) := hv
        _ = t * (sylowGenerator i * h) := by rw [← mul_assoc, ht, mul_assoc]
    rcases complement_fixer_central_class h hh hc' (orderOf_eq_prime hh2 hn) with hc0 | hc1
    · right
      have hv : x * t = h := by rw [he, hct.eq, mul_assoc, ← pow_two, ht2, mul_one]
      exact hv.symm ▸ hc0
    · left
      have hv : x = h * t := he.trans hct.eq
      exact hv.symm ▸ hc1


theorem sylow_fixer_central_class (P : Sylow 2 D)
    (x : Carrier) (hx : x ∈ C)
    (hc : ∀ y ∈ (P : Subgroup D), Commute x (y : Carrier))
    (hx2 : orderOf x = 2) (hnt : x ≠ t) :
    IsConj EvenLocalCandidates.e0 x ∨ IsConj EvenLocalCandidates.e0 (x * t) := by
  obtain ⟨k, hk⟩ := MulAction.exists_smul_eq D P baseSylow
  let e : MulAut Carrier := MulAut.conj (k : Carrier)
  have hkt : Commute (k : Carrier) t :=
    mem_centralizer_singleton_iff.mp (D_le_centralizer k.property)
  have het : e t = t := mul_inv_eq_iff_eq_mul.mpr hkt.eq
  have hxC : e x ∈ C := by
    apply mem_centralizer_singleton_iff.mpr
    have h := (show Commute x t from mem_centralizer_singleton_iff.mp hx).map e.toMonoidHom
    change Commute (e x) (e t) at h
    exact het ▸ h.eq
  have hfix (i : Fin 2) : Commute (e x) (sylowGenerator i) := by
    have hm : (⟨sylowGenerator i,sylowGenerator_mem_D i⟩ : D) ∈ (k • P : Sylow 2 D) :=
      hk.symm ▸ sylowGenerator_mem_baseSylow i
    change (⟨sylowGenerator i,sylowGenerator_mem_D i⟩ : D) ∈
      (P : Subgroup D).map (MulAut.conj k).toMonoidHom at hm
    obtain ⟨y,hy,he⟩ := hm
    have he' : e (y : Carrier) = sylowGenerator i := congrArg Subtype.val he
    exact he' ▸ (hc y hy).map e.toMonoidHom
  have hn : e x ≠ t := by intro h; exact hnt (e.injective (h.trans het.symm))
  have ho : orderOf (e x) = 2 := (e.orderOf_eq x).trans hx2
  rcases fixer_central_class (e x) hxC hfix ho hn with h | h
  · exact Or.inl (h.trans (isConj_iff.mpr ⟨(k : Carrier),rfl⟩).symm)
  · right
    have h' : IsConj EvenLocalCandidates.e0 (e (x*t)) := by
      simpa only [map_mul,het] using h
    exact h'.trans (isConj_iff.mpr ⟨(k : Carrier),rfl⟩).symm
end CFSG.Quasithin.Chapter16.OtherPreliminaries.JankoTwoHigmanSims.HSInner.ClassCoverage.ProductEmbedding.SylowFixerCertificate
