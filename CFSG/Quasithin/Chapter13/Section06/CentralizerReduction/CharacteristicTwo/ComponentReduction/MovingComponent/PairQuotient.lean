module

public import Theory.GroupTheory.GeneralizedFitting.ComponentCalculus
public import Theory.GroupTheory.NormalizerAction
public import Theory.GroupTheory.SubgroupConjugation
public import Mathlib.GroupTheory.NoncommCoprod

/-!
# Coordinates for the central quotient of a moving component pair

An index-two component normalizer gives precisely two conjugates. Distinct
components commute. Multiplication identifies the center quotient of their
join with the product of the individual center quotients: its inverse image
of the center is exactly the product of the two centers. This retains every
central cover. The factor formulas use the actual normalizer quotient K*.

Source: Aschbacher–Smith, combined 1 March 2004 manuscript, the moving
component paragraph in 13.6.6, printed p.927. The index and the single-factor
model equivalence remain explicit; neither the product nor its coordinates
is an input.
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentReduction.MovingComponent
open Subgroup Theory.GroupTheory
open scoped Pointwise
variable {H : Type*} [Group H]

private theorem centralProduct_quotient (K J : Subgroup H) (hc : ⁅K, J⁆ = ⊥) :
    ∃ e : (↥(K ⊔ J) ⧸ center ↥(K ⊔ J)) ≃* ((K ⧸ center K) × (J ⧸ center J)),
      ∀ (k : K) (j : J),
        e (QuotientGroup.mk' (center ↥(K ⊔ J))
          ⟨k * j, mul_mem ((show K ≤ K ⊔ J from le_sup_left) k.property) ((show J ≤ K ⊔ J from le_sup_right) j.property)⟩) =
        (QuotientGroup.mk' (center K) k, QuotientGroup.mk' (center J) j) := by
  have hcomm (k : K) (j : J) : Commute (k : H) (j : H) :=
    (mem_centralizer_iff.mp ((commutator_eq_bot_iff_le_centralizer.mp hc) k.property)
      j j.property).symm
  let f : K × J →* ↥(K ⊔ J) :=
    ((inclusion (show K ≤ K ⊔ J from le_sup_left)).noncommCoprod
      (inclusion (show J ≤ K ⊔ J from le_sup_right))
      (fun k j => Subtype.ext (hcomm k j).eq))
  have hf : Function.Surjective f := by
    rintro ⟨x, hx⟩
    have hJN : J ≤ normalizer (K : Set H) :=
      (commutator_eq_bot_iff_le_centralizer.mp ((commutator_comm J K).trans hc)).trans
        (Subgroup.centralizer_le_normalizer _)
    rw [← SetLike.mem_coe, coe_mul_of_right_le_normalizer_left K J hJN] at hx
    obtain ⟨k, hk, j, hj, he⟩ := hx
    exact ⟨(⟨k, hk⟩, ⟨j, hj⟩), Subtype.ext he⟩
  let F := (QuotientGroup.mk' (center ↥(K ⊔ J))).comp f
  let Q := (QuotientGroup.mk' (center K)).prodMap (QuotientGroup.mk' (center J))
  have hF : Function.Surjective F := (QuotientGroup.mk'_surjective _).comp hf
  have hQ : Function.Surjective Q := by
    rintro ⟨x, y⟩
    obtain ⟨k, rfl⟩ := QuotientGroup.mk'_surjective (center K) x
    obtain ⟨j, rfl⟩ := QuotientGroup.mk'_surjective (center J) y
    exact ⟨(k, j), rfl⟩
  have hker : F.ker = Q.ker := by
    ext ⟨k, j⟩
    change QuotientGroup.mk' (center ↥(K ⊔ J)) (f (k, j)) = 1 ↔
      (QuotientGroup.mk' (center K) k, QuotientGroup.mk' (center J) j) = (1, 1)
    rw [Prod.mk.injEq]
    simp only [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    constructor
    · intro hz
      constructor
      · apply mem_center_iff.mpr
        intro x
        apply Subtype.ext
        have he := congrArg Subtype.val (mem_center_iff.mp hz (inclusion le_sup_left x))
        change (x : H) * ((k : H) * j) = ((k : H) * j) * x at he
        have hxj := (hcomm x j).eq
        have hkx : (x : H) * k = (k : H) * x := by
          apply mul_right_cancel (b := (j : H))
          simpa only [mul_assoc, ← hxj] using he
        exact hkx
      · apply mem_center_iff.mpr
        intro y
        apply Subtype.ext
        have he := congrArg Subtype.val (mem_center_iff.mp hz (inclusion le_sup_right y))
        change (y : H) * ((k : H) * j) = ((k : H) * j) * y at he
        have hky := (hcomm k y).eq
        apply mul_left_cancel (a := (k : H))
        simpa only [Subgroup.coe_mul, ← mul_assoc, ← hky] using he
    · rintro ⟨hk, hj⟩
      apply mem_center_iff.mpr
      intro x
      obtain ⟨⟨u, v⟩, rfl⟩ := hf x
      apply Subtype.ext
      change ((u : H) * v) * ((k : H) * j) = ((k : H) * j) * ((u : H) * v)
      have huk : Commute (u : H) k := (show Commute u k from mem_center_iff.mp hk u).map K.subtype
      have hvj : Commute (v : H) j := (show Commute v j from mem_center_iff.mp hj v).map J.subtype
      exact (huk.mul_left (hcomm k v).symm).mul_right ((hcomm u j).mul_left hvj) |>.eq
  let e := (QuotientGroup.quotientKerEquivOfSurjective F hF).symm.trans
    ((QuotientGroup.quotientMulEquivOfEq hker).trans
      (QuotientGroup.quotientKerEquivOfSurjective Q hQ))
  refine ⟨e, fun k j => ?_⟩
  change e (F (k, j)) = Q (k, j)
  change (QuotientGroup.quotientKerEquivOfSurjective Q hQ)
    (QuotientGroup.quotientMulEquivOfEq hker
      ((QuotientGroup.quotientKerEquivOfSurjective F hF).symm (F (k, j)))) = _
  rw [show F (k, j) = QuotientGroup.quotientKerEquivOfSurjective F hF
    (QuotientGroup.mk' F.ker (k, j)) from rfl, MulEquiv.symm_apply_apply]
  rfl

noncomputable def quotientCenterCongr {A B : Type*} [Group A] [Group B]
    (e : A ≃* B) : (A ⧸ center A) ≃* (B ⧸ center B) :=
  QuotientGroup.congr _ _ e (by
    apply le_antisymm
    · rintro _ ⟨a, ha, rfl⟩
      exact (centerCongr e ⟨a, ha⟩).property
    · intro b hb
      exact ⟨e.symm b, (centerCongr e.symm ⟨b, hb⟩).property, e.apply_symm_apply b⟩)

theorem quotientCenterCongr_mk {A B : Type*} [Group A] [Group B] (e : A ≃* B) (a : A) :
    quotientCenterCongr e (QuotientGroup.mk' (center A) a) =
      QuotientGroup.mk' (center B) (e a) := rfl

theorem conjugate_dichotomy (K : Subgroup H)
    (hi : (normalizer (K : Set H)).index = 2)
    {t : H} (ht : t ∉ normalizer (K : Set H)) (s : H) :
    K.conjBy s = K ∨ K.conjBy s = K.conjBy t := by
  by_cases hs : s ∈ normalizer (K : Set H)
  · exact Or.inl (mem_normalizer_iff_map_conj_eq.mp hs)
  · have he : t⁻¹ * s ∈ normalizer (K : Set H) :=
      (mul_mem_iff_of_index_two hi).mpr (by simp [ht, hs])
    have heq : K.conjBy (t⁻¹ * s) = K := mem_normalizer_iff_map_conj_eq.mp he
    have hh := congrArg (fun B : Subgroup H => B.conjBy t) heq
    rw [conjBy_mul, conjBy_inv'] at hh
    exact Or.inr hh

theorem orbit_eq_pair (K T : Subgroup H)
    (hi : (normalizer (K : Set H)).index = 2)
    {t : H} (ht : t ∈ T) (hm : t ∉ normalizer (K : Set H)) :
    componentOrbit K T = K ⊔ K.conjBy t := by
  apply le_antisymm
  · change (⨆ s : T, K.conjBy (s : H)) ≤ K ⊔ K.conjBy t
    refine iSup_le fun s => ?_
    rcases conjugate_dichotomy K hi hm s with he | he
    · rw [he]
      exact le_sup_left
    · rw [he]
      exact le_sup_right
  · exact sup_le (le_componentOrbit K T)
      (le_iSup (fun s : T => K.map (MulAut.conj (s : H)).toMonoidHom) ⟨t, ht⟩)

theorem moving_conjugate_swaps (K : Subgroup H) (hi : (normalizer (K : Set H)).index = 2)
    {t : H} (ht : t ∉ normalizer (K : Set H)) :
    (K.conjBy t).conjBy t = K := by
  rcases conjugate_dichotomy K hi ht (t * t) with he | he
  · rwa [conjBy_mul] at he
  · have hh := congrArg (fun B : Subgroup H => B.conjBy t⁻¹) he
    simp only [conjBy_mul, conjBy_inv] at hh
    exact (ht (mem_normalizer_iff_map_conj_eq.mpr hh)).elim

/-- Every actor preserves or interchanges the two actual component subgroups. -/
theorem pair_permutation (K : Subgroup H)
    (hi : (normalizer (K : Set H)).index = 2)
    {t : H} (ht : t ∉ normalizer (K : Set H)) (u : H) :
    (K.conjBy u = K ∧ (K.conjBy t).conjBy u = K.conjBy t) ∨
      (K.conjBy u = K.conjBy t ∧ (K.conjBy t).conjBy u = K) := by
  have hne : (K.conjBy t).conjBy u ≠ K.conjBy u := by
    intro he
    apply ht
    apply mem_normalizer_iff_map_conj_eq.mpr
    exact map_injective (MulAut.conj u).injective he
  have hd := conjugate_dichotomy K hi ht (u * t)
  rw [conjBy_mul] at hd
  rcases conjugate_dichotomy K hi ht u with hfix | hswap
  · left
    refine ⟨hfix, ?_⟩
    exact hd.resolve_left (fun he => hne (he.trans hfix.symm))
  · right
    refine ⟨hswap, ?_⟩
    exact hd.resolve_right (fun he => hne (he.trans hswap.symm))

variable {S : Type*} [Group S]

theorem component_pair_model (K : Subgroup H) (hK : IsComponent H K)
    {t : H} (ht : t ∉ normalizer (K : Set H))
    (eK : NormalizerAction.componentImage K ≃* S) :
    ∃ e : (↥(K ⊔ K.conjBy t) ⧸ center ↥(K ⊔ K.conjBy t)) ≃* (S × S),
      ∀ (k l : K),
        e (QuotientGroup.mk' (center ↥(K ⊔ K.conjBy t))
          ⟨(k : H) * MulAut.conj t (l : H), mul_mem
            ((show K ≤ K ⊔ K.conjBy t from le_sup_left) k.property)
            ((show K.conjBy t ≤ K ⊔ K.conjBy t from le_sup_right)
              (mem_map_of_mem (MulAut.conj t).toMonoidHom l.property))⟩) =
          (eK (NormalizerAction.componentCentralQuotientEquiv K
              (QuotientGroup.mk' (center K) k)),
           eK (NormalizerAction.componentCentralQuotientEquiv K
              (QuotientGroup.mk' (center K) l))) := by
  have hc : ⁅K, K.conjBy t⁆ = ⊥ := hK.commutator_eq_bot_of_ne (hK.map_conj t)
    (fun he => ht (mem_normalizer_iff_map_conj_eq.mpr he.symm))
  obtain ⟨e, he⟩ := centralProduct_quotient K (K.conjBy t) hc
  let c : K ≃* K.conjBy t := (MulAut.conj t).subgroupMap K
  let ec := quotientCenterCongr c
  let kmodel := (NormalizerAction.componentCentralQuotientEquiv K).trans eK
  refine ⟨e.trans (kmodel.prodCongr (ec.symm.trans kmodel)), fun k l => ?_⟩
  refine (congrArg (kmodel.prodCongr (ec.symm.trans kmodel)) (he k (c l))).trans ?_
  change (kmodel (QuotientGroup.mk' (center K) k),
    kmodel (ec.symm (ec (QuotientGroup.mk' (center K) l)))) = _
  rw [ec.symm_apply_apply]
  rfl

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentReduction.MovingComponent
