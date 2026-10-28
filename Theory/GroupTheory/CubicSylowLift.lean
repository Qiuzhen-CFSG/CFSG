module
public import Theory.GroupTheory.CubicSylowExtension
public import Theory.GroupTheory.PCoreFrattiniTransport

/-!
# Lifting an invariant cubic Sylow overgroup

An automorphism-invariant overgroup of the quotient Sylow lifts through
K/O₂(K) to a T-normalized subgroup of the original K. Adjoining T preserves
its relative index three. A two-group kernel also preserves its S₃
quotient over the intrinsic two-core. All conjugations use the original
normalizer action, without requiring K normal in the ambient group.

The concrete consumer is the middle node in Aschbacher--Smith 15.2.21(3),
printed p.1114, implemented in BinaryLinear.FourMiddleLift and the Chapter15
SmallActionsSource.MiddleParabolic adapter.
-/

public section
open Subgroup
namespace Subgroup.CubicSylowLift
variable {G Q : Type*} [Group G] [Group Q] [Finite G]

/-- Lift a Sylow-invariant subgroup through the literal two-core quotient. -/
theorem exists_lift (T : Sylow 2 G) (K : Subgroup G)
    (hn : (T : Subgroup G) ≤ normalizer (K : Set G))
    (eK : (K ⧸ pCore 2 K) ≃* Q)
    (model : ∀ S : Sylow 2 Q, ∃ J : Subgroup Q,
      (S : Subgroup Q) ≤ J ∧ (S : Subgroup Q).relIndex J = 3 ∧
      Nonempty ((J ⧸ pCore 2 J) ≃* Equiv.Perm (Fin 3)) ∧
      ∀ a : MulAut Q, (S : Subgroup Q).map a.toMonoidHom = S →
        J.map a.toMonoidHom = J) :
    ∃ E : Subgroup G, E ≤ K ∧ (T : Subgroup G) ≤ normalizer (E : Set G) ∧
      (T : Subgroup G).relIndex (E ⊔ (T : Subgroup G)) = 3 ∧
      Nonempty ((E ⧸ pCore 2 E) ≃* Equiv.Perm (Fin 3)) := by
  let : Finite Q := Finite.of_surjective eK eK.surjective
  obtain ⟨P,hP⟩ := NormalSylowQuotientAction.intersection_sylow T K hn
  let q := eK.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 K))
  have hq : Function.Surjective q := eK.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : q.ker = pCore 2 K := by
    ext k
    change eK (QuotientGroup.mk k) = 1 ↔ k ∈ pCore 2 K
    rw [eK.map_eq_one_iff,QuotientGroup.eq_one_iff]
  have hkerP : q.ker ≤ (P : Subgroup K) := hker ▸ pCore_isPGroup.le_sylow_of_normal P
  let Pq := P.mapSurjective hq
  obtain ⟨J,hPJ,hi,⟨eJ⟩,hinv⟩ := model Pq
  let Jpre := J.comap q
  let Jamb := Jpre.map K.subtype
  have hPJpre : (P : Subgroup K) ≤ Jpre := (map_le_iff_le_comap).mp hPJ
  have hnorm : (T : Subgroup G) ≤ normalizer (Jamb : Set G) := by
    intro t ht
    let a := K.normalizerMonoidHom ⟨t,hn ht⟩
    let b := (MulAut.congr eK) ((pCore 2 K).quotientAut a)
    have he (k : K) : b (q k) = q (a k) := by
      dsimp only [b,q,MonoidHom.comp_apply,MulEquiv.coe_toMonoidHom]
      simp only [MulAut.congr_apply, MulEquiv.trans_apply, eK.symm_apply_apply,quotientAut_apply_mk]
    have hehom : b.toMonoidHom.comp q = q.comp a.toMonoidHom :=
      MonoidHom.ext he
    have haP : (P : Subgroup K).map a.toMonoidHom = P := by
      rw [hP]
      ext x
      constructor
      · rintro ⟨y,hy,rfl⟩
        change (a y : K).val ∈ (T : Subgroup G)
        rw [normalizerMonoidHom_apply_apply_coe]
        exact (T : Subgroup G).mul_mem ((T : Subgroup G).mul_mem ht hy)
          ((T : Subgroup G).inv_mem ht)
      · intro hx
        refine ⟨a.symm x,?_,a.apply_symm_apply x⟩
        change (a.symm x : K).val ∈ (T : Subgroup G)
        have he : a.symm = K.normalizerMonoidHom ⟨t⁻¹,(normalizer (K : Set G)).inv_mem (hn ht)⟩ :=
          (map_inv K.normalizerMonoidHom ⟨t,hn ht⟩).symm
        rw [he,normalizerMonoidHom_apply_apply_coe,inv_inv]
        exact (T : Subgroup G).mul_mem
          ((T : Subgroup G).mul_mem ((T : Subgroup G).inv_mem ht) hx) ht
    have hbP : (Pq : Subgroup (Q)).map b.toMonoidHom = Pq := by
      change ((P : Subgroup K).map q).map b.toMonoidHom = (P : Subgroup K).map q
      rw [map_map,hehom,←map_map,haP]
    have hbJ := hinv b hbP
    have haJ : Jpre.map a.toMonoidHom = Jpre := by
      apply le_antisymm
      · rintro k ⟨l,hl,rfl⟩
        change q (a l) ∈ J
        rw [←he]
        exact hbJ ▸ mem_map_of_mem b.toMonoidHom hl
      · intro k hk
        refine ⟨a.symm k,?_,a.apply_symm_apply k⟩
        change q (a.symm k) ∈ J
        have hm : b (q (a.symm k)) ∈ J := by rwa [he,a.apply_symm_apply]
        have hcom : J.comap b.toMonoidHom = J := by
          have hh := congrArg (Subgroup.comap b.toMonoidHom) hbJ
          simpa only [comap_map_eq, (b.toMonoidHom.ker_eq_bot b.injective), sup_bot_eq] using hh.symm
        exact hcom ▸ hm
    apply mem_normalizer_iff_map_conj_eq.mpr
    change (Jpre.map K.subtype).map (MulAut.conj t).toMonoidHom = Jpre.map K.subtype
    have hc : (MulAut.conj t).toMonoidHom.comp K.subtype = K.subtype.comp a.toMonoidHom := by
      apply MonoidHom.ext
      intro k
      exact (normalizerMonoidHom_apply_apply_coe K ⟨t,hn ht⟩ k).symm
    rw [map_map,hc,←map_map,haJ]

  have hkerJ : q.ker ≤ Jpre := hkerP.trans hPJpre
  have hpreIndex : (P : Subgroup K).relIndex Jpre = 3 := by
    have hh := relIndex_map_map q (P : Subgroup K) Jpre
    rw [sup_eq_left.mpr hkerP,sup_eq_left.mpr hkerJ,
      map_comap_eq_self_of_surjective hq] at hh
    exact hh.symm.trans hi
  have hYindex : (T : Subgroup G).relIndex (Jamb ⊔ (T : Subgroup G)) = 3 := by
    rw [relIndex_sup_of_normalizes_left Jamb (T : Subgroup G) hnorm]
    have hh := relIndex_comap (T : Subgroup G) K.subtype Jpre
    change ((T : Subgroup G).subgroupOf K).relIndex Jpre =
      (T : Subgroup G).relIndex Jamb at hh
    rw [←hP] at hh
    exact hh.symm.trans hpreIndex
  let f : Jpre →* J := (q.comp Jpre.subtype).codRestrict J (fun x => x.property)
  have hf : Function.Surjective f := by
    intro j
    obtain ⟨x,hx⟩ := hq j
    exact ⟨⟨x,show q x ∈ J from hx ▸ j.property⟩,Subtype.ext hx⟩
  have hkf : IsPGroup 2 f.ker := by
    have he : f.ker = q.ker.subgroupOf Jpre := by
      ext x
      change f x = 1 ↔ q x = 1
      exact Subtype.ext_iff
    rw [he,hker]
    exact pCore_isPGroup.comap_subtype
  let epre : Jpre ≃* Jamb := Subgroup.equivMapOfInjective Jpre K.subtype K.subtype_injective
  let ecore := QuotientGroup.congr _ _ epre (pCore_map_iso 2 epre)
  exact ⟨Jamb,map_subtype_le _,hnorm,hYindex,
    ⟨ecore.symm.trans ((f.pCoreQuotientEquiv hf hkf).trans eJ)⟩⟩
end Subgroup.CubicSylowLift
