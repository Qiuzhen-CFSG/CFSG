module
public import CFSG.Quasithin.ChapterC.Section05.CounterexampleCharacteristic.ReducedMarking.Core
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents
public import CFSG.Quasithin.Chapter1.Section01Inheritance
public import Theory.GroupTheory.CComponent.PrimeCoreDichotomy
/-!
# The actual noncubic local-family input in C.5.13

The block is normal in KT, and its noncubic quotient is quasisimple. Prime-core
lifting therefore makes it a genuine C-component of KT. Its nontrivial core
and original Sylow give local-family membership. The auxiliary normalizer
inherits characteristic two and the same Sylow subgroup.
Source: Aschbacher–Smith C.5.13, printed p.162, applying 1.2.3–4.
-/
public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterC.Section05.NormalizerControl
variable {G : Type*} [Group G] [Finite G]
/-- The nonsolvable chi-zero alternatives have quasisimple two-core quotient.
This local order exclusion avoids importing later E.6/Chapter 3 interfaces. -/
theorem noncubic_quotient_quasisimple {D : Type*} [Group D]
    (h : IsChiZeroBlock D) (h3 : ¬ IsAlternatingBlock D 3) :
    IsQuasisimple (D ⧸ pCore 2 D) := by
  rcases h with ⟨n,hn,hs,F,_,_,hc,_,hm⟩ | ha | ha
  · rcases hs.quotient with hq | hq
    · exact hq
    · obtain ⟨e⟩ := hm.quotient_iso
      have hle := Nat.card_le_card_of_injective
        (Matrix.SpecialLinearGroup.upperUnipotentHom F)
        (Matrix.SpecialLinearGroup.upperUnipotentHom_injective F)
      change Nat.card F ≤ Nat.card (Matrix.SpecialLinearGroup (Fin 2) F) at hle
      rw [← Nat.card_congr e.toEquiv,hq,hc] at hle
      have hfour : 4 ≤ 2^n := Nat.pow_le_pow_right (by decide : 1 ≤ 2) hn
      omega
  · exact (h3 ha).elim
  · rcases ha.2.1.quotient with hq | hc
    · exact hq
    · obtain ⟨e⟩ := ha.2.2.quotient_iso
      have he : Nat.card (D ⧸ pCore 2 D) = 60 := by
        rw [Nat.card_congr e.toEquiv,Nat.card_eq_fintype_card,card_alternatingGroup]
        decide
      omega
/-- The actual normalized noncubic block is a member of the local family. -/
theorem noncubic_mem_local_family (K T : Subgroup G)
    (hK : IsChiZeroBlock K) (h3 : ¬ IsAlternatingBlock K 3)
    (hTK : T ≤ normalizer (K : Set G))
    (P : Sylow 2 (K ⊔ T : Subgroup G))
    (hP : (P : Subgroup (K ⊔ T : Subgroup G)).map (K ⊔ T).subtype = T) :
    K ∈ Chapter1.L G T := by
  let A := K ⊔ T
  have hshort := hK.chi.short
  let e := (subgroupOfEquivOfLe (show K ≤ A from le_sup_left)).symm
  let : (K.subgroupOf A).Normal := (normal_subgroupOf_iff_le_normalizer le_sup_left).mpr
    (sup_le K.le_normalizer hTK)
  let : IsQuasisimple (K ⧸ pCore 2 K) := noncubic_quotient_quasisimple hK h3
  let : IsQuasisimple ((K.subgroupOf A) ⧸ pCore 2 (K.subgroupOf A)) :=
    IsQuasisimple.of_mulEquiv (QuotientGroup.congr _ _ e (pCore_map_iso 2 e))
  have hcomp : (K.subgroupOf A).IsCComponent :=
    isCComponent_of_isPPerfect_of_quasisimple_core_quotient
      (inferInstance : (K.subgroupOf A).Normal).isSubnormal
      (hshort.twoPerfect.of_surjective e.toMonoidHom e.surjective)
  have hcore : A.pCoreIn 2 ≠ ⊥ := by
    intro he
    have hk : K.pCoreIn 2 ≤ A.pCoreIn 2 := pCoreIn_mono_of_normalizes le_sup_left
      (sup_le K.le_normalizer hTK)
    have hz : (pCore 2 K).map K.subtype = ⊥ := bot_unique (he ▸ hk)
    exact hshort.core_ne_bot ((map_injective K.subtype_injective)
      (hz.trans (Subgroup.map_bot K.subtype).symm))
  exact Chapter1.mem_L_of_cComponent hcore ⟨P,hP⟩ le_sup_left hcomp
/-- C.5.10–11 put the literal noncubic block in L(X₁,T₁), and supply
both the actual auxiliary Sylow subgroup and characteristic two. -/
theorem noncubic_auxiliary_local_family (K T X : Subgroup G)
    (hK : IsChiZeroBlock K) (h3 : ¬ IsAlternatingBlock K 3)
    (hTK : T ≤ normalizer (K : Set G)) (hAX : K ⊔ T ≤ X)
    (hX : X ∈ Chapter1.He G)
    (P : Sylow 2 X) (hP : (P : Subgroup X).map X.subtype = T) :
    let N := X ⊓ normalizer ((K ⊔ T).pCoreIn 2 : Set G)
    K ∈ Chapter1.LIn N T ∧ N ∈ Chapter1.He G ∧
      ∃ S : Sylow 2 N, (S : Subgroup N).map N.subtype = T := by
  let A := K ⊔ T
  let N := X ⊓ normalizer (A.pCoreIn 2 : Set G)
  have hAN : A ≤ N := le_inf hAX (A.le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image A (pCore 2 A)))
  obtain ⟨Q,hQ⟩ := Chapter1.IsSylowIn.restrict (show Chapter1.IsSylowIn 2 T X from ⟨P,hP⟩)
    (show T ≤ A from le_sup_right) hAX
  exact ⟨⟨le_sup_left.trans hAN,noncubic_mem_local_family K T hK h3 hTK Q hQ⟩,
    Chapter1.normalizer_mem_He_of_isPGroup hX (isPGroup_pCoreIn 2 A)
      ((pCoreIn_le 2 A).trans hAX),
    Chapter1.IsSylowIn.restrict ⟨P,hP⟩ (le_sup_right.trans hAN) inf_le_left⟩
end CFSG.Quasithin.ChapterC.Section05.NormalizerControl
