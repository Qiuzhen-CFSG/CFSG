module
public import Theory.GroupTheory.NormalSylowQuotientAction.MarkedLift
public import Theory.GroupTheory.SylowSubnormalIntersection

/-!
# Marked quotient lifts for a component stabilizer

Only the stabilizer of a component in the ambient Sylow is required to
preserve a model subgroup. Its invariant lift retains the literal quotient
map and conjugation action. The same stabilizer preserves the image of the
Sylow intersection, even when the full Sylow moves the component.

Source application: Aschbacher--Smith 14.6.20, printed p.1037.
-/

public section
open Subgroup
namespace Subgroup.NormalSylowQuotientAction
variable {G B : Type*} [Group G] [Group B]

/-- Invariance under the original Sylow action normalizes the actual lift. -/
theorem quotient_lift_normalized_of_subgroup_marked_invariant (p : ℕ)
    (A : Subgroup G) (K : Subgroup G)
    (hn : A ≤ normalizer (K : Set G))
    (eK : (K ⧸ pCore p K) ≃* B) (J : Subgroup B)
    (hinv : ∀ s : A, J.map (markedCoreAction p K eK ⟨s,hn s.property⟩).toMonoidHom = J) :
    A ≤ normalizer
      ((J.comap (eK.toMonoidHom.comp (QuotientGroup.mk' (pCore p K)))).map K.subtype : Set G) := by
  let q := eK.toMonoidHom.comp (QuotientGroup.mk' (pCore p K))
  let Jpre := J.comap q
  intro t ht
  let a := K.normalizerMonoidHom ⟨t,hn ht⟩
  let b := markedCoreAction p K eK ⟨t,hn ht⟩
  have he (k : K) : b (q k) = q (a k) := markedCoreAction_mk p K eK _ k
  have hbJ : J.map b.toMonoidHom = J := hinv ⟨t,ht⟩
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


/-- Every element of the Sylow component stabilizer preserves the same quotient Sylow. -/
theorem markedCoreAction_preserves_component_sylow (p : ℕ) (T : Sylow p G) (K : Subgroup G)
    (eK : (K ⧸ pCore p K) ≃* B)
    (P : Sylow p K) (hP : (P : Subgroup K) = (T : Subgroup G).subgroupOf K)
    (s : ((T : Subgroup G) ⊓ normalizer (K : Set G) : Subgroup G)) :
    ((P : Subgroup K).map (eK.toMonoidHom.comp (QuotientGroup.mk' (pCore p K)))).map
      (markedCoreAction p K eK ⟨s,s.property.2⟩).toMonoidHom =
      (P : Subgroup K).map (eK.toMonoidHom.comp (QuotientGroup.mk' (pCore p K))) := by
  let q := eK.toMonoidHom.comp (QuotientGroup.mk' (pCore p K))
  let a := K.normalizerMonoidHom ⟨s,s.property.2⟩
  have he : (markedCoreAction p K eK ⟨s,s.property.2⟩).toMonoidHom.comp q =
      q.comp a.toMonoidHom := MonoidHom.ext (markedCoreAction_mk p K eK _)
  have ha : (P : Subgroup K).map a.toMonoidHom = P := by
    rw [hP]
    ext k
    constructor
    · rintro ⟨l,hl,rfl⟩
      change (a l : G) ∈ (T : Subgroup G)
      rw [normalizerMonoidHom_apply_apply_coe]
      exact T.mul_mem (T.mul_mem s.property.1 hl) (T.inv_mem s.property.1)
    · intro hk
      refine ⟨a.symm k,?_,a.apply_symm_apply k⟩
      change (a.symm k : G) ∈ (T : Subgroup G)
      have hi : a.symm = K.normalizerMonoidHom ⟨(s : G)⁻¹,inv_mem s.property.2⟩ := by
        change (K.normalizerMonoidHom ⟨s,s.property.2⟩)⁻¹ =
          K.normalizerMonoidHom (⟨s,s.property.2⟩ : normalizer (K : Set G))⁻¹
        rw [map_inv]
      rw [hi,normalizerMonoidHom_apply_apply_coe,inv_inv]
      exact T.mul_mem (T.mul_mem (T.inv_mem s.property.1) hk) s.property.1
  change ((P : Subgroup K).map q).map _ = (P : Subgroup K).map q
  rw [map_map,he,←map_map,ha]
end Subgroup.NormalSylowQuotientAction
