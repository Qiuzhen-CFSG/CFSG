module
public import Theory.GroupTheory.PCoreQuotientAction
public import Theory.GroupTheory.NormalQuotientOuterAction

/-!
# A noninner original actor escapes the component image

For a normal subgroup C, an actor whose image modulo the ambient p-core
belongs to the image of C acts internally on C/O_p(C). The ambient p-core
acts trivially there, so this follows from the original subgroup and the
quotient-action kernel. No component or centerlessness hypothesis is needed.

The embedding adapter retains the actual K ≤ I and the exact conjugation
on K/O₂(K). Thus the original noninner Sylow action forces the component
image to be a proper subgroup of I/O₂(I), as used in 14.7.51.
Source: Aschbacher–Smith, printed p.1065, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.EightSource.GraphMarking
variable {G : Type*} [Group G]

/-- Membership in the normal subgroup image modulo the ambient core forces
inner action on its intrinsic core quotient. -/
theorem action_inner_of_mem_core_image (p : ℕ) (C : Subgroup G) [C.Normal]
    (t : G)
    (ht : QuotientGroup.mk' (pCore p G) t ∈ C.map (QuotientGroup.mk' (pCore p G))) :
    normalQuotientAction C (pCore p C) t ∈ MulAut.innerSubgroup (C ⧸ pCore p C) := by
  have hm : t ∈ C ⊔ pCore p G := by
    change t ∈ (C.map (QuotientGroup.mk' (pCore p G))).comap
      (QuotientGroup.mk' (pCore p G)) at ht
    rwa [comap_map_eq,QuotientGroup.ker_mk'] at ht
  have hk : pCore p G ≤ (normalQuotientAction C (pCore p C)).ker := by
    intro x hx
    have hfix := pCore_le_quotientAction_ker p C hx
    apply MulEquiv.ext
    intro y
    obtain ⟨c,rfl⟩ := QuotientGroup.mk'_surjective (pCore p C) y
    rw [normalQuotientAction_apply_mk]
    have he := DFunLike.congr_fun (show
      ((pCore p C).quotientAut.comp (MulAut.conjNormal : G →* MulAut C)) x = 1
      from hfix) (QuotientGroup.mk' (pCore p C) c)
    rw [MonoidHom.comp_apply,quotientAut_apply_mk] at he
    exact he
  change t ∈ (MulAut.innerSubgroup (C ⧸ pCore p C)).comap
    (normalQuotientAction C (pCore p C))
  rw [normalQuotientAction_comap_inner]
  exact (sup_le_sup_left hk C) hm

private theorem embedded_action_compatible (p : ℕ) (I : Subgroup G) (C : Subgroup I)
    [C.Normal] (t : I)
    (ht : (t : G) ∈ normalizer (C.map I.subtype : Set G)) :
    let e := C.equivMapOfInjective I.subtype I.subtype_injective
    let Q := QuotientGroup.congr _ _ e (pCore_map_iso p e)
    MulAut.congr Q (normalQuotientAction C (pCore p C) t) =
      (pCore p (C.map I.subtype)).quotientAut
        ((C.map I.subtype).normalizerMonoidHom ⟨t,ht⟩) := by
  let K := C.map I.subtype
  let e := C.equivMapOfInjective I.subtype I.subtype_injective
  let Q := QuotientGroup.congr _ _ e (pCore_map_iso p e)
  have he (c : C) : Q (QuotientGroup.mk' (pCore p C) c) =
      QuotientGroup.mk' (pCore p K) (e c) := QuotientGroup.congr_mk' _ _ _ _ c
  apply MulEquiv.ext
  intro x
  obtain ⟨c,rfl⟩ := Q.surjective.comp (QuotientGroup.mk'_surjective (pCore p C)) x
  change Q (normalQuotientAction C (pCore p C) t
    (Q.symm (Q (QuotientGroup.mk' (pCore p C) c)))) = _
  simp only [Function.comp_apply]
  rw [Q.symm_apply_apply,normalQuotientAction_apply_mk,he,he,quotientAut_apply_mk]
  rfl

/-- The same implication on the canonical image C.map I.subtype, with the
literal original ambient normalizer action. -/
theorem embedded_action_inner_of_mem_core_image
    (p : ℕ) (I : Subgroup G) (C : Subgroup I) [C.Normal] (t : I)
    (hn : (t : G) ∈ normalizer (C.map I.subtype : Set G))
    (ht : QuotientGroup.mk' (pCore p I) t ∈ C.map (QuotientGroup.mk' (pCore p I))) :
    (pCore p (C.map I.subtype)).quotientAut
      ((C.map I.subtype).normalizerMonoidHom ⟨t,hn⟩) ∈
        MulAut.innerSubgroup (C.map I.subtype ⧸ pCore p (C.map I.subtype)) := by
  let e := C.equivMapOfInjective I.subtype I.subtype_injective
  let Q := QuotientGroup.congr _ _ e (pCore_map_iso p e)
  rw [←embedded_action_compatible p I C t hn,←MulAut.map_innerSubgroup_congr Q]
  exact mem_map_of_mem _ (action_inner_of_mem_core_image p C t ht)
/-- A noninner actor lies outside the component image modulo the ambient core. -/
theorem core_image_not_mem_of_noninner (p : ℕ) (C : Subgroup G) [C.Normal]
    (t : G)
    (hout : normalQuotientAction C (pCore p C) t ∉
      MulAut.innerSubgroup (C ⧸ pCore p C)) :
    QuotientGroup.mk' (pCore p G) t ∉ C.map (QuotientGroup.mk' (pCore p G)) :=
  fun ht => hout (action_inner_of_mem_core_image p C t ht)

/-- A noninner original ambient actor has image outside the actual component
in the original local core quotient. -/
theorem ambient_core_image_not_mem_of_noninner
    (I K : Subgroup G) (hKI : K ≤ I) (hKn : (K.subgroupOf I).Normal)
    (t : I) (hn : (t : G) ∈ normalizer (K : Set G))
    (hout : (pCore 2 K).quotientAut (K.normalizerMonoidHom ⟨t,hn⟩) ∉
      MulAut.innerSubgroup (K ⧸ pCore 2 K)) :
    QuotientGroup.mk' (pCore 2 I) t ∉
      (K.subgroupOf I).map (QuotientGroup.mk' (pCore 2 I)) := by
  let := hKn
  intro ht
  have hn' : (t : G) ∈ normalizer ((K.subgroupOf I).map I.subtype : Set G) := by
    rwa [map_subgroupOf_eq_of_le hKI]
  have hi := embedded_action_inner_of_mem_core_image 2 I (K.subgroupOf I) t hn' ht
  have transfer (A B : Subgroup G) (he : A = B)
      (hA : (t : G) ∈ normalizer (A : Set G))
      (hB : (t : G) ∈ normalizer (B : Set G)) :
      (pCore 2 A).quotientAut (A.normalizerMonoidHom ⟨t,hA⟩) ∈
        MulAut.innerSubgroup (A ⧸ pCore 2 A) →
      (pCore 2 B).quotientAut (B.normalizerMonoidHom ⟨t,hB⟩) ∈
        MulAut.innerSubgroup (B ⧸ pCore 2 B) := by
    subst B
    exact id
  exact hout (transfer _ K (map_subgroupOf_eq_of_le hKI) hn' hn hi)

/-- The exact noninner premise on the original T-action forces the actual
component image to be proper in I/O₂(I). The actor subgroup can be arbitrary. -/
theorem ambient_core_image_ne_top_of_noninner
    {T : Subgroup G} (I K : Subgroup G) (hKI : K ≤ I)
    (hKn : (K.subgroupOf I).Normal)
    (hn : T ≤ normalizer (K : Set G)) (hTI : T ≤ I)
    (hout : ¬ ∀ (t : G) (ht : t ∈ T),
      (pCore 2 K).quotientAut (K.normalizerMonoidHom ⟨t,hn ht⟩) ∈
        MulAut.innerSubgroup (K ⧸ pCore 2 K)) :
    (K.subgroupOf I).map (QuotientGroup.mk' (pCore 2 I)) ≠ ⊤ := by
  intro htop
  apply hout
  intro t ht
  by_contra hi
  apply ambient_core_image_not_mem_of_noninner I K hKI hKn ⟨t,hTI ht⟩ (hn ht) hi
  rw [htop]
  trivial

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.EightSource.GraphMarking
