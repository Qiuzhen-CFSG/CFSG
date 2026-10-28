module
public import CFSG.Quasithin.ChapterC.Section05.ConjugateSource.AlternatingPair

/-!
# Alternating-five conjugate factorizations

The literal core action is faithful, so the fixed-plane calculation forces
S = Uˣ Q and its symmetric factorization. The preceding direct product
Q = U × D has invariant factors; uniqueness of those factors shows that D
centralizes Uˣ. This proves C.5.6(1) and the spanning assertions of (2)
for the original A₅ block, including when R swaps two blocks.

Source: Aschbacher–Smith, C.5.6, printed pp.156–157.
-/

public section
open Subgroup BinaryPermutation
namespace CFSG.Quasithin.ChapterC.Section05.ConjugateSource
variable {G : Type*} [Group G] [Finite G] {R K L : Subgroup G}
private theorem core_faithful (p : FivePerm)
    (hp : ∀ v : core (Fin 5), coreRepresentation (Fin 5) p v = v) : p = 1 := by
  have hn : naturalMulAction (Fin 5) p = 1 := by
    apply MulEquiv.ext
    intro v
    apply Multiplicative.toAdd.injective
    change naturalRepresentation (Fin 5) p v.toAdd = v.toAdd
    let e := coreEquivNatural (Fin 5) (by decide)
    obtain ⟨w, hw⟩ := e.surjective v.toAdd
    rw [← hw, ← coreEquivNatural_equivariant, hp]
  exact (naturalMulAction_injective_of_odd (Fin 5) (by decide))
    (hn.trans (map_one (naturalMulAction (Fin 5))).symm)

omit [Finite G] in
theorem AlternatingPairSetup.action_kernel (h : AlternatingPairSetup R K L) :
    h.action.ker = (centralizer (sourceModule K : Set G)).subgroupOf (K ⊔ ChapterB.baumann R) := by
  ext s
  change h.action s = 1 ↔ (s : G) ∈ centralizer (sourceModule K : Set G)
  constructor
  · intro hs u hu
    have he := h.equivariant s ⟨u, hu⟩
    rw [hs, map_one, Module.End.one_apply] at he
    change (h.coordinates.symm (h.coordinates ⟨u, hu⟩) : G) = (s : G) * u * (s : G)⁻¹ at he
    rw [h.coordinates.symm_apply_apply] at he
    exact (mul_inv_eq_iff_eq_mul.mp he.symm).symm
  · intro hs
    apply core_faithful
    intro v
    obtain ⟨u, hu⟩ := h.coordinates.surjective (Multiplicative.ofAdd v)
    have he := h.equivariant s u
    rw [← hs u u.property, mul_inv_cancel_right] at he
    have hh : h.coordinates.symm (Multiplicative.ofAdd
        (coreRepresentation (Fin 5) (h.action s) (h.coordinates u).toAdd)) = u := Subtype.ext he
    rw [hu] at hh
    apply Multiplicative.ofAdd.injective
    rw [← hu]
    exact (h.coordinates.apply_symm_apply _).symm.trans (congrArg h.coordinates hh)

omit [Finite G] in
theorem AlternatingPairSetup.baumann_action_index (h : AlternatingPairSetup R K L) :
    (centralizer (sourceModule K : Set G)).relIndex (ChapterB.baumann R) = 4 := by
  have hi := relIndex_ker ((ChapterB.baumann R).subgroupOf (K ⊔ ChapterB.baumann R)) h.action
  rw [h.action_kernel, relIndex_subgroupOf le_sup_right, h.baumann_image] at hi
  exact hi.trans (ChapterB.Offenders.Odd.card_disjointTranspositions (Or.inl rfl) (by decide))
end CFSG.Quasithin.ChapterC.Section05.ConjugateSource
namespace CFSG.Quasithin.ChapterC.Section05.ConjugateSource
variable {G : Type*} [Group G] [Finite G] {R K L : Subgroup G}
private theorem span_of_index_eq (S V Q : Subgroup G)
    (hVS : V ≤ S) (hQS : Q ≤ S) (hVQ : V ≤ normalizer (Q : Set G))
    (hi : Q.relIndex V = Q.relIndex S) : S = V ⊔ Q := by
  let : (Q.subgroupOf (V ⊔ Q)).Normal := normal_subgroupOf_sup_of_le_normalizer hVQ
  have hs : Q.relIndex (V ⊔ Q) = Q.relIndex V := by
    have hj := relIndex_sup_right (V.subgroupOf (V ⊔ Q)) (Q.subgroupOf (V ⊔ Q))
    rw [← subgroupOf_sup le_sup_left le_sup_right,
      relIndex_subgroupOf le_rfl, relIndex_subgroupOf le_sup_left] at hj
    exact hj
  have hm := relIndex_mul_relIndex Q (V ⊔ Q) S le_sup_right (sup_le hVS hQS)
  rw [hs, hi] at hm
  have he : (V ⊔ Q).relIndex S = 1 := by
    have hp : 0 < Q.relIndex S := Nat.pos_of_ne_zero index_ne_zero_of_finite
    nlinarith
  exact le_antisymm (relIndex_eq_one.mp he) (sup_le hVS hQS)

omit [Finite G] in
private theorem centralizer_normalized (U S : Subgroup G)
    (hn : S ≤ normalizer (U : Set G)) :
    S ≤ normalizer (S ⊓ centralizer (U : Set G) : Set G) :=
  (le_inf S.le_normalizer (hn.trans ((normal_subgroupOf_iff_le_normalizer
    (Subgroup.centralizer_le_normalizer (U : Set G))).mp inferInstance))).trans
    inf_normalizer_le_normalizer_inf

theorem AlternatingPairSetup.first_factorization (h : AlternatingPairSetup R K L)
    (x : G) (hx : x ∈ normalizer (R : Set G))
    (hnc : ¬ (sourceModule K).map (MulAut.conj x⁻¹).toMonoidHom ≤ centralizer (sourceModule K : Set G)) :
    ChapterB.baumann R = (sourceModule K).map (MulAut.conj x⁻¹).toMonoidHom ⊔
      (K ⊔ ChapterB.baumann R).pCoreIn 2 := by
  let S := ChapterB.baumann R
  let U := sourceModule K
  let V := U.map (MulAut.conj x⁻¹).toMonoidHom
  have hS : S.map (MulAut.conj x⁻¹).toMonoidHom = S :=
    mem_normalizer_iff_map_conj_eq.mp
      (Stellmacher.normalizer_le_normalizer_baumann R ((normalizer (R : Set G)).inv_mem hx))
  have hVS : V ≤ S := (map_mono h.module_le).trans_eq hS
  have hnU : S ≤ normalizer (U : Set G) :=
    (baumann_le_transvectionRadical R).trans (h.transvection_normalizes x hx).1
  rw [h.core]
  apply span_of_index_eq S V (S ⊓ centralizer (U : Set G)) hVS inf_le_left
    (hVS.trans (centralizer_normalized U S hnU))
  rw [inf_relIndex_left]
  have he : (S ⊓ centralizer (U : Set G)).subgroupOf V = (centralizer (U : Set G)).subgroupOf V := by
    ext v
    exact and_iff_right (hVS v.property)
  change ((S ⊓ centralizer (U : Set G)).subgroupOf V).index = _
  rw [he]
  exact (h.conjugate_action_index x hx hnc).trans h.baumann_action_index.symm
end CFSG.Quasithin.ChapterC.Section05.ConjugateSource


namespace CFSG.Quasithin.ChapterC.Section05.ConjugateSource
variable {G : Type*} [Group G] [Finite G] {R K L : Subgroup G}
omit [Finite G] in
private theorem map_centralizer (U : Subgroup G) (e : G ≃* G) :
    (centralizer (U : Set G)).map e.toMonoidHom = centralizer (U.map e.toMonoidHom : Set G) := by
  apply le_antisymm
  · exact map_centralizer_le_centralizer_image _ _
  · intro g hg
    refine ⟨e.symm g, ?_, e.apply_symm_apply g⟩
    intro u hu
    apply e.injective
    simpa only [map_mul, e.apply_symm_apply] using hg (e u) (mem_map_of_mem _ hu)

theorem AlternatingPairSetup.second_factorization (h : AlternatingPairSetup R K L)
    (x : G) (hx : x ∈ normalizer (R : Set G))
    (hnc : ¬ (sourceModule K).map (MulAut.conj x⁻¹).toMonoidHom ≤ centralizer (sourceModule K : Set G)) :
    ChapterB.baumann R = sourceModule K ⊔
      (ChapterB.baumann R ⊓ centralizer ((sourceModule K).map (MulAut.conj x⁻¹).toMonoidHom : Set G)) := by
  let S := ChapterB.baumann R
  let U := sourceModule K
  let V := U.map (MulAut.conj x⁻¹).toMonoidHom
  have hS : S.map (MulAut.conj x⁻¹).toMonoidHom = S :=
    mem_normalizer_iff_map_conj_eq.mp
      (Stellmacher.normalizer_le_normalizer_baumann R ((normalizer (R : Set G)).inv_mem hx))
  have hnV : S ≤ normalizer (V : Set G) :=
    (baumann_le_transvectionRadical R).trans (h.transvection_normalizes x hx).2.1
  have hcV : (centralizer (V : Set G)).relIndex S = 4 := by
    have hi := relIndex_map_map_of_injective (f := (MulAut.conj x⁻¹).toMonoidHom)
      (centralizer (U : Set G)) S (MulAut.conj x⁻¹).injective
    rw [map_centralizer, hS] at hi
    exact hi.trans h.baumann_action_index
  apply span_of_index_eq S U _ h.module_le inf_le_left
    (h.module_le.trans (centralizer_normalized V S hnV))
  rw [inf_relIndex_left]
  have he : (S ⊓ centralizer (V : Set G)).subgroupOf U = (centralizer (V : Set G)).subgroupOf U := by
    ext u
    exact and_iff_right (h.module_le u.property)
  change ((S ⊓ centralizer (V : Set G)).subgroupOf U).index = _
  rw [he]
  exact (h.module_conjugate_index x hx hnc).trans hcV.symm

theorem AlternatingPairSetup.centralizer_centralizes_conjugate
    (h : AlternatingPairSetup R K L)
    (x : G) (hx : x ∈ normalizer (R : Set G))
    (hnc : ¬ (sourceModule K).map (MulAut.conj x⁻¹).toMonoidHom ≤ centralizer (sourceModule K : Set G)) :
    ChapterB.baumann R ⊓ centralizer (K : Set G) ≤
      centralizer ((sourceModule K).map (MulAut.conj x⁻¹).toMonoidHom : Set G) := by
  let S := ChapterB.baumann R
  let U := sourceModule K
  let V := U.map (MulAut.conj x⁻¹).toMonoidHom
  let D := S ⊓ centralizer (K : Set G)
  have hS : S.map (MulAut.conj x⁻¹).toMonoidHom = S :=
    mem_normalizer_iff_map_conj_eq.mp
      (Stellmacher.normalizer_le_normalizer_baumann R ((normalizer (R : Set G)).inv_mem hx))
  have hVS : V ≤ S := (map_mono h.module_le).trans_eq hS
  have hnU : S ≤ normalizer (U : Set G) :=
    (baumann_le_transvectionRadical R).trans (h.transvection_normalizes x hx).1
  have hnD : S ≤ normalizer (D : Set G) := centralizer_normalized K S h.normalizes
  have hdisj : Disjoint U D := alternatingModule_disjoint_of_commuting K D h.block inf_le_right
  have hnC : U ≤ normalizer (S ⊓ centralizer (V : Set G) : Set G) :=
    h.module_le.trans (centralizer_normalized V S
      ((baumann_le_transvectionRadical R).trans (h.transvection_normalizes x hx).2.1))
  intro d hd v hv
  have hdspan : d ∈ U ⊔ (S ⊓ centralizer (V : Set G)) := h.second_factorization x hx hnc ▸ hd.1
  obtain ⟨u, hu, c, hc, heq⟩ :=
    (show ∃ u ∈ U, ∃ c ∈ S ⊓ centralizer (V : Set G), u * c = d from by
      change d ∈ ((U ⊔ (S ⊓ centralizer (V : Set G)) : Subgroup G) : Set G) at hdspan
      rw [coe_mul_of_left_le_normalizer_right U _ hnC] at hdspan
      exact hdspan)
  have hfix : MulAut.conj v (u⁻¹ * d) = u⁻¹ * d := by
    have hc' : u⁻¹ * d = c := by rw [← heq]; simp
    rw [hc']
    change v * c * v⁻¹ = c
    rw [hc.2 v hv, mul_inv_cancel_right]
  have hh := fixed_factors_of_disjoint (MulAut.conj v).toMonoidHom U D hdisj
    (fun a ha => (mem_normalizer_iff.mp (hnU (hVS hv)) a).mp ha)
    (fun a ha => (mem_normalizer_iff.mp (hnD (hVS hv)) a).mp ha)
    (U.inv_mem hu) hd hfix
  exact mul_inv_eq_iff_eq_mul.mp hh.2
end CFSG.Quasithin.ChapterC.Section05.ConjugateSource

namespace CFSG.Quasithin.ChapterC.Section05.ConjugateSource
variable {G : Type*} [Group G] [Finite G] {R K L : Subgroup G}

/-- The noncommuting conjugate induces the full marked pair-swap action. -/
theorem AlternatingPairSetup.conjugate_action_image (h : AlternatingPairSetup R K L)
    (x : G) (hx : x ∈ normalizer (R : Set G))
    (hnc : ¬ (sourceModule K).map (MulAut.conj x⁻¹).toMonoidHom ≤ centralizer (sourceModule K : Set G)) :
    (((sourceModule K).map (MulAut.conj x⁻¹).toMonoidHom).subgroupOf
      (K ⊔ ChapterB.baumann R)).map h.action = ChapterB.Offenders.D 5 := by
  let S := ChapterB.baumann R
  let V := (sourceModule K).map (MulAut.conj x⁻¹).toMonoidHom
  let N := K ⊔ S
  have hS : S.map (MulAut.conj x⁻¹).toMonoidHom = S :=
    mem_normalizer_iff_map_conj_eq.mp
      (Stellmacher.normalizer_le_normalizer_baumann R ((normalizer (R : Set G)).inv_mem hx))
  have hVS : V ≤ S := (map_mono h.module_le).trans_eq hS
  have hVN : V ≤ N := hVS.trans le_sup_right
  have hc := relIndex_ker (V.subgroupOf N) h.action
  rw [h.action_kernel, relIndex_subgroupOf hVN, h.conjugate_action_index x hx hnc] at hc
  apply eq_of_le_of_card_ge
  · rw [← h.baumann_image]
    exact map_mono (subgroupOf_mono N hVS)
  · rw [← hc]
    exact (ChapterB.Offenders.Odd.card_disjointTranspositions (Or.inl rfl) (by decide)).le

omit [Finite G] in
/-- The original core transports to the relative centralizer of Uˣ. -/
theorem AlternatingPairSetup.conjugate_core (h : AlternatingPairSetup R K L)
    (x : G) (hx : x ∈ normalizer (R : Set G)) :
    ((K ⊔ ChapterB.baumann R).pCoreIn 2).map (MulAut.conj x⁻¹).toMonoidHom =
      ChapterB.baumann R ⊓
        centralizer ((sourceModule K).map (MulAut.conj x⁻¹).toMonoidHom : Set G) := by
  have hS : (ChapterB.baumann R).map (MulAut.conj x⁻¹).toMonoidHom = ChapterB.baumann R :=
    mem_normalizer_iff_map_conj_eq.mp
      (Stellmacher.normalizer_le_normalizer_baumann R ((normalizer (R : Set G)).inv_mem hx))
  rw [h.core, map_inf _ _ _ (MulAut.conj x⁻¹).injective, hS, map_centralizer]

/-- The two literal conjugate cores generate S, as required in C.5.6(2). -/
theorem AlternatingPairSetup.core_conjugate_span (h : AlternatingPairSetup R K L)
    (x : G) (hx : x ∈ normalizer (R : Set G))
    (hnc : ¬ (sourceModule K).map (MulAut.conj x⁻¹).toMonoidHom ≤ centralizer (sourceModule K : Set G)) :
    ChapterB.baumann R = (K ⊔ ChapterB.baumann R).pCoreIn 2 ⊔
      ((K ⊔ ChapterB.baumann R).pCoreIn 2).map (MulAut.conj x⁻¹).toMonoidHom := by
  have hUQ : sourceModule K ≤ (K ⊔ ChapterB.baumann R).pCoreIn 2 :=
    h.product ▸ le_sup_left
  apply le_antisymm
  · exact (h.first_factorization x hx hnc).le.trans
      (sup_le ((map_mono (f := (MulAut.conj x⁻¹).toMonoidHom) hUQ).trans le_sup_right) le_sup_left)
  · apply sup_le
    · rw [h.core]
      exact inf_le_left
    · rw [h.conjugate_core x hx]
      exact inf_le_left
end CFSG.Quasithin.ChapterC.Section05.ConjugateSource
