module

public import CFSG.Quasithin.ChapterF.Section06.Elementary.Rigidity.Local
public import Theory.GroupTheory.SylowNormalizerCommutingFamily
public import Mathlib.GroupTheory.Complement
public import Mathlib.GroupTheory.IndexNormal
/-!
# Invariant-subgroup rigidity in a Goldschmidt amalgam

The image of a Sylow three-subgroup in the local S₃ quotient is normal.
Surjectivity on Sylow normalizers therefore gives an element t of the common
Sylow two-subgroup outside the local two-core which normalizes the chosen
three-subgroup. The two cosets of that core give T = Q⟨t⟩ and t² ∈ Q.

For the subgroup S in F.6.12, the join S ⊔ Sᵗ stays inside Q. Its two
factors are preserved by Q, the chosen three-subgroup and the opposite
residual; t interchanges them. Thus both local generators normalize the
join, and the common-normal-core theorem forces S = 1. Characteristic
subgroups are invariant under the actual induced automorphisms of Q.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*,
Lemma F.6.12(1)–(2), printed p.307 (1 March 2004 manuscript).
-/

open Subgroup
open scoped Pointwise
namespace CFSG.Quasithin.ChapterF
variable {G : Type*} [Group G] [Finite G] {G₁ G₂ : Subgroup G}

private theorem local_frattini (T : Sylow 2 G) (D : Sylow 3 G)
    (he : Nonempty ((G ⧸ pCore 2 G) ≃* Equiv.Perm (Fin 3)))
    (hi : (pCore 2 G).relIndex (T : Subgroup G) = 2) :
    ((T : Subgroup G) ⊔ (D : Subgroup G) = ⊤) ∧
      ∃ t : G, t ∈ (T : Subgroup G) ∧ t ∉ pCore 2 G ∧
        t ∈ normalizer (D : Set G) := by
  obtain ⟨e⟩ := he
  let Q := pCore 2 G
  let q := QuotientGroup.mk' Q
  let Dbar := D.mapSurjective (QuotientGroup.mk'_surjective Q)
  let Tbar := T.mapSurjective (QuotientGroup.mk'_surjective Q)
  have hcard : Nat.card (G ⧸ Q) = 6 := by
    rw [Nat.card_congr e.toEquiv]
    simp [Nat.card_eq_fintype_card, Fintype.card_perm, Nat.factorial]
  have hdcard : Nat.card Dbar = 3 := by
    rw [Dbar.card_eq_multiplicity, hcard]
    have hf : Nat.factorization 6 3 = 1 := by
      change Nat.factorization (2 * 3) 3 = 1
      rw [Nat.factorization_mul (by decide) (by decide)]
      norm_num [Nat.prime_two.factorization, Nat.prime_three.factorization]
    rw [hf, pow_one]
  have htcard : Nat.card Tbar = 2 := by
    change Q.relIndex (T : Subgroup G) = 2 at hi
    rw [← QuotientGroup.ker_mk' Q, relIndex_ker] at hi
    exact hi
  have hdindex : (Dbar : Subgroup (G ⧸ Q)).index = 2 := by
    have hc := (Dbar : Subgroup (G ⧸ Q)).index_mul_card
    rw [hdcard, hcard] at hc
    omega
  let : (Dbar : Subgroup (G ⧸ Q)).Normal := normal_of_index_eq_two hdindex
  have hQT : Q ≤ (T : Subgroup G) := pCore_isPGroup.le_sylow_of_normal T
  have hgenbar : (Tbar : Subgroup (G ⧸ Q)) ⊔ (Dbar : Subgroup (G ⧸ Q)) = ⊤ := by
    apply IsComplement'.sup_eq_top
    apply isComplement'_of_coprime
    · rw [htcard, hdcard, hcard]
    · rw [htcard, hdcard]
      decide
  have hgen : (T : Subgroup G) ⊔ (D : Subgroup G) = ⊤ := by
    have hg := congrArg (fun H : Subgroup (G ⧸ Q) => H.comap q) hgenbar
    change (((T : Subgroup G).map q ⊔ (D : Subgroup G).map q).comap q) = _ at hg
    rw [← Subgroup.map_sup, comap_map_eq, QuotientGroup.ker_mk', comap_top,
      sup_eq_left.mpr (hQT.trans le_sup_left)] at hg
    exact hg
  refine ⟨hgen, ?_⟩
  have hnormbar : (normalizer (D : Set G)).map q = ⊤ := by
    rw [D.normalizer_map_surjective q (QuotientGroup.mk'_surjective Q)]
    exact (Dbar : Subgroup (G ⧸ Q)).normalizer_eq_top
  have hcover : Q ⊔ normalizer (D : Set G) = ⊤ := by
    have hh := congrArg (fun H : Subgroup (G ⧸ Q) => H.comap q) hnormbar
    rw [comap_map_eq, QuotientGroup.ker_mk', comap_top] at hh
    rwa [sup_comm] at hh
  have hnot : ¬ (T : Subgroup G) ≤ Q := by
    intro hle
    have hh : Q.relIndex (T : Subgroup G) = 1 := relIndex_eq_one.mpr hle
    exact (by decide : (2 : ℕ) ≠ 1) (hi.symm.trans hh)
  obtain ⟨s, hsT, hsQ⟩ := SetLike.not_le_iff_exists.mp hnot
  obtain ⟨a, ha, t, ht, hat⟩ := mem_sup_of_normal_left.mp
    (show s ∈ Q ⊔ normalizer (D : Set G) by rw [hcover]; trivial)
  have htT : t ∈ (T : Subgroup G) := by
    have hx := (T : Subgroup G).mul_mem ((T : Subgroup G).inv_mem (hQT ha)) hsT
    rw [← hat, inv_mul_cancel_left] at hx
    exact hx
  have htQ : t ∉ Q := fun hh => hsQ (hat ▸ Q.mul_mem ha hh)
  exact ⟨t, htT, htQ, ht⟩

omit [Finite G] in
private theorem index_two_generates (Q T : Subgroup G) (hQT : Q ≤ T)
    (hi : Q.relIndex T = 2) (t : G) (ht : t ∈ T) (htQ : t ∉ Q) :
    Q ⊔ zpowers t = T := by
  apply le_antisymm (sup_le hQT (zpowers_le.mpr ht))
  intro x hx
  by_cases hxQ : x ∈ Q
  · exact mem_sup_left hxQ
  · have hxt : x * t ∈ Q :=
      (mul_mem_iff_of_index_two (H := Q.subgroupOf T) hi
        (a := ⟨x, hx⟩) (b := ⟨t, ht⟩)).mpr (iff_of_false hxQ htQ)
    have hh := (Q ⊔ zpowers t).mul_mem (mem_sup_left hxt)
      (mem_sup_right ((zpowers t).inv_mem (mem_zpowers t)))
    simpa only [mul_inv_cancel_right] using hh

omit [Finite G] in
private theorem normalizes_conjugate_join (A S : Subgroup G) (t : G)
    (hAS : A ≤ normalizer (S : Set G)) (htA : t ∈ normalizer (A : Set G)) :
    A ≤ normalizer ((S ⊔ S.map (MulAut.conj t).toMonoidHom : Subgroup G) : Set G) := by
  apply le_trans (le_inf hAS ?_) (normalizer_inf_normalizer_le_normalizer_sup _ _)
  rw [← map_equiv_normalizer_eq S (MulAut.conj t)]
  have hh := map_mono (f := (MulAut.conj t).toMonoidHom) hAS
  have he : A.map (MulAut.conj t).toMonoidHom = A := mem_normalizer_iff_map_conj_eq.mp htA
  rwa [he] at hh

omit [Finite G] in
private theorem conjugator_normalizes_join (Q S : Subgroup G) (t : G)
    (hQS : Q ≤ normalizer (S : Set G)) (htsq : t ^ 2 ∈ Q) :
    t ∈ normalizer ((S ⊔ S.map (MulAut.conj t).toMonoidHom : Subgroup G) : Set G) := by
  apply mem_normalizer_iff_map_conj_eq.mpr
  change (S ⊔ S.map (MulAut.conj t).toMonoidHom).map (MulAut.conj t).toMonoidHom = _
  rw [Subgroup.map_sup, map_map]
  have hc : (MulAut.conj t).toMonoidHom.comp (MulAut.conj t).toMonoidHom =
      (MulAut.conj (t ^ 2)).toMonoidHom := by
    ext x
    change t * (t * x * t⁻¹) * t⁻¹ = t ^ 2 * x * (t ^ 2)⁻¹
    simp only [pow_two, mul_inv_rev]
    group
  have he : S.map (MulAut.conj (t ^ 2)).toMonoidHom = S :=
    mem_normalizer_iff_map_conj_eq.mp (hQS htsq)
  rw [hc, he, sup_comm]


/-- F.6.12(1), for the left local core and any actual Sylow three-subgroup
of the left generator. The normality hypothesis is relative to Q₁L₂. -/
public theorem IsGoldschmidtTriple.left_invariant_subgroup_eq_bot
    (h : IsGoldschmidtTriple G₁ G₂) (hcore : pCore 2 G = ⊥)
    (D : Sylow 3 G₁) (S : Subgroup G)
    (hSQ : S ≤ (pCore 2 G₁).map G₁.subtype)
    (hDS : (D : Subgroup G₁).map G₁.subtype ≤ normalizer (S : Set G))
    (hSN : (S.subgroupOf ((pCore 2 G₁).map G₁.subtype ⊔
      (pResidual 2 G₂).map G₂.subtype)).Normal) : S = ⊥ := by
  let Q := (pCore 2 G₁).map G₁.subtype
  let L := (pResidual 2 G₂).map G₂.subtype
  let Da := (D : Subgroup G₁).map G₁.subtype
  let T := G₁ ⊓ G₂
  obtain ⟨P, hP⟩ := h.intersection_sylow
  have hPG : (P : Subgroup G) ≤ G₁ := hP.symm.le.trans inf_le_left
  let P₁ := P.subtype hPG
  have hmapP : (P₁ : Subgroup G₁).map G₁.subtype = T := by
    change ((P : Subgroup G).subgroupOf G₁).map G₁.subtype = T
    rw [map_subgroupOf_eq_of_le hPG, ← hP]
  have hi : (pCore 2 G₁).relIndex (P₁ : Subgroup G₁) = 2 := by
    rw [← relIndex_map_map_of_injective _ _ G₁.subtype_injective, hmapP]
    exact h.left_core_index
  obtain ⟨hgen, t, htP, htQ, htD⟩ := local_frattini P₁ D h.quotient_left hi
  have htT : (t : G) ∈ T := hmapP ▸ mem_map_of_mem G₁.subtype htP
  have htQa : (t : G) ∉ Q := by
    intro ht
    exact htQ ((mem_map_iff_mem G₁.subtype_injective).mp ht)
  have htDa : (t : G) ∈ normalizer (Da : Set G) :=
    (D : Subgroup G₁).le_normalizer_map G₁.subtype (mem_map_of_mem G₁.subtype htD)
  have hTD : T ⊔ Da = G₁ := by
    have hh := congrArg (fun H : Subgroup G₁ => H.map G₁.subtype) hgen
    simpa only [Subgroup.map_sup, hmapP, ← MonoidHom.range_eq_map, range_subtype] using hh
  have hQSLS : Q ⊔ L ≤ normalizer (S : Set G) :=
    (normal_subgroupOf_iff_le_normalizer (hSQ.trans le_sup_left)).mp hSN
  have hQS : Q ≤ normalizer (S : Set G) := le_sup_left.trans hQSLS
  have hLS : L ≤ normalizer (S : Set G) := le_sup_right.trans hQSLS
  have htQN : (t : G) ∈ normalizer (Q : Set G) := h.left_core_normalized t.property
  have htLN : (t : G) ∈ normalizer (L : Set G) := h.intersection_normalizes_right_residual htT
  let R := S ⊔ S.map (MulAut.conj (t : G)).toMonoidHom
  have hQR : Q ≤ normalizer (R : Set G) := normalizes_conjugate_join Q S t hQS htQN
  have hDR : Da ≤ normalizer (R : Set G) := normalizes_conjugate_join Da S t hDS htDa
  have hLR : L ≤ normalizer (R : Set G) := normalizes_conjugate_join L S t hLS htLN
  have htsq : (t : G) ^ 2 ∈ Q :=
    (Q.subgroupOf T).sq_mem_of_index_two h.left_core_index ⟨t, htT⟩
  have htR : (t : G) ∈ normalizer (R : Set G) := conjugator_normalizes_join Q S t hQS htsq
  have hTR : T ≤ normalizer (R : Set G) := by
    rw [← index_two_generates Q T h.local_twoCore_le_intersection h.left_core_index t htT htQa]
    exact sup_le hQR (zpowers_le.mpr htR)
  have hG₁R : G₁ ≤ normalizer (R : Set G) := hTD ▸ sup_le hTR hDR
  have hG₂R : G₂ ≤ normalizer (R : Set G) := by
    rw [← h.right_residual_sup_intersection]
    exact sup_le hLR hTR
  have hRQ : R ≤ Q := by
    apply sup_le hSQ
    have hh := map_mono (f := (MulAut.conj (t : G)).toMonoidHom) hSQ
    have he : Q.map (MulAut.conj (t : G)).toMonoidHom = Q :=
      mem_normalizer_iff_map_conj_eq.mp htQN
    exact hh.trans_eq he
  have hRT := hRQ.trans h.local_twoCore_le_intersection
  have hRbot := h.common_normal_eq_bot hcore R hRT
    ((normal_subgroupOf_iff_le_normalizer (hRT.trans inf_le_left)).mpr hG₁R)
    ((normal_subgroupOf_iff_le_normalizer (hRT.trans inf_le_right)).mpr hG₂R)
  exact le_bot_iff.mp ((le_sup_left : S ≤ R).trans_eq hRbot)


/-- F.6.12(1), with the two generators interchanged. -/
public theorem IsGoldschmidtTriple.right_invariant_subgroup_eq_bot
    (h : IsGoldschmidtTriple G₁ G₂) (hcore : pCore 2 G = ⊥)
    (D : Sylow 3 G₂) (S : Subgroup G)
    (hSQ : S ≤ (pCore 2 G₂).map G₂.subtype)
    (hDS : (D : Subgroup G₂).map G₂.subtype ≤ normalizer (S : Set G))
    (hSN : (S.subgroupOf ((pCore 2 G₂).map G₂.subtype ⊔
      (pResidual 2 G₁).map G₁.subtype)).Normal) : S = ⊥ :=
  h.symm.left_invariant_subgroup_eq_bot hcore D S hSQ hDS hSN

/-- F.6.12(2): characteristic means characteristic inside the local core,
whereas normality is inside the larger subgroup Q₁L₂. -/
public theorem IsGoldschmidtTriple.left_characteristic_subgroup_eq_bot
    (h : IsGoldschmidtTriple G₁ G₂) (hcore : pCore 2 G = ⊥)
    (S : Subgroup G) (hSQ : S ≤ (pCore 2 G₁).map G₁.subtype)
    (hchar : (S.subgroupOf ((pCore 2 G₁).map G₁.subtype)).Characteristic)
    (hSN : (S.subgroupOf ((pCore 2 G₁).map G₁.subtype ⊔
      (pResidual 2 G₂).map G₂.subtype)).Normal) : S = ⊥ := by
  let Q := (pCore 2 G₁).map G₁.subtype
  let D : Sylow 3 G₁ := Classical.choice inferInstance
  apply h.left_invariant_subgroup_eq_bot hcore D S hSQ ?_ hSN
  apply le_normalizer_iff.mpr
  intro d hd s hs
  have hdQ : d ∈ normalizer (Q : Set G) := h.left_core_normalized (map_subtype_le _ hd)
  let a := Q.normalizerMonoidHom ⟨d, hdQ⟩
  exact characteristic_iff_le_comap.mp hchar a (show (⟨s, hSQ hs⟩ : Q) ∈ S.subgroupOf Q from hs)

/-- F.6.12(2), with the two generators interchanged. -/
public theorem IsGoldschmidtTriple.right_characteristic_subgroup_eq_bot
    (h : IsGoldschmidtTriple G₁ G₂) (hcore : pCore 2 G = ⊥)
    (S : Subgroup G) (hSQ : S ≤ (pCore 2 G₂).map G₂.subtype)
    (hchar : (S.subgroupOf ((pCore 2 G₂).map G₂.subtype)).Characteristic)
    (hSN : (S.subgroupOf ((pCore 2 G₂).map G₂.subtype ⊔
      (pResidual 2 G₁).map G₁.subtype)).Normal) : S = ⊥ :=
  h.symm.left_characteristic_subgroup_eq_bot hcore S hSQ hchar hSN

end CFSG.Quasithin.ChapterF
