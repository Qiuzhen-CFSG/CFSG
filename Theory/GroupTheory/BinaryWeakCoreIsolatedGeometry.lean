module
public import Theory.GroupTheory.IsolatedFourTwoGroup

/-!
# Local geometry in the isolated binary weak-core case

An isolated four-group in a rank-three two-group contains a central involution.
If the ambient centralizer of Q has a unique involution, this identifies its
involution with the central involution in every isolated four-group of Q.
In particular the same involution is central in the selected two-group.
Moreover, if every four-subgroup of Q is isolated, C_S(Q) is noncyclic:
a cyclic quotient of the elementary eight B has order at most two, so
the intersection B ∩ Q contains a four-group, contradicting isolation.
If the entire ambient centralizer is a two-group, its join with Q is a
two-group containing B and already gives the required component transport.

These are local reductions for the binary fusion remark following GLS2,
Proposition 22.4 (`refs/KGroup/GLS2/ChapterF.tex`), using the geometry of
Lemma 10.21(iii). They do not identify an ambient four-group extension with
an extension inside a specified Sylow subgroup.
-/

namespace Subgroup

/-- The weak-rank centralizer transport holds whenever the entire ambient
centralizer is a two-group, without isolation or simplicity hypotheses. -/
public theorem elementaryCommutingConnected_conj_of_twoGroup_centralizer
    {G : Type*} [Group G] [Finite G] (S A Q B : Subgroup G)
    (hS : IsPGroup 2 S)
    [IsElementaryAbelian 2 A] [IsElementaryAbelian 2 B]
    (hA : 8 ≤ Nat.card A) (hB : 8 ≤ Nat.card B)
    (hAS : A ≤ S) (hQS : Q ≤ S)
    (hBweak : B ≤ Q ⊔ (S ⊓ centralizer (Q : Set G)))
    (hC : IsPGroup 2 (centralizer (Q : Set G)))
    (c : G) (hc : c ∈ centralizer (Q : Set G)) :
    ElementaryCommutingConnected 2 A (A.map (MulAut.conj c).toMonoidHom) := by
  let R := Q ⊔ centralizer (Q : Set G)
  have hQ : IsPGroup 2 Q :=
    hS.of_injective (inclusion hQS) (inclusion_injective hQS)
  have hR : IsPGroup 2 R :=
    hQ.to_sup_of_normal_left' hC (centralizer_le_normalizer _)
  have hBR : B ≤ R := hBweak.trans (sup_le_sup_left inf_le_right Q)
  have hBS : B ≤ S := hBweak.trans (sup_le hQS inf_le_left)
  have hcR : c ∈ R := (le_sup_right : centralizer (Q : Set G) ≤ R) hc
  let e := MulAut.conj c
  let : IsElementaryAbelian 2 (B.map e.toMonoidHom) := IsElementaryAbelian.map _
  have hBcR : B.map e.toMonoidHom ≤ R := (map_mono hBR).trans
    (mem_normalizer_iff_map_conj_eq.mp (R.le_normalizer hcR)).le
  have hAB := elementaryCommutingConnected_of_le_twoGroup S A B hS hA hB hAS hBS
  have hBBc := elementaryCommutingConnected_of_le_twoGroup R B (B.map e.toMonoidHom)
    hR hB (by rwa [card_map_of_injective e.injective]) hBR hBcR
  exact hAB.trans (hBBc.trans (hAB.symm.map e))

private theorem isolated_four_subgroupOf_twoGroup
    {G : Type*} [Group G] [Finite G] (S E : Subgroup G) (hES : E ≤ S)
    (hiso : ∀ W : Subgroup G, IsElementaryAbelian 2 W → Nat.card W = 4 →
      W ≤ S → W ≤ centralizer (E : Set G) → W = E) :
    ∀ W : Subgroup S, IsElementaryAbelian 2 W → Nat.card W = 4 →
      W ≤ centralizer (E.subgroupOf S : Set S) → W = E.subgroupOf S := by
  intro W hWe hW hWC
  let : IsElementaryAbelian 2 W := hWe
  have hm : W.map S.subtype = E := hiso _ (IsElementaryAbelian.map S.subtype)
    (by simpa only [card_map_of_injective S.subtype_injective] using hW)
    (map_subtype_le _) (by
      rintro x ⟨w, hw, rfl⟩ e he
      exact congrArg Subtype.val (hWC hw ⟨e, hES he⟩ he))
  apply map_injective S.subtype_injective
  rw [hm, map_subgroupOf_eq_of_le hES]

/-- The unique involution of the ambient centralizer is in Q, centralizes S,
and is centralized by the entire ambient centralizer. Only one isolated
four-group of Q is needed for this conclusion. -/
public theorem central_involution_of_isolated_four_of_unique_centralizer
    {G : Type*} [Group G] [Finite G] (S A Q E : Subgroup G)
    (hS : IsPGroup 2 S) [IsElementaryAbelian 2 A] [IsElementaryAbelian 2 E]
    (hA : 8 ≤ Nat.card A) (hE : Nat.card E = 4)
    (hAS : A ≤ S) (hQS : Q ≤ S) (hEQ : E ≤ Q)
    (hiso : ∀ W : Subgroup G, IsElementaryAbelian 2 W → Nat.card W = 4 →
      W ≤ S → W ≤ centralizer (E : Set G) → W = E)
    (hunique : ∃! t : centralizer (Q : Set G), orderOf t = 2) :
    ∃ z : G, orderOf z = 2 ∧ z ∈ E ∧ z ∈ Q ∧
      z ∈ centralizer (S : Set G) ∧
      centralizer (Q : Set G) ≤ centralizer ({z} : Set G) := by
  have hES := hEQ.trans hQS
  let : IsElementaryAbelian 2 (A.subgroupOf S) := IsElementaryAbelian.subgroupOf hAS
  let : IsElementaryAbelian 2 (E.subgroupOf S) := IsElementaryAbelian.subgroupOf hES
  have hAc : 8 ≤ Nat.card (A.subgroupOf S) := by
    rwa [Nat.card_congr (subgroupOfEquivOfLe hAS).toEquiv]
  have hEc : Nat.card (E.subgroupOf S) = 4 := by
    rwa [Nat.card_congr (subgroupOfEquivOfLe hES).toEquiv]
  obtain ⟨U, hUn, hUe, hU⟩ := hS.exists_normal_elementaryAbelian_four (A.subgroupOf S) hAc
  let : U.Normal := hUn
  let : IsElementaryAbelian 2 U := hUe
  obtain ⟨z, hz, hzZ, hzEU, -, -⟩ := exists_central_generator_inf_of_isolated_four
    hS (A.subgroupOf S) U (E.subgroupOf S) hAc hU hEc
    (isolated_four_subgroupOf_twoGroup S E hES hiso)
  have hzE : (z : G) ∈ E := (show z ∈ E.subgroupOf S ⊓ U from
    hzEU ▸ mem_zpowers z).1
  have hzS : (z : G) ∈ centralizer (S : Set G) := by
    intro s hs
    exact congrArg Subtype.val (mem_center_iff.mp hzZ ⟨s, hs⟩)
  have hzQ := hEQ hzE
  have hzC : (z : G) ∈ centralizer (Q : Set G) := centralizer_le hQS hzS
  have hzG : orderOf (z : G) = 2 := by simpa only [orderOf_coe] using hz
  let zC : centralizer (Q : Set G) := ⟨z, hzC⟩
  have hzCorder : orderOf zC = 2 := by
    rw [← orderOf_coe]
    exact hzG
  refine ⟨z, hzG, hzE, hzQ, hzS, ?_⟩
  intro c hc
  let cC : centralizer (Q : Set G) := ⟨c, hc⟩
  have heq : MulAut.conj cC zC = zC := hunique.unique
    ((MulAut.conj cC).orderOf_eq zC |>.trans hzCorder) hzCorder
  have heqG : c * (z : G) * c⁻¹ = z := congrArg Subtype.val heq
  exact mem_centralizer_singleton_iff.mpr (mul_inv_eq_iff_eq_mul.mp heqG)

private theorem elementary_subgroup {H : Type*} [Group H] [IsElementaryAbelian 2 H]
    (K : Subgroup H) : IsElementaryAbelian 2 K := {
  toIsMulCommutative := inferInstance
  exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr fun x =>
    Subtype.ext (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p 2 H) x) }

private theorem four_in_kernel_of_cyclic_image
    {H K : Type*} [Group H] [Group K] [Finite H] [Finite K]
    [IsElementaryAbelian 2 H] [IsCyclic K] (f : H →* K) (hH : 8 ≤ Nat.card H) :
    ∃ F : Subgroup H, IsElementaryAbelian 2 F ∧ Nat.card F = 4 ∧ F ≤ f.ker := by
  have hrange : Nat.card f.range ≤ 2 := by
    have hexp : Monoid.exponent f.range ∣ 2 :=
      Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr (by
        rintro ⟨_, x, rfl⟩
        apply Subtype.ext
        change f x ^ 2 = 1
        rw [← map_pow, Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
          (IsElementaryAbelian.exponent_dvd_p 2 H) x, map_one])
    rw [IsCyclic.exponent_eq_card] at hexp
    exact Nat.le_of_dvd (by decide) hexp
  have hker : 4 ≤ Nat.card f.ker := by
    have hc := f.ker.card_mul_index
    rw [index_ker] at hc
    nlinarith
  obtain ⟨F, hFker, hFcard⟩ := Sylow.exists_subgroup_le_card_pow_prime_of_le_card
    (by decide : Nat.Prime 2) (IsElementaryAbelian.isPGroup 2 H)
    (show 2 ^ 2 ≤ Nat.card f.ker from hker)
  exact ⟨F, elementary_subgroup F, hFcard, hFker⟩

/-- If all four-subgroups of Q are isolated in S, a rank-three elementary
subgroup of Q C_S(Q) forces C_S(Q) to be noncyclic. This assertion is purely
local and needs neither simplicity nor absence of normal four-groups. -/
public theorem not_isCyclic_centralizer_of_isolated_fours_of_weak_rank
    {G : Type*} [Group G] [Finite G] (S Q B : Subgroup G)
    [IsElementaryAbelian 2 B] (hB : 8 ≤ Nat.card B) (hQS : Q ≤ S)
    (hBweak : B ≤ Q ⊔ (S ⊓ centralizer (Q : Set G)))
    (hiso : ∀ V : Subgroup G, IsElementaryAbelian 2 V → Nat.card V = 4 → V ≤ Q →
      ∀ W : Subgroup G, IsElementaryAbelian 2 W → Nat.card W = 4 →
        W ≤ S → W ≤ centralizer (V : Set G) → W = V) :
    ¬ IsCyclic (S ⊓ centralizer (Q : Set G) : Subgroup G) := by
  intro hcyc
  let C := S ⊓ centralizer (Q : Set G)
  let D := C ⊔ Q
  have hCQ : C ≤ normalizer (Q : Set G) := inf_le_right.trans (centralizer_le_normalizer _)
  have hBD : B ≤ D := by simpa only [D, sup_comm, C] using hBweak
  have hDS : D ≤ S := sup_le inf_le_left hQS
  let : (Q.subgroupOf D).Normal := normal_subgroupOf_sup_of_le_normalizer hCQ
  let : IsCyclic C := hcyc
  let : (Q.subgroupOf C).Normal := normal_subgroupOf_of_le_normalizer hCQ
  let : IsCyclic (C ⧸ Q.subgroupOf C) := isCyclic_of_surjective
    (QuotientGroup.mk' (Q.subgroupOf C)) (QuotientGroup.mk'_surjective _)
  let e := QuotientGroup.quotientInfEquivProdNormalizerQuotient C Q hCQ
  let : IsCyclic (D ⧸ Q.subgroupOf D) := isCyclic_of_surjective e e.surjective
  let f : B →* D ⧸ Q.subgroupOf D :=
    (QuotientGroup.mk' (Q.subgroupOf D)).comp (inclusion hBD)
  obtain ⟨F, hFe, hF, hFker⟩ := four_in_kernel_of_cyclic_image f hB
  let : IsElementaryAbelian 2 F := hFe
  let V := F.map B.subtype
  have hVB : V ≤ B := map_subtype_le _
  have hVS : V ≤ S := hVB.trans (hBD.trans hDS)
  have hVQ : V ≤ Q := by
    rintro v ⟨b, hb, rfl⟩
    exact (QuotientGroup.eq_one_iff (N := Q.subgroupOf D) (inclusion hBD b)).mp (hFker hb)
  let : IsElementaryAbelian 2 V := IsElementaryAbelian.map_subtype
  have hV : Nat.card V = 4 := by
    rw [card_map_of_injective B.subtype_injective]
    exact hF
  let : IsElementaryAbelian 2 (B.subgroupOf S) := IsElementaryAbelian.subgroupOf (hBD.trans hDS)
  let : IsElementaryAbelian 2 (V.subgroupOf S) := IsElementaryAbelian.subgroupOf hVS
  have hVBS : V.subgroupOf S ≤ B.subgroupOf S := fun _ hx => hVB hx
  have hBSV := maximal_elementary_of_isolated_four (V.subgroupOf S)
    (by rwa [Nat.card_congr (subgroupOfEquivOfLe hVS).toEquiv])
    (isolated_four_subgroupOf_twoGroup S V hVS (hiso V inferInstance hV hVQ))
    (B.subgroupOf S) inferInstance hVBS
  have hc := card_le_of_le hBSV
  rw [Nat.card_congr (subgroupOfEquivOfLe (hBD.trans hDS)).toEquiv,
    Nat.card_congr (subgroupOfEquivOfLe hVS).toEquiv, hV] at hc
  omega

end Subgroup
