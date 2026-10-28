module

public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.Basic
public import Mathlib.GroupTheory.Complement
import Mathlib.GroupTheory.Nilpotent

/-!
# The quotient contradiction in the proper linear case

The last paragraph of GLS, Volume 4, Chapter 2, Section 15 uses two local
conclusions: `D` has a normal complement in `M` (Lemma 15.7), and `O²(D)`
is proper (from Lemmas 15.2(b) and 15.6). The resulting surjection from
`M` onto `D/O²(D)` contradicts focal transfer and ambient simplicity.

We prove that endpoint using the narrow focal interface already imported
by `Generation.Basic`. The complement is a subgroup of `M`, normal in
`M`; ambient normality is neither asserted nor needed. The quotient is
by the two-residual, not by the odd core used in `residualGenerated`.

The local conclusions remain explicit premises here. This module does not
yet prove Proposition 15.1 or `proper_residualGenerated_linear_false`.
Their construction from the actual linear model is the remaining work.
-/

noncomputable section

namespace BenderSuzuki.ZD

open Theory.GroupTheory PFAppendixIII PFchapter1section1

universe u

/-- The centralizer of the generated subgroup fixes both distinguished
cosets: it centralizes `z`, so lies in `M`, and centralizes `t`, so also
lies in `Mᵗ`. This part of source 12.2(d) needs no model identification. -/
public theorem centralizer_residualGenerated_le_pair
    {G : Type*} [Group G] {Z : Set G} {M : Subgroup G}
    (h : IsProductDisconnected Z M) {z t : G} (hz : z ∈ Z) (hzM : z ∈ M) :
    Subgroup.centralizer (residualGenerated M z t : Set G) ≤
      residualPairStabilizer M t := by
  have hzL : z ∈ residualGenerated M z t :=
    (show Subgroup.zpowers z ≤ residualGenerated M z t from
      le_sup_left.trans le_sup_left) (Subgroup.mem_zpowers z)
  have htL : t ∈ residualGenerated M z t :=
    (show Subgroup.zpowers t ≤ residualGenerated M z t from
      le_sup_right.trans le_sup_left) (Subgroup.mem_zpowers t)
  intro x hx
  have hzx : z * x = x * z := Subgroup.mem_centralizer_iff.mp hx z hzL
  have htx : t * x = x * t := Subgroup.mem_centralizer_iff.mp hx t htL
  have hxM : x ∈ M := mem_of_commute h hz hzM hzx
  refine ⟨hxM, ?_⟩
  change x ∈ rightConjugate M t
  rw [rightConjugate, Subgroup.conjBy, Subgroup.mem_map]
  refine ⟨x, hxM, ?_⟩
  simp only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe, MulAut.conj_apply, inv_inv]
  rw [mul_assoc, ← htx, inv_mul_cancel_left]

/-- The intersection `D ∩ L` has odd order when `L` is proper. An
involution in this intersection would belong to `Z` by local strong
embedding, whereas no element of `D` belongs to `Z`. This establishes
oddness, not the cyclicity and exact order also required in source 12.2(f). -/
public theorem pair_inf_proper_residualGenerated_odd
    {G : Type*} [Group G] [Finite G] {Z : Set G} {M : Subgroup G}
    (h : IsProductDisconnected Z M) (r : SimpleReduction Z M)
    {z t : G} (hz : z ∈ Z) (hzM : z ∈ M) (ht : t ∈ Z) (htM : t ∉ M)
    (hL : residualGenerated M z t ≠ ⊤) :
    Odd (Nat.card (residualPairStabilizer M t ⊓ residualGenerated M z t : Subgroup G)) := by
  apply Nat.not_even_iff_odd.mp
  intro heven
  let H := residualPairStabilizer M t ⊓ residualGenerated M z t
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := H) 2 heven.two_dvd
  have hxi : IsInvolution x := (orderOf_eq_prime_iff.mp hx).symm
  have hxG : IsInvolution (x : G) :=
    IsInvolution.map_of_injective hxi H.subtype Subtype.val_injective
  have hxZ := (isInvolution_iff_mem_Z_in_proper_residualGenerated
    h r hz hzM ht htM hL x.property.2).mp hxG
  exact not_mem_Z_of_mem_residualPairStabilizer h htM x.property.1 hxZ

private theorem even_abelianization_of_proper_twoResidual
    {H : Type*} [Group H] [Finite H]
    (hres : External.hallPResidual 2 H ≠ ⊤) :
    2 ∣ Nat.card (H ⧸ derivedSubgroup H) := by
  let R := External.hallPResidual 2 H
  let : R.Normal := External.hallPResidual_normal 2 H
  let Q := H ⧸ R
  let : Nontrivial Q := QuotientGroup.nontrivial_iff.mpr hres
  have hQ : IsPGroup 2 Q := External.hallPResidual_quotient_isPGroup 2
  let : Group.IsNilpotent Q := hQ.isNilpotent
  have hcomm : commutator Q ≠ ⊤ :=
    (Group.IsSolvable.commutator_lt_top_of_nontrivial Q).ne
  obtain ⟨n, hn⟩ := (hQ.to_quotient (commutator Q)).exists_card_eq
  have hnpos : n ≠ 0 := by
    intro hnzero
    have hidx := Subgroup.one_lt_index_of_ne_top hcomm
    rw [Subgroup.index_eq_card, hn, hnzero] at hidx
    norm_num at hidx
  have heven : 2 ∣ (commutator Q).index := by
    rw [Subgroup.index_eq_card, hn]
    exact dvd_pow_self 2 hnpos
  let q : H →* Q := QuotientGroup.mk' R
  have hmap : (commutator H).map q = commutator Q := by
    rw [map_commutator_eq, q.range_eq_top_of_surjective (QuotientGroup.mk'_surjective R)]
    rfl
  have hle : commutator H ≤ (commutator Q).comap q :=
    Subgroup.map_le_iff_le_comap.mp hmap.le
  have hdvd := Subgroup.index_dvd_of_le hle
  rw [Subgroup.index_comap_of_surjective _ (QuotientGroup.mk'_surjective R)] at hdvd
  simpa only [derivedSubgroup, derivedSeries_one, Subgroup.index_eq_card] using
    heven.trans hdvd

/-- The source 15.2(g) residual conclusion, proved without importing the
residual assembly module. Fusion is controlled only on an ambient Sylow
subgroup contained in `M`; strong embedding of `M` is not assumed. -/
public theorem SimpleReduction.linear_twoResidual_eq_top
    {G : Type u} [Group G] [Finite G] {Z : Set G} {M : Subgroup G}
    (r : SimpleReduction Z M) (h : IsProductDisconnected Z M) :
    External.hallPResidual 2 M = ⊤ := by
  by_contra hres
  obtain ⟨S, hSM, hfusion⟩ := r.fusion
  obtain ⟨hlt, hsup⟩ :=
    hallPResidual_factorization_of_dvd_abelianization_of_controlsFusionIn
      M S hSM hfusion (even_abelianization_of_proper_twoResidual hres)
  rcases r.simple.eq_bot_or_eq_top_of_normal (External.hallPResidual 2 G)
      (External.hallPResidual_normal 2 G) with hbot | htop
  · exact h.proper (by simpa [hbot] using hsup)
  · exact hlt.ne htop

/-- The final quotient argument of Proposition 15.1. Its two local
premises must still be established from the proper linear model: a normal
complement in `M` and a proper two-residual of the actual two-point group. -/
public theorem linearExclusion_of_pair_normalComplement
    {G : Type u} [Group G] [Finite G] {Z : Set G} {M : Subgroup G}
    (r : SimpleReduction Z M) (h : IsProductDisconnected Z M) {t : G}
    (N : Subgroup M) (hN : N.Normal)
    (hsplit : ((residualPairStabilizer M t).subgroupOf M).IsComplement' N)
    (hD : External.hallPResidual 2 (residualPairStabilizer M t) ≠ ⊤) :
    False := by
  let D := residualPairStabilizer M t
  let R := External.hallPResidual 2 D
  let : N.Normal := hN
  let : R.Normal := External.hallPResidual_normal 2 D
  let Q := D ⧸ R
  let : Nontrivial Q := QuotientGroup.nontrivial_iff.mpr hD
  let eD : D.subgroupOf M ≃* D := Subgroup.subgroupOfEquivOfLe inf_le_left
  let f : M →* Q := (QuotientGroup.mk' R).comp
    (eD.toMonoidHom.comp
      (hsplit.QuotientMulEquiv.toMonoidHom.comp (QuotientGroup.mk' N)))
  have hf : Function.Surjective f :=
    (QuotientGroup.mk'_surjective R).comp
      (eD.surjective.comp
        (hsplit.QuotientMulEquiv.surjective.comp (QuotientGroup.mk'_surjective N)))
  have hQ : IsPGroup 2 Q := External.hallPResidual_quotient_isPGroup 2
  have hker := External.hallPResidual_le_ker_of_isPGroup f hQ
  rw [r.linear_twoResidual_eq_top h] at hker
  obtain ⟨x, hx⟩ := exists_ne (1 : Q)
  obtain ⟨y, rfl⟩ := hf x
  exact hx (MonoidHom.mem_ker.mp (hker (Subgroup.mem_top y)))

end BenderSuzuki.ZD
