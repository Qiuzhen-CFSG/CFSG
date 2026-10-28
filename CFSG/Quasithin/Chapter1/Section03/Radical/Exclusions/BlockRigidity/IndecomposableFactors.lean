module

public import CFSG.Quasithin.Chapter1.Section03.Radical.Exclusions.BlockRigidity.SourceContracts
public import CFSG.Quasithin.Chapter1.Section03.Radical.Exclusions.BlockRigidity.CenterAndTrace
public import CFSG.Quasithin.Chapter1.Section03.Radical.Exclusions.ResidualFactors
public import CFSG.Quasithin.Chapter1.Section03.Radical.Exclusions.CenterProduct
public import Theory.GroupTheory.NormalizedSupCard
public import Theory.GroupTheory.PPerfectHom

/-!
# Direct indecomposability of the residual quotient factors

Write W = O²(X ∩ K). The actual plane isomorphism and the nontrivial,
proper intersection P ∩ K give |P ∩ K| = p. Since W is normalized by X,
|WP| = |W|p, whereas the odd complement gives |X| = 2ⁿp². Thus |W|
divides 2ⁿp, and so does the order of its image in X/Z(X).

This image is nontrivial by its odd trace and the two-group center of X.
It is two-perfect because W is a finite two-residual. If it split into two
nontrivial direct factors, both projections would be two-perfect. Neither
factor could be a two-group, so both orders would be divisible by p,
contradicting the cardinality bound. The actual normalizer action on X/Z(X)
transports these facts to the conjugate factor.

This proves the indecomposability needed for A.1.15 without assuming
commutation of W and its conjugate, or a permutation of the factor pair.
Source: Aschbacher–Smith, combined manuscript of 1 March 2004, proof of
Proposition 1.3.8, printed p.514, and Lemma A.1.15, printed p.23.
-/

@[expose] public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter1.RadicalExclusions
open XiEmbedding BlockRigidity
variable {G : Type*} [Group G] [Finite G]

/-- The nontrivial proper trace in the actual plane has order p. -/
theorem BinaryBlockEmbedding.complement_intersection_card {p : ℕ} {T X P H₀ K : Subgroup G}
    (h : BinaryBlockEmbedding p T X P H₀ K) : Nat.card (P ⊓ K : Subgroup G) = p := by
  have hP : Nat.card P = p ^ 2 :=
    (Nat.card_congr h.plane.some.toEquiv).trans (plane_card p)
  obtain ⟨n, hn, he⟩ := (Nat.dvd_prime_pow h.local_input.prime).mp
    (hP ▸ card_dvd_of_le (show P ⊓ K ≤ P from inf_le_left))
  have h0 : n ≠ 0 := by
    intro hn
    rw [hn, pow_zero, card_eq_one] at he
    exact h.complement_intersection.1 he
  have h2 : n ≠ 2 := by
    intro hn
    have heq : P ⊓ K = P := eq_of_le_of_card_ge inf_le_left (by rw [he, hn, hP])
    exact h.complement_intersection.2 (heq.symm.le.trans inf_le_right)
  have : n = 1 := by omega
  simpa [this] using he

omit [Finite G] in
private theorem odd_intersection_le_residual {p : ℕ} {P X K : Subgroup G}
    (hp : Odd p) (hP : IsPGroup p P) (hPX : P ≤ X) :
    P ⊓ K ≤ blockResidual X K := by
  intro a ha
  let a₀ : (X ⊓ K : Subgroup G) := ⟨a, hPX ha.1, ha.2⟩
  refine mem_map.mpr ⟨a₀, mem_pResidual_of_orderOf_coprime ?_, rfl⟩
  have hc := (hP.orderOf_coprime hp.coprime_two_right ⟨a, ha.1⟩).symm
  simpa only [← Subgroup.orderOf_coe] using hc

/-- The order of the block residual has at most one odd prime factor, counted
with multiplicity. -/
theorem BinaryBlockEmbedding.blockResidual_card_dvd {p : ℕ} {T X P H₀ K : Subgroup G}
    (h : BinaryBlockEmbedding p T X P H₀ K) :
    ∃ n, Nat.card (blockResidual X K) ∣ 2 ^ n * p := by
  let _ : Fact p.Prime := ⟨h.local_input.prime⟩
  let W := blockResidual X K
  have hWX : W ≤ X := (blockResidual_le X K).trans inf_le_left
  have hPX := h.local_input.complement_le
  have hXK : X ≤ normalizer K := h.containment.trans
    (cComponentOrbit_le_normalizer h.component (le_sup_right.trans h.local_input.overgroup))
  have hXW : X ≤ normalizer W := normalizes_blockResidual X.le_normalizer hXK
  have hi : W ⊓ P = P ⊓ K := by
    apply le_antisymm
    · exact le_inf inf_le_right (inf_le_left.trans ((blockResidual_le X K).trans inf_le_right))
    · exact le_inf (odd_intersection_le_residual h.local_input.odd
        h.local_input.odd_complement.isPGroup hPX) inf_le_left
  have hP : Nat.card P = p ^ 2 :=
    (Nat.card_congr h.plane.some.toEquiv).trans (plane_card p)
  have hw := card_mul_eq_card_inf_mul_card_sup_of_normalizes W P (hPX.trans hXW)
  rw [hi, h.complement_intersection_card, hP] at hw
  have hw' : Nat.card W * p = Nat.card (W ⊔ P : Subgroup G) := by
    nlinarith [h.local_input.prime.pos]
  obtain ⟨n, hn⟩ := (isPGroup_pCoreIn 2 X).exists_card_eq
  have hX : Nat.card X = 2 ^ n * p ^ 2 := by
    rw [← h.local_input.complement, card_sup_eq_mul_of_normalizes_of_disjoint]
    · rw [hn, hP]
    · exact hPX.trans (X.le_normalizer.trans
        (normalizer_le_normalizer_characteristic_image X (pCore 2 X)))
    · exact h.local_input.disjoint
  refine ⟨n, Nat.dvd_of_mul_dvd_mul_right h.local_input.prime.pos ?_⟩
  rw [hw', mul_assoc, ← pow_two, ← hX]
  exact card_dvd_of_le (sup_le hWX hPX)

private theorem indecomposable_of_card_dvd {D : Type*} [Group D] [Finite D]
    {p n : ℕ} (hp : p.Prime) (ho : Odd p) (hD : IsPPerfect 2 D)
    (hne : Nontrivial D) (hc : Nat.card D ∣ 2 ^ n * p) : DirectlyIndecomposable D := by
  refine ⟨hne, fun A B hd hcomm hgen => ?_⟩
  obtain ⟨e₀, _⟩ := exists_mulEquiv_prod_sup_of_disjoint_of_commuting A B hd
    (commutator_eq_bot_iff_le_centralizer.mp hcomm)
  let e : A × B ≃* D := e₀.trans ((MulEquiv.subgroupCongr hgen).trans topEquiv)
  have hcard : Nat.card A * Nat.card B = Nat.card D :=
    (Nat.card_prod A B).symm.trans (Nat.card_congr e.toEquiv)
  have hA : IsPPerfect 2 A := hD.of_surjective
    ((MonoidHom.fst A B).comp e.symm.toMonoidHom)
    (fun a => ⟨e (a, 1), by simp⟩)
  have hB : IsPPerfect 2 B := hD.of_surjective
    ((MonoidHom.snd A B).comp e.symm.toMonoidHom)
    (fun b => ⟨e (1, b), by simp⟩)
  have hbot (C : Subgroup D) (hC : IsPPerfect 2 C) (hpc : ¬ p ∣ Nat.card C) : C = ⊥ := by
    have hdiv : Nat.card C ∣ 2 ^ n :=
      (hp.coprime_iff_not_dvd.mpr hpc).symm.dvd_of_dvd_mul_right
        (C.card_subgroup_dvd_card.trans hc)
    have he := hC.hom_eq_one_of_isPGroup (IsPGroup.of_card_dvd_pow hdiv) (MonoidHom.id C)
    apply eq_bot_iff.mpr
    intro c hc
    exact congrArg Subtype.val (DFunLike.congr_fun he ⟨c, hc⟩)
  by_cases ha : p ∣ Nat.card A
  · by_cases hb : p ∣ Nat.card B
    · have hdvd : p * p ∣ 2 ^ n * p := (hcard ▸ Nat.mul_dvd_mul ha hb).trans hc
      have hp2 : p ∣ 2 ^ n := Nat.dvd_of_mul_dvd_mul_right hp.pos hdvd
      exact False.elim (hp.ne_one (Nat.eq_one_of_dvd_coprimes (ho.coprime_two_right.pow_right n) dvd_rfl hp2))
    · exact Or.inr (hbot B hB hb)
  · exact Or.inl (hbot A hA ha)

/-- The nontrivial odd trace survives the quotient by the two-group center. -/
theorem BinaryBlockEmbedding.centerFactor_nontrivial {p : ℕ} {T X P L₀ M H₀ K : Subgroup G}
    (h : BinaryBlockEmbedding p T X P H₀ K) (hc : Configuration p T X P L₀ M)
    (h114 : HOver G (T : Set G) ⊆ He G) :
    Nontrivial (centerFactor X (blockResidual X K)) := by
  let _ : Fact p.Prime := ⟨hc.prime⟩
  apply (nontrivial_iff_ne_bot _).mpr
  intro hb
  have he := centerFactor_preimage ((blockResidual_le X K).trans inf_le_left)
  rw [hb, MonoidHom.comap_bot, QuotientGroup.ker_mk'] at he
  have hi := h.odd_trace hc h114
  rw [← he] at hi
  have hd := h.local_input.odd_complement.isPGroup.disjoint_of_coprime
    ((xi_center_isPGroup_of_global_He h114 hc.xi).map X.subtype) hc.odd.coprime_two_right
  exact h.complement_intersection.1 (hi.symm.trans (disjoint_iff.mp hd))

omit [Finite G] in
/-- Passing to the actual quotient image preserves two-perfectness. -/
theorem centerFactor_isPPerfect {X W : Subgroup G} (hWX : W ≤ X)
    (hW : IsPPerfect 2 W) : IsPPerfect 2 (centerFactor X W) := by
  have hh : IsPPerfect 2 (W.subgroupOf X) := hW.of_surjective
    (subgroupOfEquivOfLe hWX).symm.toMonoidHom (subgroupOfEquivOfLe hWX).symm.surjective
  let f := (QuotientGroup.mk' (center X)).comp (W.subgroupOf X).subtype
  have he : f.range = centerFactor X W := by
    rw [MonoidHom.range_comp, range_subtype]
    rfl
  exact (hh.of_surjective f.rangeRestrict f.rangeRestrict_surjective).of_surjective
    (MulEquiv.subgroupCongr he).toMonoidHom (MulEquiv.subgroupCongr he).surjective

omit [Finite G] in
/-- The cardinality of the quotient image divides that of its source subgroup. -/
theorem centerFactor_card_dvd {X W : Subgroup G} (hWX : W ≤ X) :
    Nat.card (centerFactor X W) ∣ Nat.card W := by
  have he := Nat.card_congr (subgroupOfEquivOfLe hWX).toEquiv
  exact he ▸ (W.subgroupOf X).card_map_dvd (QuotientGroup.mk' (center X))

omit [Finite G] in
/-- Conjugation by a normalizer of X induces an equivalence of the actual
quotient factors, with the quotient action specified pointwise. -/
theorem centerFactor_conjBy_equiv {X W : Subgroup G} (hWX : W ≤ X)
    {t : G} (ht : t ∈ normalizer X) :
    ∃ e : centerFactor X W ≃* centerFactor X (W.conjBy t),
      ∀ a, (e a : X ⧸ center X) =
        quotientAut (center X) (X.normalizerMonoidHom ⟨t, ht⟩) a := by
  let α := X.normalizerMonoidHom ⟨t, ht⟩
  let β := quotientAut (center X) α
  have hWtX : W.conjBy t ≤ X := by
    have hh := map_mono (f := (MulAut.conj t).toMonoidHom) hWX
    have htX : X.map (MulAut.conj t).toMonoidHom = X := mem_normalizer_iff_map_conj_eq.mp ht
    rwa [htX] at hh
  have hs : (W.subgroupOf X).map α.toMonoidHom = (W.conjBy t).subgroupOf X := by
    apply map_injective X.subtype_injective
    rw [map_map, map_subgroupOf_eq_of_le hWtX]
    change (W.subgroupOf X).map ((MulAut.conj t).toMonoidHom.comp X.subtype) = _
    rw [← map_map, map_subgroupOf_eq_of_le hWX]
    rfl
  have hh : (centerFactor X W).map β.toMonoidHom = centerFactor X (W.conjBy t) := by
    unfold centerFactor
    rw [map_map, ← hs, map_map]
    congr 1
    ext x
    exact quotientAut_apply_mk (center X) α x
  refine ⟨((centerFactor X W).equivMapOfInjective β.toMonoidHom β.injective).trans
    (MulEquiv.subgroupCongr hh), fun a => ?_⟩
  rfl

/-- The first residual quotient factor is directly indecomposable. -/
theorem BinaryBlockEmbedding.centerFactor_directlyIndecomposable {p : ℕ}
    {T X P L₀ M H₀ K : Subgroup G}
    (h : BinaryBlockEmbedding p T X P H₀ K) (hc : Configuration p T X P L₀ M)
    (h114 : HOver G (T : Set G) ⊆ He G) :
    DirectlyIndecomposable (centerFactor X (blockResidual X K)) := by
  have hWX := (blockResidual_le X K).trans inf_le_left
  obtain ⟨n, hn⟩ := h.blockResidual_card_dvd
  exact indecomposable_of_card_dvd hc.prime hc.odd
    (centerFactor_isPPerfect hWX (blockResidual_isPPerfect X K))
    (h.centerFactor_nontrivial hc h114) ((centerFactor_card_dvd hWX).trans hn)

/-- Both quotient factors are directly indecomposable for every normalizer of X. -/
theorem BinaryBlockEmbedding.centerFactors_directlyIndecomposable {p : ℕ}
    {T X P L₀ M H₀ K : Subgroup G}
    (h : BinaryBlockEmbedding p T X P H₀ K) (hc : Configuration p T X P L₀ M)
    (h114 : HOver G (T : Set G) ⊆ He G) {t : G} (ht : t ∈ normalizer X) :
    DirectlyIndecomposable (centerFactor X (blockResidual X K)) ∧
      DirectlyIndecomposable (centerFactor X ((blockResidual X K).conjBy t)) := by
  have hWX := (blockResidual_le X K).trans inf_le_left
  obtain ⟨e, _⟩ := centerFactor_conjBy_equiv hWX ht
  let _ := h.centerFactor_nontrivial hc h114
  have hn : Nontrivial (centerFactor X ((blockResidual X K).conjBy t)) :=
    e.injective.nontrivial
  obtain ⟨n, hd⟩ := h.blockResidual_card_dvd
  have hc' : Nat.card (centerFactor X ((blockResidual X K).conjBy t)) ∣ 2 ^ n * p := by
    rw [← Nat.card_congr e.toEquiv]
    exact (centerFactor_card_dvd hWX).trans hd
  exact ⟨h.centerFactor_directlyIndecomposable hc h114,
    indecomposable_of_card_dvd hc.prime hc.odd
      ((centerFactor_isPPerfect hWX (blockResidual_isPPerfect X K)).of_surjective
        e.toMonoidHom e.surjective) hn hc'⟩

/-- The exact moving-element setup of the binary branch of 1.3.8 supplies
both indecomposable factors for the parent's A.1.15 application. -/
theorem BinaryBlockEmbedding.centerFactors_directlyIndecomposable_of_source
    (T : Sylow 2 G) {p : ℕ} {X P L₀ M H₀ K : Subgroup G}
    (h : BinaryBlockEmbedding p T X P H₀ K) (hc : Configuration p T X P L₀ M)
    (_hH : H₀ ∈ HOver G (T : Set G)) (h114 : HOver G (T : Set G) ⊆ He G)
    {t : G} (ht : t ∈ (T : Subgroup G) ⊓ normalizer P) (_htn : t ∉ normalizer K) :
    DirectlyIndecomposable (centerFactor X (blockResidual X K)) ∧
      DirectlyIndecomposable (centerFactor X ((blockResidual X K).conjBy t)) :=
  h.centerFactors_directlyIndecomposable hc h114 (h.local_input.invariant ht.1)

end CFSG.Quasithin.Chapter1.RadicalExclusions
