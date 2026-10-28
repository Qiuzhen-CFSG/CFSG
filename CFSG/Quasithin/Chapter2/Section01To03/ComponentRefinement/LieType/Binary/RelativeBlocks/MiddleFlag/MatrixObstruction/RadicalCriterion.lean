module

public import CFSG.Quasithin.ChapterC.Section01.BlockBasics
public import Theory.GroupTheory.PResidual.SubnormalCoreAction
public import Theory.GroupTheory.PPerfectHom
public import Mathlib.GroupTheory.Commutator.Finite

/-!
# A radical-pair obstruction to short subnormal groups

For a subnormal embedded short group D, coprime commutator idempotence and
irreducibility force the image of U(D) into every self-centralizing normal
two-subgroup. For two abelian such subgroups R and S with
R ∩ S ≤ [R,S], the three-subgroup lemma then forces [R,D] = 1.
Self-centralization would put D in the two-group R, contradicting O²(D) = D
and the nonzero irreducible module.

The proof keeps the original domain D. Only its core commutator is
transported through the injective map; no closure of short groups under
homomorphic images or later block-structure result is used.

Source: the C.1.7 clauses and the local exclusion in Aschbacher–Smith
2.3.9(7), printed pp.123 and 525–526.
-/

public section

open Subgroup Theory.GroupTheory
open scoped commutatorElement
namespace CFSG.Quasithin.ChapterC

variable {D A : Type*} [Group D] [Group A]

private theorem blockU_map_injective (f : D →* A) (hf : Function.Injective f) :
    (blockU D).map f = (blockU f.range).map f.range.subtype := by
  let e : D ≃* f.range := MonoidHom.ofInjective hf
  have ht : (⊤ : Subgroup D).map e.toMonoidHom = ⊤ := by
    rw [← MonoidHom.range_eq_map, MonoidHom.range_eq_top]
    exact e.surjective
  have he : (blockU D).map e.toMonoidHom = blockU f.range := by
    rw [blockU, map_commutator, pCore_map_iso, ht]
    rfl
  rw [← he, map_map]
  rfl

private theorem IsShort.blockU_idempotent (h : IsShort D) :
    ⁅blockU D, (⊤ : Subgroup D)⁆ = blockU D := by
  let := h.finite
  have ht : IsPPerfect 2 (⊤ : Subgroup D) :=
    h.twoPerfect.of_surjective (topEquiv : (⊤ : Subgroup D) ≃* D).symm.toMonoidHom
      (topEquiv : (⊤ : Subgroup D) ≃* D).symm.surjective
  exact commutator_isPPerfect_idempotent _ _ ht pCore_isPGroup le_normalizer_of_normal

private theorem IsShort.range_not_le_two (h : IsShort D) (f : D →* A)
    (hf : Function.Injective f) (R : Subgroup A) (hp : IsPGroup 2 R) :
    ¬ f.range ≤ R := by
  intro hle
  let g : D →* R := f.codRestrict R (fun d => hle ⟨d, rfl⟩)
  have hg := h.twoPerfect.hom_eq_one_of_isPGroup hp g
  have hone (d : D) : d = 1 := by
    apply hf
    have hh := congrArg (fun q : R => (q : A)) (DFunLike.congr_fun hg d)
    simpa only [g, MonoidHom.codRestrict_apply, MonoidHom.one_apply, Subgroup.coe_one,
      map_one] using hh
  apply h.blockU_ne_bot
  exact le_bot_iff.mp (fun d _ => (mem_bot.mpr (hone d)))

private theorem IsShort.blockU_map_le_selfCentralizing [Finite A] (h : IsShort D)
    (f : D →* A) (hf : Function.Injective f) (hs : f.range.IsSubnormal)
    (R : Subgroup A) [R.Normal] (hp : IsPGroup 2 R)
    (hc : centralizer (R : Set A) ≤ R) : (blockU D).map f ≤ R := by
  let := h.finite
  let B := f.range
  have hb : IsPPerfect 2 B :=
    h.twoPerfect.of_surjective f.rangeRestrict f.rangeRestrict_surjective
  have hcb : ⁅R, B⁆ ≤ (blockU D).map f := by
    rw [blockU_map_injective f hf]
    exact commutator_le_core_commutator_of_isSubnormal B R hs hb hp
      le_normalizer_of_normal
  have hcr : ⁅R, B⁆ ≤ R := commutator_le_left _ _
  let N : Subgroup D := (blockU D ⊓ R.comap f) ⊔ (blockU D ⊓ center D)
  have hN : N ≤ blockU D := sup_le inf_le_left inf_le_left
  rcases h.irreducible.2 N inferInstance le_sup_right hN with hsmall | hbig
  · have hz : ⁅R, B⁆ ≤ (center D).map f := by
      intro x hx
      obtain ⟨d, hd, rfl⟩ := hcb hx
      apply mem_map_of_mem
      have hdN : d ∈ N := mem_sup_left ⟨hd, hcr hx⟩
      rw [hsmall] at hdN
      exact hdN.2
    have hzcomm : ⁅(center D).map f, B⁆ = ⊥ := by
      change ⁅(center D).map f, f.range⁆ = ⊥
      rw [MonoidHom.range_eq_map, ← map_commutator, commutator_center_left, Subgroup.map_bot]
    have hc0 : ⁅R, B⁆ = ⊥ := by
      rw [← commutator_isPPerfect_idempotent B R hb hp le_normalizer_of_normal]
      exact le_bot_iff.mp ((commutator_mono hz le_rfl).trans hzcomm.le)
    have hBR : B ≤ R := by
      apply le_trans _ hc
      apply commutator_eq_bot_iff_le_centralizer.mp
      rw [commutator_comm, hc0]
    exact False.elim (h.range_not_le_two f hf R hp hBR)
  · apply map_le_iff_le_comap.mpr
    have hu : blockU D ≤ R.comap f ⊔ center D := by
      rw [← hbig]
      exact sup_le (inf_le_right.trans le_sup_left) (inf_le_right.trans le_sup_right)
    rw [← h.blockU_idempotent]
    apply commutator_le.mpr
    intro u hu' d _
    obtain ⟨r, hr, z, hz, rfl⟩ := mem_sup_of_normal_right.mp (hu hu')
    have hzd : ⁅z, d⁆ = 1 := by
      apply commutatorElement_eq_one_iff_mul_comm.mpr
      exact (mem_center_iff.mp hz d).symm
    rw [commutatorElement_mul_left_eq_conj_mul, hzd, mul_one, mul_inv_cancel, one_mul]
    exact commutator_le_left (R.comap f) ⊤ (commutator_mem_commutator hr (mem_top d))

/-- Two abelian self-centralizing normal radicals exclude short subnormal embeddings. -/
theorem not_isShort_of_radical_pair [Finite A]
    (R S : Subgroup A) [R.Normal] [S.Normal]
    (hpR : IsPGroup 2 R) (hpS : IsPGroup 2 S)
    (haR : ⁅R, R⁆ = ⊥) (haS : ⁅S, S⁆ = ⊥)
    (hcR : centralizer (R : Set A) ≤ R) (hcS : centralizer (S : Set A) ≤ S)
    (hRS : R ⊓ S ≤ ⁅R, S⁆)
    (f : D →* A) (hf : Function.Injective f) (hs : f.range.IsSubnormal) :
    ¬ IsShort D := by
  intro h
  let B := f.range
  have hb : IsPPerfect 2 B :=
    h.twoPerfect.of_surjective f.rangeRestrict f.rangeRestrict_surjective
  have huR := h.blockU_map_le_selfCentralizing f hf hs R hpR hcR
  have huS := h.blockU_map_le_selfCentralizing f hf hs S hpS hcS
  have hRU : ⁅R, B⁆ ≤ (blockU D).map f := by
    rw [blockU_map_injective f hf]
    exact commutator_le_core_commutator_of_isSubnormal B R hs hb hpR
      le_normalizer_of_normal
  have hSU : ⁅S, B⁆ ≤ (blockU D).map f := by
    rw [blockU_map_injective f hf]
    exact commutator_le_core_commutator_of_isSubnormal B S hs hb hpS
      le_normalizer_of_normal
  have hRSB : ⁅⁅R, S⁆, B⁆ = ⊥ := by
    apply commutator_commutator_eq_bot_of_rotate
    · exact le_bot_iff.mp ((commutator_mono (hSU.trans huR) le_rfl).trans haR.le)
    · rw [commutator_comm B R]
      exact le_bot_iff.mp ((commutator_mono (hRU.trans huS) le_rfl).trans haS.le)
  have hRB : ⁅R, B⁆ = ⊥ := by
    rw [← commutator_isPPerfect_idempotent B R hb hpR le_normalizer_of_normal]
    exact le_bot_iff.mp ((commutator_mono
      ((le_inf (hRU.trans huR) (hRU.trans huS)).trans hRS) le_rfl).trans hRSB.le)
  apply h.range_not_le_two f hf R hpR
  apply le_trans _ hcR
  apply commutator_eq_bot_iff_le_centralizer.mp
  rwa [commutator_comm]

/-- The radical-pair obstruction persists in every finite direct power. -/
theorem not_isShort_of_radical_pair_power [Finite A]
    (R S : Subgroup A) [R.Normal] [S.Normal]
    (hpR : IsPGroup 2 R) (hpS : IsPGroup 2 S)
    (haR : ⁅R, R⁆ = ⊥) (haS : ⁅S, S⁆ = ⊥)
    (hcR : centralizer (R : Set A) ≤ R) (hcS : centralizer (S : Set A) ≤ S)
    (hRS : R ⊓ S ≤ ⁅R, S⁆) (k : ℕ)
    (f : D →* (Fin k → A)) (hf : Function.Injective f) (hs : f.range.IsSubnormal) :
    ¬ IsShort D := by
  classical
  let P (T : Subgroup A) : Subgroup (Fin k → A) := pi Set.univ (fun _ => T)
  have pn (T : Subgroup A) [T.Normal] : (P T).Normal := by
    constructor
    intro g hg a i _
    exact (inferInstance : T.Normal).conj_mem _ (hg i (Set.mem_univ i)) (a i)
  let : (P R).Normal := pn R
  let : (P S).Normal := pn S
  have pp (T : Subgroup A) (hp : IsPGroup 2 T) : IsPGroup 2 (P T) := by
    intro g
    choose n hn using fun i : Fin k => hp (⟨(g : Fin k → A) i, g.property i (Set.mem_univ i)⟩ : T)
    refine ⟨∑ i, n i, ?_⟩
    apply Subtype.ext
    funext i
    have hi : (g : Fin k → A) i ^ (2 ^ n i) = 1 := congrArg Subtype.val (hn i)
    apply orderOf_dvd_iff_pow_eq_one.mp
    exact (orderOf_dvd_of_pow_eq_one hi).trans (pow_dvd_pow 2
      (Finset.single_le_sum (fun j _ => Nat.zero_le (n j)) (Finset.mem_univ i)))
  have pa (T : Subgroup A) (ha : ⁅T, T⁆ = ⊥) : ⁅P T, P T⁆ = ⊥ := by
    dsimp only [P]
    rw [commutator_pi_pi_of_finite]
    simp only [ha, pi_bot]
  have pc (T : Subgroup A) (hc : centralizer (T : Set A) ≤ T) :
      centralizer (P T : Set (Fin k → A)) ≤ P T := by
    intro g hg i _
    apply hc
    rw [mem_centralizer_iff]
    intro t ht
    have hh := mem_centralizer_iff.mp hg (fun _ : Fin k => t) (fun _ _ => ht)
    exact congrFun hh i
  apply not_isShort_of_radical_pair (P R) (P S) (pp R hpR) (pp S hpS)
    (pa R haR) (pa S haS) (pc R hcR) (pc S hcS) _ f hf hs
  dsimp only [P]
  rw [commutator_pi_pi_of_finite]
  intro g hg i hi
  exact hRS ⟨hg.1 i hi, hg.2 i hi⟩

end CFSG.Quasithin.ChapterC
