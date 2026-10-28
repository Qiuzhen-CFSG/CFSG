module

public import CFSG.Quasithin.ChapterE.Section06.Obstructions
public import Theory.GroupTheory.GeneralizedFitting.Defs
public import Theory.GroupTheory.PResidual.Defs


/-!
# Hyperplanes and the dimension bound in E.6

The standing alternatives are exactly E.6.15. An escaping hyperplane forces
`r = 1` and hence `m > 2`, which puts it in the actual obstruction family Γ.
E.6.16(2) uses the earlier characteristic-two conclusion E.6.6(2), stated as
the equality of the intrinsic generalized Fitting subgroup and two-core.

For E.6.17 the E.6.13 nonnormality theorem is an explicit earlier input. If
the automizer has odd order, the Sylow two-subgroup centralizes V, so every
subspace of V is normal in it. An escaping hyperplane contradicts E.6.13.
Thus the automizer has an involution, and rank-nullity for its square-zero
displacement gives `2m ≤ dim V`. The final intersection estimates retain
the actual coranks needed in the subsequent component enlargements.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
manuscript (1 March 2004), E.6.15–17 and the setup of E.6.18, printed
pp.251–252 (PDF pp.262–263). These are conditional proofs with only the
indicated earlier source results explicit; they do not assert E.6.18–23.
-/

public section

open Subgroup Representation.BinaryOffender
open scoped IsMulCommutative

namespace CFSG.Quasithin.ChapterE.Section06.Hyperplanes

variable {G : Type*} [Group G] [Finite G] {V M : Subgroup G}

/-- The source family 𝒰 of codimension-one subspaces of V. -/
@[expose] def IsHyperplane (V W : Subgroup G) : Prop := W ≤ V ∧ subgroupCorank V W = 1

/-- Exactly Hypothesis E.6.15. -/
@[expose] def HypothesisE615 (V : Subgroup G) [IsElementaryAbelian 2 V] : Prop :=
  1 < globalR V ∨ 2 < localM V

/-- Below m, any escaping subspace belongs to the genuine family Γ. -/
theorem small_escape_mem [IsElementaryAbelian 2 V]
    {K : CFSG.Quasithin.GroupClass} {T : Sylow 2 G}
    (h : HypothesisE61 K T M V) {W : Subgroup G}
    (hWV : W ≤ V) (hc : subgroupCorank V W < localM V)
    (he : ¬ centralizer (W : Set G) ≤ M) : W ∈ obstructionFamily M V :=
  ⟨hWV, nontrivial_of_corank_lt_localM hc, he,
    h.oddCentralizerCondition_of_small hWV hc⟩

/-- E.6.16(1): the three consequences of an escaping hyperplane. -/
theorem lemma_E_6_16_1 [IsElementaryAbelian 2 V]
    {K : CFSG.Quasithin.GroupClass} {T : Sylow 2 G}
    (h : HypothesisE61 K T M V) (h15 : HypothesisE615 V)
    {W : Subgroup G} (hW : IsHyperplane V W)
    (he : ¬ centralizer (W : Set G) ≤ M) :
    globalR V = 1 ∧ 2 < localM V ∧ W ∈ obstructionFamily M V := by
  have hr := globalR_eq_one_of_hyperplane h.normalizer_le hW.1 hW.2 he
  have hm : 2 < localM V := h15.resolve_left (by rw [hr]; exact lt_irrefl _)
  exact ⟨hr, hm, small_escape_mem h hW.1 (by rw [hW.2]; omega) he⟩

omit [Finite G] in
/-- An odd automizer kills the actual conjugation action of the Sylow two-subgroup. -/
theorem sylow_centralizes_of_odd_automizer
    {T : Sylow 2 G} (hT : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hodd : Odd (Nat.card (Automizer V))) :
    (T : Subgroup G) ≤ centralizer (V : Set G) := by
  let f : T →* Automizer V :=
    V.normalizerMonoidHom.rangeRestrict.comp (Subgroup.inclusion hT)
  intro t ht
  have hf : f ⟨t, ht⟩ = 1 := by
    obtain ⟨n, hn⟩ := T.isPGroup'.exists_orderOf_dvd_pow (⟨t, ht⟩ : T)
    apply orderOf_eq_one_iff.mp
    exact Nat.eq_one_of_dvd_coprimes ((Nat.coprime_two_left.mpr hodd).pow_left n)
      ((orderOf_map_dvd f _).trans hn) (orderOf_dvd_natCard _)
  have hk : (⟨t, hT ht⟩ : normalizer (V : Set G)) ∈ V.normalizerMonoidHom.ker := by
    exact congrArg (fun a : Automizer V => (a : MulAut V)) hf
  rwa [Subgroup.normalizerMonoidHom_ker] at hk

section Linear
variable {X B : Type*} [Group X] [AddCommGroup B] [Module (ZMod 2) B]
  [FiniteDimensional (ZMod 2) B]

private theorem involution_twice_fixedCodim_le (ρ : Representation (ZMod 2) X B)
    {t : X} (ht : orderOf t = 2) :
    2 * fixedCodim ρ (zpowers t) ≤ Module.finrank (ZMod 2) B := by
  let d : Module.End (ZMod 2) B := ρ t - 1
  have hker : d.ker = fixedSpace ρ (zpowers t) := by
    ext b
    change ρ t b - b = 0 ↔ b ∈ Representation.invariants (ρ.comp (zpowers t).subtype)
    rw [sub_eq_zero]
    exact (Representation.mem_invariants_iff_of_forall_mem_zpowers (ρ.comp (zpowers t).subtype)
      (⟨t, mem_zpowers t⟩ : zpowers t)
      (by
        intro x
        obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp x.property
        exact ⟨i, Subtype.ext hi⟩) b).symm
  have htt (b : B) : ρ t (ρ t b) = b := by
    change (ρ t * ρ t) b = b
    have ht2 : t * t = 1 := by simpa only [ht, pow_two] using pow_orderOf_eq_one t
    rw [← map_mul, ht2, map_one]
    rfl
  have hneg (b : B) : -b = b := by
    have hb : b + b = 0 := by
      calc
        b + b = ((1 : ZMod 2) + 1) • b := by rw [add_smul, one_smul]
        _ = 0 := by rw [show (1 : ZMod 2) + 1 = 0 by decide, zero_smul]
    exact neg_eq_of_add_eq_zero_left hb
  have hr : d.range ≤ d.ker := by
    rintro _ ⟨b, rfl⟩
    change ρ t (ρ t b - b) - (ρ t b - b) = 0
    rw [map_sub, htt]
    calc
      b - ρ t b - (ρ t b - b) = -(ρ t b - b) - (ρ t b - b) := by abel
      _ = 0 := by rw [hneg, sub_self]
  have hdim := Submodule.finrank_mono hr
  have hn := d.finrank_range_add_finrank_ker
  have hc := fixedCodim_add_finrank ρ (zpowers t)
  rw [hker] at hdim hn
  omega
end Linear

/-- E.6.17, with exactly the nonnormality conclusion of E.6.13 as an earlier input. -/
theorem lemma_E_6_17 [IsElementaryAbelian 2 V]
    {K : CFSG.Quasithin.GroupClass} {T : Sylow 2 G}
    (h : HypothesisE61 K T M V) (h15 : HypothesisE615 V)
    (h13 : ∀ U ∈ obstructionFamily M V, ¬ (T : Subgroup G) ≤ normalizer (U : Set G))
    (hr : globalR V = 1) :
    2 < localM V ∧ 6 ≤ Module.finrank (ZMod 2) (Additive V) := by
  have hm : 2 < localM V := h15.resolve_left (by rw [hr]; exact lt_irrefl _)
  refine ⟨hm, ?_⟩
  by_cases hi : ∃ t : Automizer V, orderOf t = 2
  · obtain ⟨t, ht⟩ := hi
    have hlow := moduleM_le_involution (automizerRepresentation V) ht
    have hupp := involution_twice_fixedCodim_le (automizerRepresentation V) ht
    change localM V ≤ _ at hlow
    omega
  · have hodd : Odd (Nat.card (Automizer V)) := by
      by_contra hn
      exact hi (exists_prime_orderOf_dvd_card' 2
        (even_iff_two_dvd.mp (Nat.not_odd_iff_even.mp hn)))
    have hT := sylow_centralizes_of_odd_automizer h.sylow_le_normalizer hodd
    obtain ⟨W, hWV, he, hc⟩ := globalR_attained (by rw [hr]; simp)
    have hc1 : subgroupCorank V W = 1 := by exact_mod_cast hc.trans hr
    have hsmall : subgroupCorank V W < localM V := by omega
    have heM : ¬ centralizer (W : Set G) ≤ M := fun heM =>
      he ((h.centralizer_le_iff (nontrivial_of_corank_lt_localM hsmall) hWV).mp heM)
    have hWG := small_escape_mem h hWV hsmall heM
    exact (h13 W hWG (hT.trans ((Subgroup.centralizer_le hWV).trans
      (Subgroup.centralizer_le_normalizer _)))).elim

/-- E.6.16(2), using E.6.6(2). The residual is O²(F*), not the two-core. -/
theorem lemma_E_6_16_2 [IsElementaryAbelian 2 V]
    {K : CFSG.Quasithin.GroupClass} {T : Sylow 2 G}
    (h : HypothesisE61 K T M V)
    (h6 : ∀ A : Subgroup G, A ≠ ⊥ → A ≤ M → IsPGroup 2 A →
      Theory.GroupTheory.generalizedFitting ↥(M ⊓ centralizer (A : Set G)) =
        pCore 2 ↥(M ⊓ centralizer (A : Set G)))
    {W : Subgroup G} (hWV : W ≤ V)
    (hres : pResidual 2 (Theory.GroupTheory.generalizedFitting (centralizer (W : Set G))) ≠ ⊥) :
    ¬ centralizer (W : Set G) ≤ M := by
  intro hCM
  have hWne : W ≠ ⊥ := by
    intro he
    subst W
    have hM : M = ⊤ := top_unique (by
      intro x _
      apply hCM
      intro y hy
      have hy1 : y = 1 := hy
      simp [hy1])
    let _ := h.simpleQTKE.simple
    exact twoLocal_ne_top_of_nonabelian_simple h.simpleQTKE.nonabelian
      h.maximalTwoLocal.1 hM
  have heq : M ⊓ centralizer (W : Set G) = centralizer (W : Set G) :=
    inf_eq_right.mpr hCM
  have hfg := h6 W hWne (hWV.trans (h.le_sylow.trans h.sylow_le))
    ((IsElementaryAbelian.isPGroup 2 V).to_le hWV)
  rw [heq] at hfg
  have hp : IsPGroup 2 (Theory.GroupTheory.generalizedFitting (centralizer (W : Set G))) := by
    rw [hfg]
    exact pCore_isPGroup
  apply hres
  apply le_bot_iff.mp
  exact sInf_le ⟨inferInstance, hp.of_equiv (QuotientGroup.quotientBot).symm⟩

/-- The corank of an intersection is at most the sum of the coranks. -/
theorem corank_inf_le [IsElementaryAbelian 2 V] (A B : Subgroup G) :
    subgroupCorank V (A ⊓ B) ≤ subgroupCorank V A + subgroupCorank V B := by
  have hi := Subgroup.relIndex_inf_le (H := A) (K := B) (L := V)
  have hpow (U : Subgroup G) : U.relIndex V = 2 ^ subgroupCorank V U := by
    rw [subgroupCorank_eq_quotient_finrank]
    exact Subgroup.relIndex_eq_two_pow_quotient_finrank V U
  rw [hpow, hpow, hpow, ← pow_add] at hi
  exact (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp hi

omit [Finite G] in
/-- Conjugation preserving V also preserves codimension in V. -/
theorem corank_conjugate (V A : Subgroup G) (g : G)
    (hg : g ∈ normalizer (V : Set G)) :
    subgroupCorank V (A.map (MulAut.conj g).toMonoidHom) = subgroupCorank V A := by
  have hV : V.map (MulAut.conj g).toMonoidHom = V := by
    exact (Subgroup.mem_normalizer_iff_map_conj_eq).mp hg
  unfold subgroupCorank
  nth_rw 1 [← hV]
  rw [Subgroup.relIndex_map_map_of_injective _ _ (MulAut.conj g).injective]

/-- The intersection with a conjugate is nonidentity when twice its corank is below dim V. -/
theorem inf_conjugate_ne_bot [IsElementaryAbelian 2 V]
    {A : Subgroup G} (g : G) (hg : g ∈ normalizer (V : Set G))
    (hdim : 2 * subgroupCorank V A < Module.finrank (ZMod 2) (Additive V)) :
    A ⊓ A.map (MulAut.conj g).toMonoidHom ≠ ⊥ := by
  have hi := corank_inf_le (V := V) A (A.map (MulAut.conj g).toMonoidHom)
  rw [corank_conjugate V A g hg] at hi
  intro he
  rw [he, corank_bot] at hi
  omega

end CFSG.Quasithin.ChapterE.Section06.Hyperplanes
