module
public import CFSG.Quasithin.ChapterE.Section03.Offenders.Transport
public import CFSG.Quasithin.ChapterE.Section01.ValuesEvenClassical.LowerObstructions.Sp4.ECaseReduction
public import CFSG.Quasithin.ChapterE.Section05.Generation
public import CFSG.Quasithin.ChapterE.Section01.ParameterReduction.Solvable
public import CFSG.Quasithin.ChapterE.Section01.ParameterReduction.ChiefOrbit.NormalizerDiagonal.Overgroups
public import Theory.GroupTheory.MaximalTwoLocalOvergroups
public import Theory.ElementaryAbelian.Injective
public import Mathlib.GroupTheory.Schreier

/-!
# E.3.35 containment from attained E-generation

Uniqueness over N_G(C_T(V)) controls the normalizer of the zeroth weak
closure. Sylow transport puts the weak closures below w inside the same
centralizer in the relative Sylow subgroup S. For an E-member, each
conjugate of its elementary generator meets O₂(K) in corank at most i.
The bounds i<w and i<r force every such conjugate to centralize V.
E.1.4 and the Sylow supplement then put the whole E-member in M, and
E-generation puts H in M.

The solvable source clause is unconditional, using the proved E.1.13.
The numeric general clause retains positive attainment of n(H): general
E.1.11 existence is a genuine earlier source obligation, not inferred from
the natural-number infimum. Existing source interfaces remain unchanged.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
Lemma E.3.35(1), printed pp.238–239; E.1.4, printed p.210.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterE.SourceContainment
variable {G : Type*} [Group G] [Finite G]

theorem weakClosure_eq_of_centralizer_le {V S : Subgroup G} (T : Sylow 2 G)
    (hS : IsPGroup 2 S) (hQS : (T : Subgroup G) ⊓ centralizer (V : Set G) ≤ S)
    {i : ℕ} (hi : (i : ℕ∞) < globalW V T) :
    indexedWeakClosure V (T : Subgroup G) i = indexedWeakClosure V S i :=
  SubgroupFamily.span_eq_in_p_overgroup (conjugateCorankFamily_invariant V i)
    T S hS ((weakClosure_le_centralizer_of_lt_globalW hi).trans hQS)

theorem normalizer_weakClosure_zero_le {V M : Subgroup G}
    [IsElementaryAbelian 2 V] {T : Sylow 2 G} (hT : HypothesisE322 V T)
    (hw : 0 < globalW V T)
    (hunique : maximalTwoLocalOvergroups (normalizer
      (((T : Subgroup G) ⊓ centralizer (V : Set G) : Subgroup G) : Set G)) = {M}) :
    normalizer (indexedWeakClosure V (T : Subgroup G) 0 : Set G) ≤ M := by
  let Q := (T : Subgroup G) ⊓ centralizer (V : Set G)
  have heq := weakClosure_eq_of_centralizer_le T T.2.to_inf_left
    (show (T : Subgroup G) ⊓ centralizer (V : Set G) ≤ Q from le_rfl) hw
  have hne : indexedWeakClosure V (T : Subgroup G) 0 ≠ ⊥ := by
    intro he
    exact hT.nontrivial (le_bot_iff.mp (he ▸ self_le_weakClosure_zero hT.le_sylow))
  have hp : IsPGroup 2 (indexedWeakClosure V (T : Subgroup G) 0) :=
    T.2.of_injective (Subgroup.inclusion (indexedWeakClosure_le _ _ _))
      (Subgroup.inclusion_injective _)
  have hl : IsTwoLocal (normalizer (indexedWeakClosure V (T : Subgroup G) 0 : Set G)) :=
    ⟨_, hne, hp, rfl⟩
  obtain ⟨N, hWN, hN⟩ := Finite.exists_le_maximal hl
  have hQN : normalizer (Q : Set G) ≤ N := by
    apply le_trans _ hWN
    rw [heq]
    exact normalizer_le_weakClosure_normalizer V Q 0
  have hNM : N = M := by
    have hm : N ∈ maximalTwoLocalOvergroups (normalizer (Q : Set G)) := ⟨hN, hQN⟩
    rw [hunique] at hm
    exact Set.mem_singleton_iff.mp hm
  exact hNM ▸ hWN

theorem conjugate_centralizes_of_small_corank {V S B : Subgroup G}
    [IsElementaryAbelian 2 V] {T : Sylow 2 G} (hT : HypothesisE322 V T)
    (hS : IsPGroup 2 S) (hQS : (T : Subgroup G) ⊓ centralizer (V : Set G) ≤ S)
    (g : G) (hBV : B ≤ V.map (MulAut.conj g).toMonoidHom) (hBS : B ≤ S)
    (hw : (subgroupCorank (V.map (MulAut.conj g).toMonoidHom) B : ℕ∞) < globalW V T)
    (hr : (subgroupCorank (V.map (MulAut.conj g).toMonoidHom) B : ℕ∞) < globalR V) :
    V.map (MulAut.conj g).toMonoidHom ≤ centralizer (V : Set G) := by
  let A := V.map (MulAut.conj g).toMonoidHom
  let _ : IsElementaryAbelian 2 A := IsElementaryAbelian.map _
  have hgamma : B ∈ gamma V S (subgroupCorank A B) := by
    refine ⟨⟨g, hBV, ?_⟩, hBS⟩
    rw [Subgroup.relIndex_eq_two_pow_quotient_finrank,
      subgroupCorank_eq_quotient_finrank]
  have hBC : B ≤ centralizer (V : Set G) := by
    have he := weakClosure_eq_of_centralizer_le T hS hQS hw
    exact (gamma_le_weakClosure hgamma).trans
      (he ▸ (weakClosure_le_centralizer_of_lt_globalW hw).trans inf_le_right)
  have hVN : V ≤ normalizer (A : Set G) := by
    apply (le_centralizer_iff.mp hBC).trans
    apply centralizer_le_normalizer_of_corank_lt_globalR hBV
    simpa only [A, globalR_map_equiv] using hr
  exact (lemma_E_3_25 hT (lt_of_le_of_lt bot_le hw) g).2.1.mpr
    ((lemma_E_3_25 hT (lt_of_le_of_lt bot_le hw) g).2.2.mpr hVN)

theorem core_corank_le {K : Type*} [Group K] [Finite K]
    (A : Subgroup K) [IsElementaryAbelian 2 A] {i : ℕ}
    (hr : Group.rank (A.map (QuotientGroup.mk' (pCore 2 K))) ≤ i) :
    subgroupCorank A (A ⊓ pCore 2 K) ≤ i := by
  let a := A.map (QuotientGroup.mk' (pCore 2 K))
  let _ : IsElementaryAbelian 2 a := IsElementaryAbelian.map _
  let _ : CommGroup a := IsMulCommutative.instCommGroup
  have hdvd : Nat.card a ∣ 2 ^ Group.rank a := card_dvd_exponent_pow_rank' a
    (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p 2 a))
  have hc : Nat.card a ≤ 2 ^ i := (Nat.le_of_dvd (by positivity) hdvd).trans
    (Nat.pow_le_pow_right (by decide) hr)
  have hindex : (pCore 2 K).relIndex A = Nat.card a := by
    simpa only [QuotientGroup.ker_mk'] using relIndex_ker A (QuotientGroup.mk' (pCore 2 K))
  change Nat.log 2 ((A ⊓ pCore 2 K).relIndex A) ≤ i
  rw [inf_relIndex_left, hindex]
  simpa only [Nat.log_pow (by decide : 1 < 2)] using Nat.log_mono_right (b := 2) hc

theorem normalClosure_centralizes {V S : Subgroup G} [IsElementaryAbelian 2 V]
    {T : Sylow 2 G} (hT : HypothesisE322 V T)
    (hS : IsPGroup 2 S) (hQS : (T : Subgroup G) ⊓ centralizer (V : Set G) ≤ S)
    {K : Type*} [Group K] [Finite K] (A : Subgroup K) [IsElementaryAbelian 2 A]
    (f : K →* G) (hf : Function.Injective f) (g : G)
    (hAg : A.map f = V.map (MulAut.conj g).toMonoidHom)
    (hcore : (pCore 2 K).map f ≤ S) {i : ℕ}
    (hrank : Group.rank (A.map (QuotientGroup.mk' (pCore 2 K))) ≤ i)
    (hw : (i : ℕ∞) < globalW V T) (hr : (i : ℕ∞) < globalR V) :
    (normalClosure (A : Set K)).map f ≤ centralizer (V : Set G) := by
  have hi := core_corank_le A hrank
  have hconj (k : K) :
      (A.map (f.comp (MulAut.conj k).toMonoidHom)) ≤ centralizer (V : Set G) := by
    let f' := f.comp (MulAut.conj k).toMonoidHom
    have hinj : Function.Injective f' := hf.comp (MulAut.conj k).injective
    have he : A.map f' = V.map (MulAut.conj (f k * g)).toMonoidHom := by
      have hcomp : f' = (MulAut.conj (f k)).toMonoidHom.comp f := by ext x; simp [f']
      rw [hcomp, ← map_map, hAg, map_map]
      congr 1
      ext x
      simp [mul_assoc]
    have hBC : ((A ⊓ pCore 2 K).map f') ≤ S := by
      apply le_trans _ hcore
      rintro x ⟨a, ha, rfl⟩
      exact mem_map_of_mem f ((inferInstance : (pCore 2 K).Normal).conj_mem a ha.2 k)
    have hb : subgroupCorank (V.map (MulAut.conj (f k * g)).toMonoidHom)
        ((A ⊓ pCore 2 K).map f') ≤ i := by
      rw [← he, subgroupCorank, relIndex_map_map_of_injective _ _ hinj]
      exact hi
    rw [he]
    apply conjugate_centralizes_of_small_corank hT hS hQS (f k * g)
      (he ▸ map_mono inf_le_left) hBC
    · exact lt_of_le_of_lt (by exact_mod_cast hb) hw
    · exact lt_of_le_of_lt (by exact_mod_cast hb) hr
  apply map_le_iff_le_comap.mpr
  change Subgroup.closure (Group.conjugatesOfSet (A : Set K)) ≤ _
  apply (Subgroup.closure_le _).mpr
  intro x hx
  obtain ⟨a, ha, hax⟩ := Group.mem_conjugatesOfSet_iff.mp hx
  obtain ⟨k, rfl⟩ := isConj_iff.mp hax
  exact hconj k (mem_map_of_mem _ ha)


theorem le_of_isEGenerated {V M H : Subgroup G} [IsElementaryAbelian 2 V]
    {T : Sylow 2 G} (hT : HypothesisE322 V T) (S : Sylow 2 H) {i : ℕ}
    (hgen : IsEGeneratedAt i S)
    (hunique : maximalTwoLocalOvergroups (normalizer
      (((T : Subgroup G) ⊓ centralizer (V : Set G) : Subgroup G) : Set G)) = {M})
    (hCV : H ⊓ centralizer (V : Set G) ≤ M)
    (hQS : (T : Subgroup G) ⊓ centralizer (V : Set G) ≤ (S : Subgroup H).map H.subtype)
    (hw : (i : ℕ∞) < globalW V T) (hr : (i : ℕ∞) < globalR V) : H ≤ M := by
  let Ω := conjugateCorankFamily V 0
  have hΩ : IsElementaryFamily Ω := by
    constructor
    · rintro A ⟨g, hAV, hi⟩
      let _ : IsElementaryAbelian 2 (V.map (MulAut.conj g).toMonoidHom) := IsElementaryAbelian.map _
      exact IsElementaryAbelian.of_injective (Subgroup.inclusion hAV) (Subgroup.inclusion_injective _)
    · intro g A hA
      exact conjugateCorankFamily_invariant V 0 A hA g
  let ΩH := ChiefOrbit.restrictedFamily H Ω
  have hΩH : IsElementaryFamily ΩH := ChiefOrbit.restrictedFamily_elementary H hΩ
  let Sg := (S : Subgroup H).map H.subtype
  have hSg : IsPGroup 2 Sg := S.2.map H.subtype
  have hw0 : (0 : ℕ∞) < globalW V T := lt_of_le_of_lt bot_le hw
  have hWS : indexedWeakClosure V (T : Subgroup G) 0 = indexedWeakClosure V Sg 0 :=
    weakClosure_eq_of_centralizer_le T hSg hQS hw0
  have hNM : normalizer (indexedWeakClosure V Sg 0 : Set G) ≤ M := by
    rw [← hWS]
    exact normalizer_weakClosure_zero_le hT hw0 hunique
  have hSM : Sg ≤ M := (Sg.le_normalizer.trans (normalizer_le_weakClosure_normalizer V Sg 0)).trans hNM
  have hSMH : (S : Subgroup H) ≤ M.subgroupOf H := map_le_iff_le_comap.mp hSM
  have hWmap : (weakClosure (S : Subgroup H) ΩH).map H.subtype = indexedWeakClosure V Sg 0 := by
    have he := ChiefOrbit.map_weakClosure_restrictedFamily Sg H (map_subtype_le _) Ω
    have hsub : Sg.subgroupOf H = (S : Subgroup H) := by
      change ((S : Subgroup H).map H.subtype).comap H.subtype = (S : Subgroup H)
      rw [comap_map_eq_self_of_injective H.subtype_injective]
    rwa [hsub] at he
  have hN : normalizer (weakClosure (S : Subgroup H) ΩH : Set H) ≤ M.subgroupOf H := by
    apply map_le_iff_le_comap.mp
    apply le_trans (Subgroup.le_normalizer_map H.subtype)
    rw [hWmap]
    exact hNM
  have hE : eFamilySubgroup i (S : Subgroup H) ΩH ≤ M.subgroupOf H := by
    apply iSup_le
    intro A
    apply sSup_le
    intro K hK
    have hA := A.property.1
    have hAS : A.val.map H.subtype ≤ Sg := map_mono A.property.2
    obtain ⟨g, hAg, _⟩ := (mem_gamma_zero_iff V Sg (A.val.map H.subtype)).mp ⟨hA, hAS⟩
    let AK := A.val.subgroupOf K
    let _ : IsElementaryAbelian 2 A.val := hK.1.1
    let _ : IsElementaryAbelian 2 AK := IsElementaryAbelian.subgroupOf hK.1.2.2.1
    let f := H.subtype.comp K.subtype
    have hf : Function.Injective f := H.subtype_injective.comp K.subtype_injective
    have heA : AK.map f = V.map (MulAut.conj g).toMonoidHom := by
      rw [← map_map, map_subgroupOf_eq_of_le hK.1.2.2.1]
      exact hAg
    have hcore : (pCore 2 K).map f ≤ Sg := by
      obtain ⟨U, hU⟩ := hK.1.2.2.2.2.1
      have hcu := map_mono (f := K.subtype) (pCore_isPGroup.le_sylow_of_normal U)
      rw [hU, subgroupOf_map_subtype] at hcu
      change (pCore 2 K).map (H.subtype.comp K.subtype) ≤ Sg
      rw [← map_map]
      exact map_mono (hcu.trans inf_le_left)
    have hNC := normalClosure_centralizes hT hSg hQS AK f hf g heA hcore
      (ValuesEvenClassical.Sp4Lower.member_core_rank_le hK) hw hr
    have hRC : (pResidual 2 K).map f ≤ centralizer (V : Set G) :=
      (map_mono hK.1.residual_le_normalClosure).trans hNC
    apply hK.1.le_of_residual_le hSMH
    rintro x ⟨k, hk, rfl⟩
    exact hCV ⟨k.val.property, hRC (mem_map_of_mem f hk)⟩
  have htop : (⊤ : Subgroup H) ≤ M.subgroupOf H := by
    rw [← hgen ΩH hΩH]
    exact sup_le hE hN
  intro x hx
  exact htop (show (⟨x, hx⟩ : H) ∈ (⊤ : Subgroup H) from mem_top _)

/-- The original numerical implication once the minimum is known to be attained.
General existence must still be proved by E.1.11 or a concrete source witness. -/
theorem le_of_generationParameter_pos {V M H : Subgroup G} [IsElementaryAbelian 2 V]
    {T : Sylow 2 G} (hT : HypothesisE322 V T) (S : Sylow 2 H)
    (hunique : maximalTwoLocalOvergroups (normalizer
      (((T : Subgroup G) ⊓ centralizer (V : Set G) : Subgroup G) : Set G)) = {M})
    (hCV : H ⊓ centralizer (V : Set G) ≤ M)
    (hQS : (T : Subgroup G) ⊓ centralizer (V : Set G) ≤ (S : Subgroup H).map H.subtype)
    (hpos : 0 < generationParameter H)
    (hn : (generationParameter H : ℕ∞) < min (globalW V T) (globalR V)) : H ≤ M :=
  le_of_isEGenerated hT S (isEGenerated_generationParameter_of_pos hpos S)
    hunique hCV hQS (lt_min_iff.mp hn).1 (lt_min_iff.mp hn).2

/-- The complete solvable clause of source E.3.35(1), with no attainment premise. -/
theorem le_of_solvable {V M H : Subgroup G} [IsElementaryAbelian 2 V]
    [Group.IsSolvable H] {T : Sylow 2 G} (hT : HypothesisE322 V T) (S : Sylow 2 H)
    (hunique : maximalTwoLocalOvergroups (normalizer
      (((T : Subgroup G) ⊓ centralizer (V : Set G) : Subgroup G) : Set G)) = {M})
    (hCV : H ⊓ centralizer (V : Set G) ≤ M)
    (hQS : (T : Subgroup G) ⊓ centralizer (V : Set G) ≤ (S : Subgroup H).map H.subtype)
    (hwr : (1 : ℕ∞) < min (globalW V T) (globalR V)) : H ≤ M :=
  le_of_isEGenerated hT S (isEGenerated_one_of_solvable S)
    hunique hCV hQS (lt_min_iff.mp hwr).1 (lt_min_iff.mp hwr).2

end CFSG.Quasithin.ChapterE.SourceContainment
