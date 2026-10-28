module

public import CFSG.Quasithin.Chapter3.Section01.LocalGeometry
public import CFSG.Quasithin.Chapter8.Section02.Normalizer.ParabolicReduction.ResidualLift
public import Theory.GroupTheory.PCoreQuotientJoinAction
public import Theory.GroupTheory.PrimeRankResidualCentralizer

/-!
# Common deductions for the rank sieve in Lemma 8.2.9

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
manuscript (1 March 2004), printed p.720 (PDF p.737).

Minimality in the literal HStar family gives H = ⟨I,T⟩. The conclusion
8.2.8(2), together with I ≤ C_G(U), then makes O²(H) act trivially on
L_U/O₂(L_U), for L_U = N_L(U)^∞. The rank deductions use this actual
quotient, with a marked model and an explicitly checked centre convention.
They allow a cubic centre; they never treat a triple cover as centreless.

For B = V ∩ O₂(I), normality of O₂(H) gives V ∩ O₂(H) ≤ B. Multiplication
of relative indices then gives the order-two/order-four alternatives for
V⁺. Odd divisors of |I/O₂(I)| pass to the literal image I⁺ in H/O₂(H).
When the quotient residual has prime order, this discharges the cover
premise of ResidualLift and yields its normalizer and code-obstruction
conclusions.

These are common source deductions, not the complete minimal-parabolic
sieve. The Chapter 7 bound on n(H), the code branch’s stronger 3′ conclusion,
the E.2.2/B.6.8 list inspections, the elimination of intersection case (II),
and their marked-model specializations remain to be proved. The unitary
and chief-section exceptions belong to the other 8.2.9 branch owners.
No tensor identity is used here; the corrected cocode scalar convention
in Normalizer/TensorDimension.lean is retained.
-/

public section

open Subgroup
open scoped Pointwise
namespace CFSG.Quasithin.Chapter8.Section02.Normalizer.ParabolicReduction.RankSieve
variable {G : Type*} [Group G]

/-- Minimality of the source HStar member forces H = ⟨I,T⟩ when I escapes M. -/
theorem join_eq_of_minimal_outside (T : Sylow 2 G) (M H I : Subgroup G)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (hIH : I ≤ H) (hIM : ¬ I ≤ M) : I ⊔ (T : Subgroup G) = H := by
  have hTH : (T : Subgroup G) ≤ H := hH.1.1.2
  have hle := sup_le hIH hTH
  by_contra hne
  have hM := Chapter3.HStar.proper_overgroup_le T hH
    (show (T : Subgroup G) ≤ I ⊔ (T : Subgroup G) from le_sup_right)
    (lt_of_le_of_ne hle hne)
  exact hIM (le_sup_left.trans hM)

/-- The generated parabolic normalizes the actual local solvable residual. -/
theorem normalizes_localResidual_of_generation (L H I T U : Subgroup G)
    (hgen : I ⊔ T = H)
    (hIC : I ≤ centralizer (U : Set G))
    (hTL : T ≤ normalizer (L : Set G)) (hTU : T ≤ normalizer (U : Set G))
    (hcomm : ⁅localResidual L U, centralizer (U : Set G)⁆ ≤
      (localResidual L U).pCoreIn 2) :
    H ≤ normalizer (localResidual L U : Set G) := by
  rw [← hgen]
  refine sup_le ?_ (normalizes_localResidual L U T hTL hTU)
  apply hIC.trans
  exact le_normalizer_iff_commutator_le_left.mpr (hcomm.trans (pCoreIn_le 2 _))

/-- The source 8.2.8(2) implies commutation of O²(H) with L_U modulo O₂(L_U). -/
theorem residual_commutator_le_localCore (L H I T U : Subgroup G)
    (hgen : I ⊔ T = H) (hT : IsPGroup 2 T)
    (hIC : I ≤ centralizer (U : Set G)) (hTU : T ≤ normalizer (U : Set G))
    (hcomm : ⁅localResidual L U, centralizer (U : Set G)⁆ ≤
      (localResidual L U).pCoreIn 2) :
    ⁅(pResidual 2 H).map H.subtype, localResidual L U⁆ ≤
      (localResidual L U).pCoreIn 2 := by
  rw [commutator_comm]
  exact (commutator_mono le_rfl
    (residual_centralizes H I T U hgen hT hIC hTU)).trans hcomm

/-- The preceding commutator bound kills the literal quotient conjugation action of O²(H). -/
theorem residual_fixes_localCore_quotient (L H I T U : Subgroup G)
    (hgen : I ⊔ T = H) (hT : IsPGroup 2 T)
    (hIC : I ≤ centralizer (U : Set G))
    (hTL : T ≤ normalizer (L : Set G)) (hTU : T ≤ normalizer (U : Set G))
    (hcomm : ⁅localResidual L U, centralizer (U : Set G)⁆ ≤
      (localResidual L U).pCoreIn 2) :
    pResidual 2 H ≤
      ((pCoreJoinAction 2 (normalizes_localResidual_of_generation L H I T U
        hgen hIC hTL hTU hcomm)).comp (inclusion le_sup_right)).ker := by
  let K := localResidual L U
  have hc := residual_commutator_le_localCore L H I T U hgen hT hIC hTU hcomm
  intro x hx
  apply MulEquiv.ext
  intro y
  obtain ⟨k, rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 K) y
  change pCoreJoinAction 2 (normalizes_localResidual_of_generation L H I T U
    hgen hIC hTL hTU hcomm) (inclusion le_sup_right x)
    (QuotientGroup.mk' (pCore 2 K) k) = QuotientGroup.mk' (pCore 2 K) k
  rw [pCoreJoinAction_mk]
  apply eq_of_mul_inv_eq_one
  rw [← map_inv, ← map_mul]
  apply (QuotientGroup.eq_one_iff _).mpr
  have hh := hc (commutator_mem_commutator
    (show (x : G) ∈ (pResidual 2 H).map H.subtype from ⟨x, hx, rfl⟩) k.property)
  change (x : G) * (k : G) * (x : G)⁻¹ * (k : G)⁻¹ ∈ (pCore 2 K).map K.subtype at hh
  rcases hh with ⟨z, hz, he⟩
  have he' : z =
      K.normalizerMonoidHom (inclusion
        (sup_le K.le_normalizer (normalizes_localResidual_of_generation L H I T U
          hgen hIC hTL hTU hcomm)) (inclusion le_sup_right x)) k * k⁻¹ := by
    apply Subtype.ext
    exact he
  exact he' ▸ hz

variable [Finite G]

/-- A marked local quotient with p-prime centre gives m_p(H) ≤ 1 from m_p(H L_U) ≤ 2. -/
theorem odd_rank_le_one_of_local_model
    (T : Sylow 2 G) (L M H I U : Subgroup G)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (hIH : I ≤ H) (hIM : ¬ I ≤ M)
    (hIC : I ≤ centralizer (U : Set G))
    (hTL : (T : Subgroup G) ≤ normalizer (L : Set G))
    (hTU : (T : Subgroup G) ≤ normalizer (U : Set G))
    (hcomm : ⁅localResidual L U, centralizer (U : Set G)⁆ ≤
      (localResidual L U).pCoreIn 2)
    {p : ℕ} [Fact p.Prime] (ho : Odd p)
    {S : Type*} [Group S] [Finite S]
    (e : (localResidual L U ⧸ pCore 2 (localResidual L U)) ≃* S)
    (hz : Nat.Coprime p (Nat.card (center S))) (hS : 1 ≤ primeRank p S)
    (hjoin : primeRank p (H ⊔ localResidual L U : Subgroup G) ≤ 2) :
    primeRank p H ≤ 1 := by
  have hgen := join_eq_of_minimal_outside T M H I hH hIH hIM
  have hz' : Nat.Coprime p (Nat.card
      (center (localResidual L U ⧸ pCore 2 (localResidual L U)))) := by
    rwa [Nat.card_congr (centerCongr e).toEquiv]
  have hr := Theory.GroupTheory.ResidualCentralizerRank.primeRank_sum_le_of_normalized_factor ho H (localResidual L U)
    (normalizes_localResidual_of_generation L H I T U hgen hIC hTL hTU hcomm)
    (residual_commutator_le_localCore L H I T U hgen T.isPGroup' hIC hTU hcomm) hz'
  have hk : 1 ≤ primeRank p (localResidual L U) := by
    rw [← primeRank_quotient_eq_of_isTwoGroup p ho (pCore 2 (localResidual L U))
      pCore_isPGroup, primeRank_congr p e]
    exact hS
  omega

/-- The three-rank deduction includes the triple-cover row, with its cubic centre retained. -/
theorem three_rank_le_one_of_local_model
    (T : Sylow 2 G) (L M H I U : Subgroup G)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (hIH : I ≤ H) (hIM : ¬ I ≤ M)
    (hIC : I ≤ centralizer (U : Set G))
    (hTL : (T : Subgroup G) ≤ normalizer (L : Set G))
    (hTU : (T : Subgroup G) ≤ normalizer (U : Set G))
    (hcomm : ⁅localResidual L U, centralizer (U : Set G)⁆ ≤
      (localResidual L U).pCoreIn 2)
    {S : Type*} [Group S] [Finite S]
    (e : (localResidual L U ⧸ pCore 2 (localResidual L U)) ≃* S)
    (hS : (Nat.Coprime 3 (Nat.card (center S)) ∧ 1 ≤ primeRank 3 S) ∨
      (Nat.card (center S) ≤ 3 ∧ 2 ≤ primeRank 3 S))
    (hjoin : primeRank 3 (H ⊔ localResidual L U : Subgroup G) ≤ 2) :
    primeRank 3 H ≤ 1 := by
  rcases hS with hS | hS
  · exact odd_rank_le_one_of_local_model T L M H I U hH hIH hIM hIC hTL hTU hcomm
      (by decide) e hS.1 hS.2 hjoin
  have hgen := join_eq_of_minimal_outside T M H I hH hIH hIM
  have hz : Nat.card (center (localResidual L U ⧸ pCore 2 (localResidual L U))) ≤ 3 := by
    rw [Nat.card_congr (centerCongr e).toEquiv]
    exact hS.1
  apply Theory.GroupTheory.ResidualCentralizerRank.three_rank_le_one_of_normalized_factor_cubic_center H (localResidual L U)
    (normalizes_localResidual_of_generation L H I T U hgen hIC hTL hTU hcomm)
    (residual_commutator_le_localCore L H I T U hgen T.isPGroup' hIC hTU hcomm) hz _ hjoin
  rw [← primeRank_quotient_eq_of_isTwoGroup 3 (by decide) (pCore 2 (localResidual L U))
    pCore_isPGroup, primeRank_congr 3 e]
  exact hS.2

omit [Finite G] in
/-- Normality of the ambient two-core places V ∩ O₂(H) inside B = V ∩ O₂(I). -/
theorem intersection_core_le_pair_core (V I : Subgroup G) (hVI : V ≤ I) :
    V ⊓ pCore 2 G ≤ V ⊓ I.pCoreIn 2 := by
  have hq : (pCore 2 G).subgroupOf I ≤ pCore 2 I :=
    le_sSup ⟨inferInstance, pCore_isPGroup.comap_subtype⟩
  intro x hx
  exact ⟨hx.1, ⟨⟨x, hVI hx.1⟩, hq hx.2, rfl⟩⟩

/-- Index two over B and the actual bound on B⁺ give the source intersection alternatives. -/
theorem pair_intersection_alternatives (V I B : Subgroup G) (hVI : V ≤ I)
    (hB : B = V ⊓ I.pCoreIn 2) (hindex : B.relIndex V = 2)
    (hsmall : Nat.card (B.map (QuotientGroup.mk' (pCore 2 G))) ≤ 2) :
    (B = V ⊓ pCore 2 G ∧ Nat.card (V.map (QuotientGroup.mk' (pCore 2 G))) = 2) ∨
      Nat.card (V.map (QuotientGroup.mk' (pCore 2 G))) = 4 := by
  have hBV : B ≤ V := hB ▸ inf_le_left
  have hVB : V ⊓ pCore 2 G ≤ B := hB ▸ intersection_core_le_pair_core V I hVI
  have hQB : pCore 2 G ⊓ B = pCore 2 G ⊓ V := by
    apply le_antisymm (inf_le_inf_left _ hBV)
    exact le_inf inf_le_left (inf_comm V (pCore 2 G) ▸ hVB)
  have he := relIndex_inf_mul_relIndex (pCore 2 G) B V
  rw [inf_eq_left.mpr hBV, hindex, hQB, inf_relIndex_right] at he
  have hc (A : Subgroup G) : (pCore 2 G).relIndex A =
      Nat.card (A.map (QuotientGroup.mk' (pCore 2 G))) := by
    simpa only [QuotientGroup.ker_mk'] using
      (relIndex_ker (K := A) (QuotientGroup.mk' (pCore 2 G)))
  rw [hc B, hc V] at he
  have hpos : 0 < Nat.card (B.map (QuotientGroup.mk' (pCore 2 G))) := Nat.card_pos
  by_cases hb : Nat.card (B.map (QuotientGroup.mk' (pCore 2 G))) = 1
  · left
    have hBQ : B ≤ pCore 2 G := relIndex_eq_one.mp ((hc B).trans hb)
    exact ⟨le_antisymm (le_inf hBV hBQ) hVB, by omega⟩
  · right
    omega

/-- Quotienting by O₂(H) preserves every odd prime divisor of the actual subgroup I. -/
theorem odd_divisor_image_twoCore_iff (I : Subgroup G) {p : ℕ}
    (hp : p.Prime) (ho : p ≠ 2) :
    p ∣ Nat.card (I.map (QuotientGroup.mk' (pCore 2 G))) ↔ p ∣ Nat.card I := by
  let f := (QuotientGroup.mk' (pCore 2 G)).subgroupMap I
  have hf : Function.Surjective f := MonoidHom.subgroupMap_surjective _ _
  have hk : IsPGroup 2 f.ker := by
    rw [show f = (QuotientGroup.mk' (pCore 2 G)).subgroupMap I from rfl,
      ker_subgroupMap, QuotientGroup.ker_mk']
    exact pCore_isPGroup.comap_subtype
  have hc : Nat.Coprime p (Nat.card f.ker) := by
    obtain ⟨n, hn⟩ := hk.exists_card_eq
    rw [hn]
    exact (hp.coprime_iff_not_dvd.mpr (by
      intro h
      exact ho ((Nat.dvd_prime Nat.prime_two).mp h |>.resolve_left hp.ne_one))).pow_right n
  constructor
  · exact fun hd => hd.trans (card_dvd_of_surjective f hf)
  · intro hd
    have he : Nat.card f.ker * Nat.card (I.map (QuotientGroup.mk' (pCore 2 G))) =
        Nat.card I := by
      simpa only [index_ker, f.range_eq_top_of_surjective hf,
        Nat.card_congr Subgroup.topEquiv.toEquiv] using f.ker.card_mul_index
    rw [← he] at hd
    exact hc.dvd_of_dvd_mul_left hd

/-- An odd divisor of the intrinsic I/O₂(I) supplies the literal prime-residual quotient cover. -/
theorem quotient_cover_of_prime_residual_of_intrinsic_divisor
    (I : Subgroup G) {p : ℕ} (hp : p.Prime) (ho : p ≠ 2)
    (hr : (Nat.card (pResidual 2 (G ⧸ pCore 2 G))).Prime)
    (hdiv : p ∣ Nat.card (I ⧸ pCore 2 I)) :
    pResidual 2 (G ⧸ pCore 2 G) ≤ I.map (QuotientGroup.mk' (pCore 2 G)) := by
  apply quotient_cover_of_prime_residual I hp ho hr
  apply (odd_divisor_image_twoCore_iff I hp ho).mpr
  exact hdiv.trans (card_dvd_of_surjective (QuotientGroup.mk' (pCore 2 I))
    (QuotientGroup.mk'_surjective _))

/-- The prime-order code alternative contradicts 8.2.8(6), with its odd divisor transported. -/
theorem code_obstruction_of_prime_sieve
    (T : Sylow 2 G) (V I : Subgroup G) (h : G)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hgen : V ⊔ V.map (MulAut.conj h⁻¹).toMonoidHom = I)
    (hr : (Nat.card (pResidual 2 (G ⧸ pCore 2 G))).Prime)
    (hfive : 5 ∣ Nat.card (I ⧸ pCore 2 I))
    (hcode : ¬ (T : Subgroup G) ≤ normalizer ((pResidual 2 I).map I.subtype : Set G)) :
    False := by
  apply incompatible_with_code_obstruction T V I h hTV hgen _ hcode
  exact quotient_cover_of_prime_residual_of_intrinsic_divisor I
    (by decide : Nat.Prime 5) (by decide) hr hfive

/-- The small prime-order alternatives give all residual-lift conclusions from intrinsic I-data. -/
theorem conclusions_of_prime_sieve
    (T : Sylow 2 G) (V I A : Subgroup G) (h : G)
    (hh : h ∈ I) (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hgen : V ⊔ V.map (MulAut.conj h⁻¹).toMonoidHom = I)
    (hP : A ⊔ (V ⊓ I.pCoreIn 2) = I.pCoreIn 2)
    {p : ℕ} (hp : p.Prime) (ho : p ≠ 2)
    (hr : (Nat.card (pResidual 2 (G ⧸ pCore 2 G))).Prime)
    (hdiv : p ∣ Nat.card (I ⧸ pCore 2 I)) :
    (pResidual 2 I).map I.subtype = pResidual 2 G ∧
      (T : Subgroup G) ≤ normalizer ((pResidual 2 I).map I.subtype : Set G) ∧
      (Set.univ : Set G) = (I : Set G) * (T : Set G) ∧
      (T : Subgroup G) ≤ normalizer ((V ⊔ A : Subgroup G) : Set G) :=
  conclusions_of_quotient_cover T V I A h hh hTV hgen hP
    (quotient_cover_of_prime_residual_of_intrinsic_divisor I hp ho hr hdiv)

end CFSG.Quasithin.Chapter8.Section02.Normalizer.ParabolicReduction.RankSieve
