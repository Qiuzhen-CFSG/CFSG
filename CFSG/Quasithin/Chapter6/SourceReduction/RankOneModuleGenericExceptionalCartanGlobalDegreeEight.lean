module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanGlobalFermatRank
import all CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanGlobalPrimeHallRank
import all CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanGlobalSpecialLinearResidual
import all CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanGlobalPrimeSymplecticResidual

/-!
# Degree-eight normalization in the full split-torus residual rows

The original left Cartan has squarefree order 255 = 3·5·17. Each of its
three prime-order subgroups normalizes the residual: otherwise local control
gives a zero-core join, forcing prime rank at most one in the right Hall
group and the overlap. The SL₃ or Sp₄ residual, or the exchanged linear row, supplies two independent
torus directions at the same prime, since eight divides its field degree.
Cauchy's theorem and coprime cardinalities show that these three subgroups
generate the whole original Cartan.

This closes the degree-eight rows without a source 5.1.6 module or torus
splitting premise. The field degrees remain distinct. The internal imports
reuse the checked literal normalizer and Hall-torus constructions while
preserving their existing public boundaries.
Source: Aschbacher–Smith 5.1.6(4) and 5.2.2, printed pp.632–633,647–649.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric
variable {G : Type*} [Group G] [Finite G]

/-- The genuine SL₃ residual excludes any escaping prime in its split torus. -/
theorem CartanPair.specialLinear_residual_fermat_not_dvd {κ : GroupClass}
    {T : Sylow 2 G} {L W H A B D : Subgroup G} {n p f : ℕ}
    (c : CartanPair T L H A B) (h : Input κ T L W n)
    (hp : p = 3 ∨ p = 5 ∨ p = 17) (hDA : D ≤ A) (hcard : Nat.card D = p)
    (hzero : (D ⊔ H).pCoreIn 2 = ⊥)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hf : 1 < f)
    (hm : Chapter1.Section02.LocalModels.IsSL
      ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 (2 ^ f)) : ¬ p ∣ 2 ^ f - 1 := by
  intro hdiv
  have hprime : p.Prime := by rcases hp with rfl | rfl | rfl <;> decide
  have ho : Odd p := by rcases hp with rfl | rfl | rfl <;> decide
  let : Fact p.Prime := ⟨hprime⟩
  obtain ⟨F,_,_,hF,N,hNM,⟨e⟩⟩ := specialLinear_residual_normalizer hH hf hm
  have hu := c.overlap_fermatRank_le_one h hp hDA hcard hzero hH.1.1.1
  have hr := primeRank_mono p hNM
  rw [← primeRank_equiv p (N.equivMapOfInjective (residual H).subtype
    (residual H).subtype_injective)] at hr
  have hl := primeRank_le_of_surjective_of_coprime p (QuotientGroup.mk' (pCore 2 N))
    (QuotientGroup.mk'_surjective _) (by
      rw [QuotientGroup.ker_mk']
      obtain ⟨k,hk⟩ := (pCore_isPGroup (p := 2) (G := N)).exists_card_eq
      rw [hk]
      exact (Nat.coprime_two_right.mpr ho).pow_right k)
  rw [primeRank_equiv p e,primeRank_prod_eq_add] at hl
  have hdvd : p ∣ Nat.card Fˣ := by rwa [Nat.card_units,hF]
  obtain ⟨x,hx⟩ := exists_prime_orderOf_dvd_card' (G := Fˣ) p hdvd
  let E := zpowers x
  have hE : Nat.card E = p := (Nat.card_zpowers x).trans hx
  have hpos : 1 ≤ primeRank p Fˣ := primeRank_ge_of_elementary_embedding
    (fun y : E => by simpa only [hE] using pow_card_eq_one' (x := y))
    (by simpa using hE) E.subtype E.subtype_injective
  omega

/-- The genuine symplectic residual excludes each of the three degree-eight primes. -/
theorem CartanPair.symplectic_residual_fermat_not_dvd {κ : GroupClass}
    {T : Sylow 2 G} {L W H A B D : Subgroup G} {n p f : ℕ}
    (c : CartanPair T L H A B) (h : Input κ T L W n)
    (hp : p = 3 ∨ p = 5 ∨ p = 17) (hDA : D ≤ A) (hcard : Nat.card D = p)
    (hzero : (D ⊔ H).pCoreIn 2 = ⊥)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H) (hf : 1 < f)
    (hm : ClassicalGroup.IsPSp ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 2 (2 ^ f)) :
    ¬ p ∣ 2 ^ f - 1 := by
  intro hdiv
  have hprime : p.Prime := by rcases hp with rfl | rfl | rfl <;> decide
  let : Fact p.Prime := ⟨hprime⟩
  obtain ⟨F,_,_,_,hF,⟨e⟩⟩ := right_torus_of_residual c h.sylow_normalizes hH hgen hf hm
  have hu := c.right_fermatRank_le_one h hp hDA hcard hzero hH.1.1.1
  rw [primeRank_equiv p e,primeRank_prod_eq_add] at hu
  have hdvd : p ∣ Nat.card Fˣ := by rwa [Nat.card_units,hF]
  obtain ⟨x,hx⟩ := exists_prime_orderOf_dvd_card' (G := Fˣ) p hdvd
  let E := zpowers x
  have hE : Nat.card E = p := (Nat.card_zpowers x).trans hx
  have hpos : 1 ≤ primeRank p Fˣ := primeRank_ge_of_elementary_embedding
    (fun y : E => by simpa only [hE] using pow_card_eq_one' (x := y))
    (by simpa using hE) E.subtype E.subtype_injective
  omega

private theorem card_255_le_of_prime_subgroups {A N : Subgroup G}
    (hcard : Nat.card A = 255)
    (hsub : ∀ p : ℕ, p = 3 ∨ p = 5 ∨ p = 17 →
      ∀ D : Subgroup G, D ≤ A → Nat.card D = p → D ≤ N) : A ≤ N := by
  have hdvd (p : ℕ) (hp : p = 3 ∨ p = 5 ∨ p = 17) :
      p ∣ Nat.card (A ⊓ N : Subgroup G) := by
    have hprime : p.Prime := by rcases hp with rfl | rfl | rfl <;> decide
    let : Fact p.Prime := ⟨hprime⟩
    have hpc : p ∣ Nat.card A := by rw [hcard]; rcases hp with rfl | rfl | rfl <;> decide
    obtain ⟨P,hP⟩ := Sylow.exists_subgroup_card_pow_prime (G := A) p (n := 1)
      (by simpa only [pow_one] using hpc)
    let D := P.map A.subtype
    have hD : Nat.card D = p := by
      rw [card_map_of_injective A.subtype_injective]
      simpa only [pow_one] using hP
    rw [←hD]
    exact card_dvd_of_le (le_inf (map_subtype_le P) (hsub p hp D (map_subtype_le P) hD))
  have h15 : 15 ∣ Nat.card (A ⊓ N : Subgroup G) :=
    (by decide : Nat.Coprime 3 5).mul_dvd_of_dvd_of_dvd
      (hdvd 3 (.inl rfl)) (hdvd 5 (.inr (.inl rfl)))
  have h255 : 255 ∣ Nat.card (A ⊓ N : Subgroup G) :=
    (by decide : Nat.Coprime 15 17).mul_dvd_of_dvd_of_dvd
      h15 (hdvd 17 (.inr (.inr rfl)))
  have he : A ⊓ N = A := eq_of_le_of_card_ge inf_le_left (by
    rw [hcard]
    exact Nat.le_of_dvd Nat.card_pos h255)
  exact he ▸ inf_le_right

/-- The degree-eight Cartan normalizes an SL₃ residual whenever eight divides
its field degree. Every prime-order factor, including order seventeen, is handled. -/
theorem Input.cartan_normalizes_of_specialLinear_residual_degree_eight {κ : GroupClass}
    {T : Sylow 2 G} {L W H A B : Subgroup G} {f : ℕ}
    (h : Input κ T L W 8)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (c : CartanPair T L H A B) (hcontrol : CartanLocalControl A H)
    (hf : 1 < f) (hnf : 8 ∣ f)
    (hm : Chapter1.Section02.LocalModels.IsSL
      ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 (2 ^ f)) :
    A ≤ normalizer (residual H : Set G) := by
  have hcard := (c.left_cyclic_and_card h.sylow_normalizes h.linear).2
  apply card_255_le_of_prime_subgroups (by simpa using hcard)
  intro p hp D hDA hD
  apply hcontrol D hDA
  intro hzero
  apply c.specialLinear_residual_fermat_not_dvd h hp hDA hD hzero hH hf hm
  have hdvd : p ∣ 2 ^ 8 - 1 := by
    rw [←hcard,←hD]
    exact card_dvd_of_le hDA
  exact hdvd.trans (Nat.pow_sub_one_dvd_pow_sub_one 2 hnf)

/-- The same three actual prime factors prove degree-eight normalization for
Sp₄, using the original residual quotient to construct the right Hall torus. -/
theorem Input.cartan_normalizes_of_symplectic_residual_degree_eight {κ : GroupClass}
    {T : Sylow 2 G} {L W H A B : Subgroup G} {f : ℕ}
    (h : Input κ T L W 8)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H)
    (c : CartanPair T L H A B) (hcontrol : CartanLocalControl A H)
    (hf : 1 < f) (hnf : 8 ∣ f)
    (hm : ClassicalGroup.IsPSp ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 2 (2 ^ f)) :
    A ≤ normalizer (residual H : Set G) := by
  have hcard := (c.left_cyclic_and_card h.sylow_normalizes h.linear).2
  apply card_255_le_of_prime_subgroups (by simpa using hcard)
  intro p hp D hDA hD
  apply hcontrol D hDA
  intro hzero
  apply c.symplectic_residual_fermat_not_dvd h hp hDA hD hzero hH hgen hf hm
  have hdvd : p ∣ 2 ^ 8 - 1 := by
    rw [←hcard,←hD]
    exact card_dvd_of_le hDA
  exact hdvd.trans (Nat.pow_sub_one_dvd_pow_sub_one 2 hnf)

open ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels

/-- The exchanged linear row also excludes order seventeen in its marked torus. -/
theorem CartanPair.exchanged_linear_torus_fermat_not_dvd {κ : GroupClass}
    {T : Sylow 2 G} {L W H A B D : Subgroup G} {n p f : ℕ}
    (c : CartanPair T L H A B) (h : Input κ T L W n)
    (hp : p = 3 ∨ p = 5 ∨ p = 17) (hDA : D ≤ A) (hcard : Nat.card D = p)
    (hzero : (D ⊔ H).pCoreIn 2 = ⊥)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    {C : Subgroup H} (hC : C.IsCComponent)
    (hqs : IsQuasisimple (C ⧸ pCore 2 C))
    (hc : ExchangedClauses ((normalizer (L : Set G)).subgroupOf H) C
      ((T : Subgroup G).subgroupOf H))
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (hF : Nat.card F = 2 ^ f)
    (hm : ModelBorelPair ((normalizer (L : Set G)).subgroupOf H) C
      (BenderSuzuki.Converse.PBorel F)) : ¬ p ∣ 2 ^ f - 1 := by
  have hprime : p.Prime := by rcases hp with rfl | rfl | rfl <;> decide
  have ho : Odd p := by rcases hp with rfl | rfl | rfl <;> decide
  let : Fact p.Prime := ⟨hprime⟩
  obtain ⟨e,he⟩ := hm
  have hz : center (sourceImage ((normalizer (L : Set G)).subgroupOf H) C) = ⊥ := by
    apply eq_bot_iff.mpr
    intro x hx
    have hh := ((centerCongr e) ⟨x,hx⟩).property
    change e x ∈ center (BenderSuzuki.Converse.PSL2 F) at hh
    rw [Atlas.RankOneFieldAutomorphisms.psl_center_eq_bot] at hh
    exact e.map_eq_one_iff.mp (mem_bot.mp hh)
  have hnot := exchanged_overlap_prime_not_dvd hC hqs hc hz
    (comap_mono h.sylow_normalizes) p ho
  have hr : primeRank p ((normalizer (L : Set G)).subgroupOf H) ≤ 1 := by
    have he : ((normalizer (L : Set G) ⊓ H).subgroupOf H) =
        (normalizer (L : Set G)).subgroupOf H := inf_subgroupOf_right _ _
    rw [←he,primeRank_equiv p (subgroupOfEquivOfLe inf_le_right)]
    exact c.overlap_fermatRank_le_one h hp hDA hcard hzero hH.1.1.1
  have hcB : Nat.card (BenderSuzuki.Converse.PBorel F) =
      Nat.card (sourceImage ((normalizer (L : Set G)).subgroupOf H)
        (((normalizer (L : Set G)).subgroupOf H) ⊓ C)) := by
    rw [←he,card_map_of_injective e.injective]
    exact Nat.card_congr (subgroupOfEquivOfLe (show
      sourceImage ((normalizer (L : Set G)).subgroupOf H) (((normalizer (L : Set G)).subgroupOf H) ⊓ C) ≤
        sourceImage ((normalizer (L : Set G)).subgroupOf H) C from map_mono inf_le_right)).toEquiv
  intro hdiv
  apply hnot hr
  rw [←hcB]
  apply hdiv.trans
  have hh := card_dvd_of_le (BenderSuzuki.Converse.PTorus_le_PBorel (F := F))
  rwa [BenderSuzuki.Converse.PTorus_card,Nat.card_units,hF] at hh

/-- Degree-eight normalization in the exchanged linear row, retaining the
actual original component and its Borel marking in H/core_H(M). -/
theorem Input.cartan_normalizes_of_exchanged_linear_degree_eight {κ : GroupClass}
    {T : Sylow 2 G} {L W H A B : Subgroup G} {f : ℕ}
    (h : Input κ T L W 8)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (c : CartanPair T L H A B) (hcontrol : CartanLocalControl A H)
    (hnf : 8 ∣ f)
    {C : Subgroup H} (hC : C.IsCComponent)
    (hqs : IsQuasisimple (C ⧸ pCore 2 C))
    (hc : ExchangedClauses ((normalizer (L : Set G)).subgroupOf H) C
      ((T : Subgroup G).subgroupOf H))
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (hF : Nat.card F = 2 ^ f)
    (hm : ModelBorelPair ((normalizer (L : Set G)).subgroupOf H) C
      (BenderSuzuki.Converse.PBorel F)) :
    A ≤ normalizer (residual H : Set G) := by
  have hcard := (c.left_cyclic_and_card h.sylow_normalizes h.linear).2
  apply card_255_le_of_prime_subgroups (by simpa using hcard)
  intro p hp D hDA hD
  apply hcontrol D hDA
  intro hzero
  apply c.exchanged_linear_torus_fermat_not_dvd h hp hDA hD hzero hH hC hqs hc hF hm
  have hdvd : p ∣ 2 ^ 8 - 1 := by
    rw [←hcard,←hD]
    exact card_dvd_of_le hDA
  exact hdvd.trans (Nat.pow_sub_one_dvd_pow_sub_one 2 hnf)

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric
