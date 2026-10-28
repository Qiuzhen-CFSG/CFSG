module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.ParameterComponent.Recognition.Paired.Structure
public import Theory.GroupTheory.PerfectCentralCoverCyclicOddSylow
public import Theory.GroupTheory.PerfectCentralCoverOddRankRigidity
public import Theory.SpecificGroups.SL2.BinaryOddRank
public import Theory.SpecificGroups.Suzuki.OddSubgroups

/-!
# The literal two-core quotient in the rank-one star-model rows

The inclusion of a C-component B in X induces a surjection from B/O₂(B)
to its image in X/R whenever R contains O₂(X). Quasisimplicity makes its
kernel central. If every odd-prime rank of the image is at most one,
cyclic-Sylow transfer kills the odd part of that kernel; the trivial
two-core of B/O₂(B) kills the two-part. Thus the specified projection is
an isomorphism, with its value on each original representative retained.

Binary PSL₂ and Suzuki satisfy the required odd-rank bound. StarSource
applies this to the actual component and maximal-core quotient in 11.3.5,
closing the gap between a star-image model and the required K/O₂(K) model.
This does not identify the model exponent with the generation minimum.
Source: Aschbacher--Smith E.2.2, pp.215--216; I.1.2, p.407; 11.3.5, p.771.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ParameterComponent.Models
variable {X : Type*} [Group X] [Finite X]

/-- The map induced by the original inclusion, with its exact image carrier. -/
def starProjection (B R : Subgroup X) [R.Normal] (hB : B.IsCComponent)
    (hR : pCore 2 X ≤ R) :
    (B ⧸ pCore 2 B) →* B.map (QuotientGroup.mk' R) :=
  QuotientGroup.lift (pCore 2 B) ((QuotientGroup.mk' R).subgroupMap B) (by
    rw [ker_subgroupMap, QuotientGroup.ker_mk', pCore_subnormal_eq_comap 2 hB.subnormal]
    exact comap_mono hR)

/-- The inclusion quotient still surjects onto the entire star image. -/
theorem starProjection_surjective (B R : Subgroup X) [R.Normal]
    (hB : B.IsCComponent) (hR : pCore 2 X ≤ R) :
    Function.Surjective (starProjection B R hB hR) :=
  QuotientGroup.lift_surjective_of_surjective _ _
    ((QuotientGroup.mk' R).subgroupMap_surjective B) _

/-- Quasisimplicity makes this particular projection a perfect central cover. -/
def starCover (B R : Subgroup X) [R.Normal] (hB : B.IsCComponent)
    [IsQuasisimple (B ⧸ pCore 2 B)] (hR : pCore 2 X ≤ R)
    [Nontrivial (B.map (QuotientGroup.mk' R))] :
    PerfectCentralCovering.Cover (B ⧸ pCore 2 B) (B.map (QuotientGroup.mk' R)) where
  toMonoidHom := starProjection B R hB hR
  surjective := starProjection_surjective B R hB hR
  isPerfect := inferInstance
  ker_le_center := by
    rcases IsQuasisimple.normal_le_center_or_eq_top (starProjection B R hB hR).ker with hk | hk
    · exact hk
    · have hz := MonoidHom.range_eq_bot_iff.mpr (MonoidHom.ker_eq_top_iff.mp hk)
      exact (bot_ne_top (hz.symm.trans
        (MonoidHom.range_eq_top.mpr (starProjection_surjective B R hB hR)))).elim

/-- Odd rank one removes the central kernel without a multiplier-table premise. -/
theorem starProjection_injective (B R : Subgroup X) [R.Normal] (hB : B.IsCComponent)
    [IsQuasisimple (B ⧸ pCore 2 B)] (hR : pCore 2 X ≤ R)
    [Nontrivial (B.map (QuotientGroup.mk' R))]
    (hr : ∀ p : ℕ, p.Prime → Odd p →
      primeRank p (B.map (QuotientGroup.mk' R)) ≤ 1) :
    Function.Injective (starProjection B R hB hR) := by
  let c := starCover B R hB hR
  have ho : Odd (Nat.card c.toMonoidHom.ker) := Nat.not_even_iff_odd.mp (by
    rw [even_iff_two_dvd]
    exact PerfectCentralCovering.not_dvd_card_central_of_pCore_eq_bot
      (pCore_quotient_pCore_eq_bot 2) _ c.ker_le_center)
  exact (MonoidHom.ker_eq_bot_iff _).mp
    (c.ker_eq_bot_of_odd_of_odd_primeRank_le_one ho hr)

/-- Binary PSL₂ has cyclic odd Sylow subgroups, including the field-four case. -/
theorem odd_rank_of_binary_linear {Y : Type*} [Group Y] [Finite Y]
    {f : ℕ} (_hf : 0 < f) (hm : ClassicalGroup.IsPSL Y 2 (2 ^ f))
    (p : ℕ) (hp : p.Prime) (ho : Odd p) : primeRank p Y ≤ 1 := by
  obtain ⟨F,hF,hfin,hcard,⟨e⟩⟩ := hm
  let := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using hcard)
  let : Fact p.Prime := ⟨hp⟩
  let P : Sylow p (Matrix.SpecialLinearGroup (Fin 2) F) := Classical.choice inferInstance
  have hP : IsCyclic P := P.isCyclic_of_odd_of_primeRank_le_one ho
    (Matrix.SL2.binary_odd_primeRank_le_one ho)
  rw [primeRank_equiv p e]
  exact P.primeRank_le_one_of_surjective hP (QuotientGroup.mk' _)
    (QuotientGroup.mk'_surjective _)

/-- The actual nondegenerate Suzuki matrix model has odd-prime rank at most one. -/
theorem odd_rank_of_suzuki {Y : Type*} [Group Y] [Finite Y]
    {m : ℕ} (hm : 0 < m)
    (e : Y ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m)
    (p : ℕ) (hp : p.Prime) (ho : Odd p) : primeRank p Y ≤ 1 := by
  let : Fact p.Prime := ⟨hp⟩
  let P : Sylow p (BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m) := Classical.choice inferInstance
  rw [primeRank_equiv p e]
  exact P.primeRank_le_one_of_isCyclic
    (BenderSuzuki.MatrixGroups.suzukiSylow_isCyclic_of_ne_two hm
      (by intro he; subst p; exact ho.not_two_dvd_nat (dvd_refl 2)) P)

/-- The original projection is an isomorphism in the odd-rank-one rows. -/
def starEquiv (B R : Subgroup X) [R.Normal] (hB : B.IsCComponent)
    [IsQuasisimple (B ⧸ pCore 2 B)] (hR : pCore 2 X ≤ R)
    [Nontrivial (B.map (QuotientGroup.mk' R))]
    (hr : ∀ p : ℕ, p.Prime → Odd p →
      primeRank p (B.map (QuotientGroup.mk' R)) ≤ 1) :
    (B ⧸ pCore 2 B) ≃* B.map (QuotientGroup.mk' R) :=
  MulEquiv.ofBijective (starProjection B R hB hR)
    ⟨starProjection_injective B R hB hR hr, starProjection_surjective B R hB hR⟩

/-- Compatibility with the literal quotient maps on original representatives. -/
@[simp] theorem starEquiv_mk (B R : Subgroup X) [R.Normal] (hB : B.IsCComponent)
    [IsQuasisimple (B ⧸ pCore 2 B)] (hR : pCore 2 X ≤ R)
    [Nontrivial (B.map (QuotientGroup.mk' R))]
    (hr : ∀ p : ℕ, p.Prime → Odd p →
      primeRank p (B.map (QuotientGroup.mk' R)) ≤ 1) (x : B) :
    starEquiv B R hB hR hr (QuotientGroup.mk' (pCore 2 B) x) =
      (QuotientGroup.mk' R).subgroupMap B x := rfl

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ParameterComponent.Models
