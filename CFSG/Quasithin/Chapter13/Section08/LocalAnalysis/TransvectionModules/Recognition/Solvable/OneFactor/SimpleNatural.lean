module

public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.TransvectionModules.Recognition.Solvable.OneFactor.Covered
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.TransvectionModules.Parabolic.Marking.EarlierCore.ComponentSetup
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.TransvectionModules.Parabolic.Marking.EarlierCore.Seed
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.TransvectionModules.Parabolic.Marking.EarlierCore.Applicability
public import Theory.SpecificGroups.SymmetricSix.BinaryFlags.NaturalResidualCard

/-!
# The ordinary natural marking in the one-factor argument

The permutation image of the literal point residual L₁ has order twelve.
Its kernel lies in O₂(L), so |L₁| has three-part three and divides a power
of two times three. This uses the same ordinary natural flag as the proved
seed-generation theorem, avoiding any change of the module marking.

Source: Aschbacher–Smith, proof of 13.8.5, printed pp.947–948
(PDF pp.964–965), with Notation 13.2.1, printed p.877.
-/

@[expose] public section

open Subgroup
open CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.Geometry.CoveredProduct.ResidualPlacement
open CFSG.Quasithin.Chapter13.Section08.TransvectionParabolic.EarlierCore
namespace CFSG.Quasithin.Chapter13.Section08.TransvectionRecognition.Solvable.OneFactor
variable {G : Type*} [Group G] [Finite G]

/-- The three-adic valuation and order bound for the same natural flag
used in the moved-space calculation. -/
theorem simple_natural_order_data {T : Sylow 2 G} {L V V₁ V₂ V₃ : Subgroup G}
    (d : NaturalSetup T L V V₁ V₂ V₃) :
    (Nat.card (one L T V₁)).factorization 3 = 1 ∧
      ∃ n : ℕ, Nat.card (one L T V₁) ∣ 3 * 2 ^ n := by
  let Y := localResidual L V₁
  let hYL : Y ≤ L := localResidual_le L V₁
  let f : Y →* Equiv.Perm (Fin 6) := d.permutation.comp (inclusion (hYL.trans le_sup_left))
  have hr : f.range = d.permutationImage Y := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨inclusion (hYL.trans le_sup_left) y, y.property, rfl⟩
    · rintro ⟨y, hy, rfl⟩
      exact ⟨⟨y, hy⟩, rfl⟩
  have hk : f.ker = (pCore 2 L).comap (inclusion hYL) := by
    ext y
    change d.permutation (inclusion (hYL.trans le_sup_left) y) = 1 ↔ _
    have he := d.model_compatible (inclusion hYL y)
    change d.permutation (inclusion (hYL.trans le_sup_left) y) = _ at he
    rw [he]
    change (d.model (QuotientGroup.mk' (pCore 2 L) (inclusion hYL y))).val = 1 ↔ _
    change ((d.model (QuotientGroup.mk' (pCore 2 L) (inclusion hYL y)) : alternatingGroup (Fin 6)) : Equiv.Perm (Fin 6)) =
      ((1 : alternatingGroup (Fin 6)) : Equiv.Perm (Fin 6)) ↔ _
    rw [Subtype.coe_inj, d.model.map_eq_one_iff]
    exact QuotientGroup.eq_one_iff _
  have hc : Nat.card f.range = 12 := by
    rw [hr, d.one_image]
    exact Theory.SpecificGroups.SymmetricSix.BinaryFlags.NaturalResidualCard.point_residual_card
      d.permutation.range d.alternating_le_range d.point d.point_dim
  have hp : IsPGroup 2 f.ker := by
    rw [hk]
    exact pCore_isPGroup.comap_of_injective _ (inclusion_injective hYL)
  obtain ⟨n, hn⟩ := hp.exists_card_eq
  have hord := card_eq_card_quotient_mul_card_subgroup f.ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv, hc, hn] at hord
  have he : one L T V₁ = Y := d.line_residual_eq
  rw [he]
  constructor
  · rw [hord, Nat.factorization_mul (by decide) (by positivity), Nat.factorization_pow,
      Nat.prime_two.factorization]
    rw [show (12 : ℕ) = 2 ^ 2 * 3 from rfl,
      Nat.factorization_mul (by decide) (by decide), Nat.factorization_pow,
      Nat.prime_two.factorization, Nat.prime_three.factorization]
    simp
  · refine ⟨n + 2, ?_⟩
    rw [hord]
    apply dvd_of_eq
    ring

/-- The source's literal three-part is three. -/
theorem simple_natural_threePart {T : Sylow 2 G} {L V V₁ V₂ V₃ : Subgroup G}
    (d : NaturalSetup T L V V₁ V₂ V₃) :
    3 ^ (Nat.card (one L T V₁)).factorization 3 = 3 := by
  rw [(simple_natural_order_data d).1, pow_one]

end CFSG.Quasithin.Chapter13.Section08.TransvectionRecognition.Solvable.OneFactor
end
