module
public import CFSG.Quasithin.Chapter15.Section02.SourcePlaneUniqueness.CharacteristicTwo.SmallActions
public import Theory.GroupTheory.PResidual.PrimeToSubnormal
public import Theory.GroupTheory.NormalizedSupCard

/-!
# Two-perfect seeds in the source small-action argument

The source requires Y₁ = O²(Y₁), expressed by IsPPerfect 2 Y₁.
It does not assert Y₁ = O₂(Y₁). The seed is embedded in the literal
NI = M ∩ I, with the original S-action and the actual S₃ core quotient.

A two-perfect seed lying in MI = Mc ∩ I lies in C_M(V), by the residual
of the preceding intersection formula M ∩ Mc = C_M(V)T. If C_M(V) is
a 3′-group, its product with the two-group S cannot have an S₃ quotient.
Thus the noncontainment in MI needed by the normalizer argument is derived.

Source: Aschbacher--Smith, combined manuscript (1 March 2004),
15.2.14(5), 15.2.21(3), and 15.2.22, printed pp.1112--1115;
refs/quasithin.pdf. The corrected seed is consumed in ComponentModels.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section02.SmallActionsSource
variable {G : Type*} [Group G] [Finite G]

/-- The subgroup supplied to 15.2.21(3) and 15.2.22 is two-perfect,
not its own two-core. NI is literally M ∩ I. -/
structure Seed (M I S Y : Subgroup G) : Prop where
  le_NI : Y ≤ M ⊓ I
  perfect : IsPPerfect 2 Y
  normalized : S ≤ normalizer (Y : Set G)
  quotient : Nonempty (((Y ⊔ S : Subgroup G) ⧸ pCore 2 (Y ⊔ S : Subgroup G)) ≃*
    Equiv.Perm (Fin 3))

variable {T : Sylow 2 G} {M Mc V H ZS I Y : Subgroup G}
variable {hsource : ChosenSmallSource T M Mc V}
variable (d : PlaneUniquenessPreceding hsource H ZS)
include d

/-- A two-perfect subgroup of NI lying in MI centralizes V by 15.2.14(5). -/
theorem Seed.le_module_centralizer_of_le_MI
    (s : Seed M I (smallActionS T ZS) Y) (hY : Y ≤ Mc ⊓ I) :
    Y ≤ M ⊓ centralizer (V : Set G) := by
  have hYA : Y ≤ M ⊓ Mc := le_inf (s.le_NI.trans inf_le_left) (hY.trans inf_le_left)
  have hm := embedded_pResidual_mono 2 hYA
  rw [(pResidual_eq_top_iff 2 Y).mpr s.perfect, ← MonoidHom.range_eq_map, range_subtype] at hm
  exact hm.trans d.partner_intersection_residual_le_module_centralizer

/-- In 15.2.22, the three-prime centralizer forces Y₁ outside MI.
Thus the missing containment hypothesis of 15.2.21(3) is derived when
needed, without ever treating Y₁ as a two-group. -/
theorem Seed.not_le_MI (s : Seed M I (smallActionS T ZS) Y)
    (hC : IsSmallActionThreePrime (M ⊓ centralizer (V : Set G))) :
    ¬ Y ≤ Mc ⊓ I := by
  intro hY
  have hCcard : Nat.Coprime 3 (Nat.card (M ⊓ centralizer (V : Set G) : Subgroup G)) := by
    have hh := primeToResidual_index_coprime (G := (M ⊓ centralizer (V : Set G) : Subgroup G)) 3
    change primeToResidual 3 (M ⊓ centralizer (V : Set G) : Subgroup G) = ⊥ at hC
    rwa [hC, index_bot] at hh
  have hYcard := hCcard.coprime_dvd_right
    (card_dvd_of_le (s.le_module_centralizer_of_le_MI d hY))
  have hScard : Nat.Coprime 3 (Nat.card (smallActionS T ZS)) := by
    obtain ⟨n, hn⟩ := (T.isPGroup'.to_le
      (show smallActionS T ZS ≤ (T : Subgroup G) from inf_le_left)).exists_card_eq
    rw [hn]
    exact (by decide : Nat.Coprime 3 2).pow_right n
  have hprod := hYcard.mul_right hScard
  rw [card_mul_eq_card_inf_mul_card_sup_of_normalizes Y (smallActionS T ZS)
    s.normalized] at hprod
  have hq := hprod.coprime_dvd_right
    (dvd_mul_left (Nat.card (Y ⊔ smallActionS T ZS : Subgroup G))
      (Nat.card (Y ⊓ smallActionS T ZS : Subgroup G)))
  have hquot := hq.coprime_dvd_right
    (card_dvd_of_surjective (QuotientGroup.mk' (pCore 2 (Y ⊔ smallActionS T ZS : Subgroup G)))
      (QuotientGroup.mk'_surjective _))
  obtain ⟨e⟩ := s.quotient
  rw [Nat.card_congr e.toEquiv, Nat.card_perm, Nat.card_fin] at hquot
  norm_num at hquot
end CFSG.Quasithin.Chapter15.Section02.SmallActionsSource
