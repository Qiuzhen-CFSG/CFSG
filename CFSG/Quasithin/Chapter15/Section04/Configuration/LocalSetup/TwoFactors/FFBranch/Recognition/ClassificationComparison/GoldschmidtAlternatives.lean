module

public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.FFBranch.Recognition.ClassificationComparison.GoldschmidtAlternatives.Cases
public import Theory.GroupTheory.PCoreSurjective

/-!
# Applying F.6.18 and excluding its cyclic-Sylow alternative

The full universal F.6.18 implication is an explicit parameter, as is the existing
F.6.11 interface. We first use F.6.11 to preserve the Goldschmidt amalgam in the
literal quotient H/O_{3'}(H), then apply F.6.18 to that quotient. In alternative
(1) both quotient local two-cores are trivial. The compatible local quotient
isomorphisms in F.6.11 identify the original local two-cores with the embedded
O₂(H), contradicting the given inequality. The argument treats both possible
names for the generators and retains every other row of F.6.18.

The only universal source implications left as parameters are `F611Universal`
and `F618Universal K`. The latter is relative to the same known-simple class K
as the SQTK input; its source instantiation must use the full known-simple class.
Neither universal implication is asserted here. In particular, this module does
not identify the source quotient with H/O₂(H) or with the offender group.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
1 March 2004 manuscript, F.6.11 pp.306–307 and F.6.18 pp.309–310;
the comparison application is in 15.4.18, printed p.1163.
-/

@[expose] public section
open Subgroup
namespace CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison
universe u
variable {H : Type u} [Group H] [Finite H]

/-- All of the universal F.6.18 implication for the specified source class.
The triple belongs to the literal quotient of an SQTK group; the covering group
itself need not have a Goldschmidt triple. Its finite hypothesis is explicit. -/
def F618Universal (K : GroupClass.{u}) : Prop :=
  ∀ {H : Type u} [Group H] [Finite H], IsSQTK K H →
    ∀ (G₁ G₂ : Subgroup (threePrimeQuotient H)),
      ChapterF.IsGoldschmidtTriple G₁ G₂ → GoldschmidtAlternatives.Alternatives G₁ G₂

/-- A trivial local two-core after the canonical source quotient forces the
original local two-core to be the restriction of the ambient two-core.
The p-core lifting theorem applies to the actual quotient by that restriction. -/
theorem local_twoCore_eq_of_trivial_threePrimeImage (U : Subgroup H)
    (h : CompatibleThreePrimeQuotient U)
    (hbot : pCore 2 (threePrimeImage U) = ⊥) :
    pCore 2 U = (pCore 2 H).subgroupOf U := by
  obtain ⟨e, _⟩ := h
  have he : pCore 2 (U ⧸ (pCore 2 H).subgroupOf U) = ⊥ := by
    apply ((pCore 2 (U ⧸ (pCore 2 H).subgroupOf U)).map_eq_bot_iff_of_injective
      (f := e.toMonoidHom) e.injective).mp
    rw [pCore_map_iso, hbot]
  let q := QuotientGroup.mk' ((pCore 2 H).subgroupOf U)
  have hk : IsPGroup 2 q.ker := by
    rw [QuotientGroup.ker_mk']
    exact pCore_isPGroup.comap_subtype
  have hc := q.comap_pCore_of_ker_isPGroup (QuotientGroup.mk'_surjective _) hk
  rw [he] at hc
  change q.ker = pCore 2 U at hc
  rw [QuotientGroup.ker_mk'] at hc
  exact hc.symm

/-- Transport through F.6.11 uses the embedded original cores, not an equality
between subgroups of two different local group types. -/
theorem original_local_cores_eq_of_trivial_images
    (G₁ G₂ : Subgroup H) (triple : ChapterF.IsGoldschmidtTriple G₁ G₂)
    (preserved : F611Preserved G₁ G₂)
    (h₁ : pCore 2 (threePrimeImage G₁) = ⊥)
    (h₂ : pCore 2 (threePrimeImage G₂) = ⊥) :
    (pCore 2 G₁).map G₁.subtype = (pCore 2 G₂).map G₂.subtype := by
  rw [local_twoCore_eq_of_trivial_threePrimeImage G₁ preserved.left_quotient h₁,
    local_twoCore_eq_of_trivial_threePrimeImage G₂ preserved.right_quotient h₂,
    Subgroup.map_subgroupOf_eq_of_le (triple.twoCore_isGreatest.1.1.trans inf_le_left),
    Subgroup.map_subgroupOf_eq_of_le (triple.twoCore_isGreatest.1.1.trans inf_le_right)]

/-- Row (1) is impossible in either orientation of the source naming convention. -/
theorem not_F618_case1_of_different_cores
    (G₁ G₂ : Subgroup H) (triple : ChapterF.IsGoldschmidtTriple G₁ G₂)
    (preserved : F611Preserved G₁ G₂)
    (different : (pCore 2 G₁).map G₁.subtype ≠ (pCore 2 G₂).map G₂.subtype) :
    ¬ (GoldschmidtAlternatives.Case1 (threePrimeImage G₁) (threePrimeImage G₂) ∨
      GoldschmidtAlternatives.Case1 (threePrimeImage G₂) (threePrimeImage G₁)) := by
  intro h
  rcases h with h | h
  · exact different (original_local_cores_eq_of_trivial_images G₁ G₂ triple preserved
      h.2.1 h.2.2.1)
  · exact different (original_local_cores_eq_of_trivial_images G₁ G₂ triple preserved
      h.2.2.1 h.2.1)

/-- Conditional application of the complete source classification, with only
row (1) excluded. Every surviving ambient, field, action and local-group clause
belongs to the actual H/O_{3'}(H) and the actual images of G₁ and G₂. -/
theorem apply_F618_of_different_cores {K : GroupClass.{u}}
    (source611 : F611Universal.{u}) (source618 : F618Universal K)
    (hH : IsSQTK K H) (G₁ G₂ : Subgroup H)
    (triple : ChapterF.IsGoldschmidtTriple G₁ G₂)
    (different : (pCore 2 G₁).map G₁.subtype ≠ (pCore 2 G₂).map G₂.subtype) :
    F611Preserved G₁ G₂ ∧
      GoldschmidtAlternatives.Remaining (threePrimeImage G₁) (threePrimeImage G₂) := by
  obtain ⟨_, _, preserved⟩ := apply_F611_of_different_cores source611 G₁ G₂ triple different
  refine ⟨preserved, ?_⟩
  have excluded := not_F618_case1_of_different_cores G₁ G₂ triple preserved different
  rcases source618 hH (threePrimeImage G₁) (threePrimeImage G₂) preserved.triple with
    (h | h) | (h | h)
  · exact (excluded (Or.inl h)).elim
  · exact Or.inl h
  · exact (excluded (Or.inr h)).elim
  · exact Or.inr h

end CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison
