module

public import CFSG.Quasithin.ChapterE.Section04.MathieuM12
public import CFSG.Quasithin.ChapterE.Section04.MathieuBounds.SmallQuotients

/-!
# The M₁₂ module bound in E.4.3(1)

For a finite group with trivial two-core and quasisimple generalized Fitting
subgroup L, an actual isomorphism L/Z(L) ≃ M₁₂ gives two distinct generating
overgroups of the prescribed Sylow two-subgroup. Each intrinsic two-core
quotient is S₃ and therefore contributes at most one to the rank budget.
The small-quotient generating-family bound then gives a(G,V) ≤ 2.

The imported M₁₂ construction proves center removal and G = LT from these
source hypotheses, and constructs the pair in both the simple group and its
full automorphism extension. The proof below retains the actual pair and its
quotient isomorphisms throughout; no family or numerical bound is assumed.
The strict Sylow fixed-space hypothesis supplies the required noncentralization
via G = LT. Faithfulness and finite dimension are retained in the public source
statement, consistently with the M₂₂ and M₂₄ endpoints.

This specializes the proved S₃/S₅ bound, independently of the literal general
E.4.2 statement and its different printed local-quotient convention.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, E.4.3(1),
printed pp.241–242 (PDF pp.252–253), with the standing hypotheses on p.240.
-/

public section

open Subgroup Theory.GroupTheory Representation.BinaryOffender
open Sporadic.Mathieu.M12SmallPair.ValueBoundParabolics
namespace CFSG.Quasithin.ChapterE.ValueBound.MathieuBounds
variable {G V : Type*} [Group G] [Finite G] [AddCommGroup V] [Module (ZMod 2) V]

/-- E.4.3(1) for the actual M₁₂ central quotient, retaining all permitted
central covers and outer extensions in the source hypotheses. -/
theorem moduleA_le_two_of_m12
    (ρ : Representation (ZMod 2) G V) [FiniteDimensional (ZMod 2) V]
    (_hρ : Function.Injective ρ) (T : Sylow 2 G)
    (hcore : pCore 2 G = ⊥) (hL : IsQuasisimple (generalizedFitting G))
    (e : (generalizedFitting G) ⧸ center (generalizedFitting G) ≃* Sporadic.Mathieu.M12)
    (hfixed : fixedSpace ρ ⊤ < fixedSpace ρ (T : Subgroup G)) :
    moduleA ρ ≤ 2 := by
  classical
  let : IsQuasisimple (generalizedFitting G) := hL
  obtain ⟨H, K, hne, hTH, hTK, hgen, ⟨eH⟩, ⟨eK⟩⟩ :=
    m12_exists_s3_pair hcore (generalizedFitting G) rfl e T
  let Δ : Finset (Subgroup G) := {H, K}
  have hT : ∀ J ∈ Δ, (T : Subgroup G) ≤ J := by
    intro J hJ
    simp only [Δ, Finset.mem_insert, Finset.mem_singleton] at hJ
    rcases hJ with rfl | rfl
    · exact hTH
    · exact hTK
  have hΔgen : sSup (Δ : Set (Subgroup G)) = ⊤ := by
    simpa only [Δ, Finset.coe_insert, Finset.coe_singleton, sSup_pair] using hgen
  have hquot : ∀ J ∈ Δ,
      Nonempty ((J ⧸ pCore 2 J) ≃* Equiv.Perm (Fin 3)) ∨
      Nonempty ((J ⧸ pCore 2 J) ≃* Equiv.Perm (Fin 5)) := by
    intro J hJ
    simp only [Δ, Finset.mem_insert, Finset.mem_singleton] at hJ
    rcases hJ with rfl | rfl
    · exact Or.inl ⟨eH⟩
    · exact Or.inl ⟨eK⟩
  have hbudget : localRankBudget Δ ≤ 2 := by
    simpa only [Δ, localRankBudget, Finset.sum_pair hne] using
      Nat.add_le_add (primeRank_two_le_one_of_equiv_s3 eH)
        (primeRank_two_le_one_of_equiv_s3 eK)
  have hLT : generalizedFitting G ⊔ (T : Subgroup G) = ⊤ :=
    (m12_component_equiv_and_sup hcore (generalizedFitting G) rfl e T).2
  exact (moduleA_le_of_symmetric_quotients ρ T hcore hL hLT hfixed
    Δ hT hΔgen hquot).trans (by exact_mod_cast hbudget)

end CFSG.Quasithin.ChapterE.ValueBound.MathieuBounds
