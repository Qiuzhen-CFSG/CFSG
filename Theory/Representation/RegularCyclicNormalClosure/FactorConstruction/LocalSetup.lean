module

public import Theory.Representation.RegularCyclicNormalClosure.FactorConstruction.ElementaryCases

/-!
# Constructing the actual local quotient from a noncommuting pair

Maximize the fixed-space intersection among noncommuting conjugates.
The commuting-pair dimension comparison makes this a maximum among all
distinct fixed-space pairs. The pointwise-fixer quotient then has the full
Goldschmidt–O'Nan input, and its singleton and swapped cases are excluded.

The complement case and the global compatibility of any exceptional
candidate remain separate obligations. This is a proved local consequence
of the original input, not the full factor-existence conclusion of
Aschbacher–Smith E.6.24, printed p.255.
-/

public section

open Module Subgroup Representation.BinaryOffender
namespace Representation.RegularCyclicNormalClosure
open FactorConstruction
variable {A W : Type*} [Group A] [Finite A] [AddCommGroup W] [Module (ZMod 2) W]
  [Finite W] {ρ : Representation (ZMod 2) A W} {C : Subgroup A}

/-- The noncommuting branch admits an actual maximal-intersection quotient
with all Goldschmidt–O'Nan hypotheses and with the singleton and swapped
alternatives excluded. The complement and transitive branches remain. -/
theorem Input.exists_local_quotient (h : Input ρ C)
    (hex : ∃ a : A, ¬ ∀ c ∈ C, ∀ d ∈ C.map (MulAut.conj a).toMonoidHom, Commute c d) :
    ∃ a : A,
      (¬ ∀ c ∈ C, ∀ d ∈ C.map (MulAut.conj a).toMonoidHom, Commute c d) ∧
      let F := fixedSpace ρ C ⊓ (fixedSpace ρ C).map (ρ a)
      (∀ b : A, (fixedSpace ρ C).map (ρ b) ≠ fixedSpace ρ C →
        finrank (ZMod 2) ↥(fixedSpace ρ C ⊓ (fixedSpace ρ C).map (ρ b)) ≤ finrank (ZMod 2) F) ∧
      GoldschmidtONan.Input (quotientOnFixer ρ F) (C.subgroupOf (pointwiseFixer ρ F)) ∧
      ¬ GoldschmidtONan.SingletonCase (quotientOnFixer ρ F) (C.subgroupOf (pointwiseFixer ρ F)) ∧
      ¬ GoldschmidtONan.SwappedCase (quotientOnFixer ρ F) (C.subgroupOf (pointwiseFixer ρ F)) := by
  obtain ⟨a, hnc, hne, hmax⟩ := h.exists_maximal_noncommuting hex
  refine ⟨a, hnc, hmax, ?_⟩
  let F := fixedSpace ρ C ⊓ (fixedSpace ρ C).map (ρ a)
  have hdim := h.intersection_dimensions a hne
  have hFU : F < fixedSpace ρ C := lt_of_le_of_ne inf_le_left (by
    intro he
    change finrank (ZMod 2) F < finrank (ZMod 2) (fixedSpace ρ C) ∧ _ at hdim
    rw [he] at hdim
    exact (Nat.lt_irrefl _) hdim.1)
  have hlocal := h.goldschmidtONan_onFixer F hFU hdim.2 hmax
  have hDK : C.map (MulAut.conj a).toMonoidHom ≤ pointwiseFixer ρ F := by
    apply (le_pointwiseFixer_iff ρ _ F).mpr
    rw [fixedSpace_map_conj]
    exact inf_le_right
  exact ⟨hlocal, h.not_singleton_onFixer a hnc F hFU.le hDK,
    h.not_swapped_onFixer a hnc F hFU.le hDK hlocal⟩

end Representation.RegularCyclicNormalClosure
