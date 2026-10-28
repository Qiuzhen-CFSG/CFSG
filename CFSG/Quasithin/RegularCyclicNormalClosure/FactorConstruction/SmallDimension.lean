module

public import CFSG.Quasithin.RegularCyclicNormalClosure.FactorConstruction.LocalExistence

/-!
# The factor seed in binary dimension at most three

If the conjugates commute, the original cyclic actor supplies the seed.
Otherwise the constructed exceptional factor has a three-dimensional moved
space and therefore zero fixed space. Since it is the full pointwise fixer
of that fixed space, it is the whole ambient group and the cross-fixation
clause is vacuous.

This closes the small-dimensional branch of Aschbacher--Smith E.6.24,
printed p.255. The higher-dimensional order-three compatibility problem
remains with the general factor construction.
-/

public section

open Module Subgroup Representation Representation.BinaryOffender
open Representation.RegularCyclicNormalClosure
open Representation.RegularCyclicNormalClosure.FactorConstruction
namespace CFSG.Quasithin.RegularCyclicNormalClosure
variable {A W : Type*} [Group A] [Finite A] [AddCommGroup W] [Module (ZMod 2) W]
  [Finite W] {ρ : Representation (ZMod 2) A W} {C : Subgroup A}

/-- The full factor seed exists in ambient binary dimension at most three. -/
theorem exists_factorSeed_of_finrank_le_three (h : Input ρ C)
    (hdim : finrank (ZMod 2) W ≤ 3) : ∃ B : Subgroup A, FactorSeed ρ C B := by
  classical
  by_cases hc : ∀ a : A, ∀ c ∈ C, ∀ d ∈ C.map (MulAut.conj a).toMonoidHom, Commute c d
  · exact ⟨C, h.factorSeed_of_commuting_conjugates hc⟩
  obtain ⟨B, hB, hfix, _⟩ := exists_exceptionalCandidate_with_fixers h (not_forall.mp hc)
  have hs := Submodule.finrank_add_eq_of_isCompl hB.split
  have hm := hB.moved_dimension
  have hzero : finrank (ZMod 2) (fixedSpace ρ B) = 0 := by omega
  have hf : fixedSpace ρ B = ⊥ := Submodule.finrank_eq_zero.mp hzero
  have htop : B = ⊤ := by
    rw [← hfix, hf]
    ext b
    simp [mem_pointwiseFixer]
  have hnormal : B.Normal := by rw [htop]; infer_instance
  let := hnormal
  refine ⟨B, hB.contained, hB.in_normalClosure, hB.split, ?_,
    Or.inr ⟨hB.cyclic_card, hB.factor_card, hB.nonabelian, hB.moved_dimension⟩⟩
  intro a ha
  exact (ha (Subgroup.Normal.map_conj_eq B a)).elim

end CFSG.Quasithin.RegularCyclicNormalClosure
