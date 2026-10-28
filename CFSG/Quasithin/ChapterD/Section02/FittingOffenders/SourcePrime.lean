module
public import CFSG.Quasithin.ChapterD.Section02.FittingOffenders.NoncyclicSupport
/-!
# The source prime and five-core conclusions of D.2.13

Split the original starred actor according to its rank. The checked cyclic
calculation gives the complete order-five action and complement. A noncyclic
actor moves only the three-core, so the five conclusion is vacuous there.
This assembles clauses (1)--(2) without any Fitting-equality assumption.

Source: Aschbacher--Smith, combined manuscript of 1 March 2004,
D.2.13(1)--(2), printed pp.184--185.
-/

public section
namespace CFSG.Quasithin.ChapterD
open Representation.BinaryOffender Subgroup
open scoped IsMulCommutative
variable {G V : Type*} [Group G] [Finite G]
  [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V)

theorem source_lemma_D_2_13_one_two
    (hf : Function.Injective ρ) {A : Subgroup G} (hA : A ∈ QhatStar ρ)
    {p : ℕ} [Fact p.Prime] (hp : Odd p) (hm : ⁅pCore p G, A⁆ ≠ ⊥) :
    (p = 3 ∨ p = 5) ∧ (p = 5 → cubicRatio ρ = 2 ∧ rank A = 1 ∧
      Nonempty ((⁅pCore p G, A⁆ : Subgroup G) ≃* Multiplicative (ZMod 5)) ∧
      IsCompl (subspaceCommutator ρ ⊤ ⁅pCore p G, A⁆)
        (fixedSpace ρ (⁅pCore p G, A⁆ ⊔ A)) ∧
      Module.finrank (ZMod 2) (subspaceCommutator ρ ⊤ ⁅pCore p G, A⁆) = 4) := by
  have hpos := hA.1.2.1.rank_pos
  by_cases hr : rank A = 1
  · refine ⟨(source_lemma_D_2_13_cyclic_prime ρ hf hA hr hp hm).1, ?_⟩
    intro he
    subst p
    obtain ⟨hq, _, he, hd, hc⟩ := source_lemma_D_2_13_cyclic_five ρ hf hA hr hm
    exact ⟨hq, hr, he, hc, hd⟩
  · have he := source_lemma_D_2_13_noncyclic_prime ρ hf hA (by omega) hp hm
    exact ⟨Or.inl he, fun h => by omega⟩
end CFSG.Quasithin.ChapterD
