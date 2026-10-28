module
public import CFSG.Quasithin.ChapterD.Section02.CyclicSource.SaturatedSupport

/-!
# Actual prime supports in source D.2.23 and D.2.24

D.2.13 supplies the original prime-core commutator. The canonical-support
argument proves its normality in G and shows that it moves the whole module.
These are the literal inputs of the small binary prime-normalizer endpoint.
-/

@[expose] public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open scoped ENNReal
namespace CFSG.Quasithin.ChapterD.CyclicSource
variable {G V : Type*} [Group G] [Finite G]
  [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V)

/-- Source D.2.23 on the actual five-core commutator. -/
theorem five_core_full_support (h : Hypotheses ρ)
    {A : Subgroup G} (hA : A ∈ QhatStar ρ) (hm : ⁅pCore 5 G,A⁆ ≠ ⊥) :
    cubicRatio ρ = 2 ∧ (⁅pCore 5 G,A⁆ : Subgroup G).Normal ∧
      Nat.card (⁅pCore 5 G,A⁆ : Subgroup G) = 5 ∧
      subspaceCommutator ρ ⊤ ⁅pCore 5 G,A⁆ = ⊤ ∧ Module.finrank (ZMod 2) V = 4 := by
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  obtain ⟨hq,hc,_,hd,_⟩ := source_lemma_D_2_13_cyclic_five ρ h.faithful hA (h.rank_one A hA) hm
  have hDF : ⁅pCore 5 G,A⁆ ≤ fittingSubgroup G :=
    (commutator_le_left (pCore 5 G) A).trans (pCore_le_fitting G 5)
  obtain ⟨hn,hmove,hdim⟩ := saturated_prime_support ρ h (k := 2) (Or.inr rfl)
    (by simpa using hq) ⁅pCore 5 G,A⁆ hDF (by simpa using hc) (by simpa using hd)
  exact ⟨hq,hn,hc,hmove,hdim⟩

/-- Source D.2.24 on the actual three-core commutator, with the moved odd
prime supplied by the genuine Fitting faithfulness reduction. -/
theorem ratio_one_full_support (h : Hypotheses ρ) (hq : cubicRatio ρ = 1)
    {A : Subgroup G} (hA : A ∈ QhatStar ρ) :
    (⁅pCore 3 G,A⁆ : Subgroup G).Normal ∧
      Nat.card (⁅pCore 3 G,A⁆ : Subgroup G) = 3 ∧
      subspaceCommutator ρ ⊤ ⁅pCore 3 G,A⁆ = ⊤ ∧ Module.finrank (ZMod 2) V = 2 := by
  let : IsElementaryAbelian 2 A := hA.1.2.1.2
  obtain ⟨p,hp,ho,hm⟩ := exists_odd_primeCore_nontrivial_action h.fitting h.twoCore A
    (IsElementaryAbelian.isPGroup 2 A) hA.1.2.1.1
  let : Fact p.Prime := ⟨hp⟩
  obtain ⟨_,hc,_,hd,_⟩ := source_lemma_D_2_13_cyclic_ratio_one ρ h.faithful hA
    (h.rank_one A hA) ho hm hq
  have hDF : ⁅pCore 3 G,A⁆ ≤ fittingSubgroup G :=
    (commutator_le_left (pCore 3 G) A).trans (pCore_le_fitting G 3)
  obtain ⟨hn,hmove,hdim⟩ := saturated_prime_support ρ h (k := 1) (Or.inl rfl)
    (by simpa using hq) ⁅pCore 3 G,A⁆ hDF (by simpa using hc) (by simpa using hd)
  exact ⟨hn,hc,hmove,hdim⟩

end CFSG.Quasithin.ChapterD.CyclicSource
