module

public import CFSG.Quasithin.ChapterG.Section06.Source
public import Theory.Representation.ResidualMovedGeneration

/-!
# Modules with displacement rank at most two: the elementary reductions

This module proves all three parts of G.6.2 and the G.6.3 trichotomy.
Conjugate generation propagates containment or fixation from the seed;
otherwise rank-nullity forces rank one on both the invariant subspace and
its literal quotient. The full G.6.4 classification remains a separate
assembly obligation, with its exact marked conclusion in `Source.lean`.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
G.6.1–G.6.4, printed pp.345–346 (PDF pp.356–357).
-/

public section

namespace CFSG.Quasithin.ChapterG.Section06
open Subgroup Representation.BinaryOffender
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V) (a : G)

/-- G.6.2(1): the source displacement-orbit hypothesis gives V = [V,K]. -/
theorem lemma_G_6_2_1
    (hspan : conjugateDisplacementSpan ρ a ⊤ = ⊤) :
    subspaceCommutator ρ ⊤ (normalClosure ({a} : Set G)) = ⊤ := by
  rw [← conjugateSpanBy_zpowers_top, commutator_conjugateSpanBy_zpowers, hspan]

/-- G.6.2(3), with the literal relative conjugate closure. -/
theorem lemma_G_6_2_3
    (hspan : conjugateDisplacementSpan ρ a ⊤ = ⊤)
    (H : Subgroup G)
    (hgen : conjugateSpanBy (zpowers a) H = normalClosure ({a} : Set G))
    (U : Submodule (ZMod 2) V) (hU : H ≤ subspaceStabilizer ρ U)
    (ha : LinearMap.range (ρ a - LinearMap.id) ≤ U) : U = ⊤ := by
  apply top_unique
  rw [← lemma_G_6_2_1 ρ a hspan, ← hgen]
  exact commutator_conjugateSpanBy_le ρ a H U hU ha

/-- G.6.2(2): O²(K) denotes the residual, embedded from K into G. -/
theorem lemma_G_6_2_2 [Finite G] [FiniteDimensional (ZMod 2) V]
    (hspan : conjugateDisplacementSpan ρ a ⊤ = ⊤) :
    subspaceCommutator ρ ⊤
      ((pResidual 2 (normalClosure ({a} : Set G))).map
        (normalClosure ({a} : Set G)).subtype) = ⊤ :=
  commutator_pResidual_eq_top ρ _ (lemma_G_6_2_1 ρ a hspan)

/-- G.6.3. The two rank-one spaces in the final alternative are precisely
[U,a] (as a subspace of V) and [V/U,a] (as a subspace of the actual quotient).
For the source involution, these are the two transvection assertions. -/
theorem lemma_G_6_3 [FiniteDimensional (ZMod 2) V]
    (hspan : conjugateDisplacementSpan ρ a ⊤ = ⊤)
    (hrank : Module.finrank (ZMod 2) (LinearMap.range (ρ a - LinearMap.id)) ≤ 2)
    (U : Submodule (ZMod 2) V)
    (hU : normalClosure ({a} : Set G) ≤ subspaceStabilizer ρ U)
    (hchoice : conjugateSpanBy (zpowers a) (normalClosure ({a} : Set G)) =
        normalClosure ({a} : Set G) ∨ ⊤ ≤ subspaceStabilizer ρ U) :
    subspaceCommutator ρ U (normalClosure ({a} : Set G)) = ⊥ ∨ U = ⊤ ∨
      (Module.finrank (ZMod 2) (U.map (ρ a - LinearMap.id)) = 1 ∧
        Module.finrank (ZMod 2)
          ((LinearMap.range (ρ a - LinearMap.id)).map U.mkQ) = 1) := by
  classical
  obtain ⟨H, hHgen, hHU⟩ : ∃ H : Subgroup G,
      conjugateSpanBy (zpowers a) H = normalClosure ({a} : Set G) ∧
      H ≤ subspaceStabilizer ρ U := by
    rcases hchoice with h | h
    · exact ⟨normalClosure ({a} : Set G), h, hU⟩
    · exact ⟨⊤, conjugateSpanBy_zpowers_top a, h⟩
  by_cases hmove : U.map (ρ a - LinearMap.id) = ⊥
  · left
    rw [← hHgen]
    apply fixedSpace_conjugateSpanBy ρ a H U hHU
    intro v hv
    have hm : ρ a v - v ∈ U.map (ρ a - LinearMap.id) := ⟨v, hv, rfl⟩
    rw [hmove, Submodule.mem_bot] at hm
    exact sub_eq_zero.mp hm
  by_cases hquot : LinearMap.range (ρ a - LinearMap.id) ≤ U
  · exact Or.inr (Or.inl (lemma_G_6_2_3 ρ a hspan H hHgen U hHU hquot))
  · right; right
    apply LinearMap.rank_one_on_subspace_and_quotient _ U _ hmove hquot hrank
    rintro _ ⟨v, hv, rfl⟩
    exact U.sub_mem ((hU (subset_normalClosure (Set.mem_singleton a)) v).2 hv) hv
end CFSG.Quasithin.ChapterG.Section06
