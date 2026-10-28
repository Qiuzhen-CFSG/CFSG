module

public import CFSG.Quasithin.ChapterE.Section06.FrobeniusReduction.LocalFactors.Geometry
public import CFSG.Quasithin.ChapterE.Section06.FrobeniusReduction.LocalFactors.NormalGeneration

/-!
# Exceptional two-summand geometry in E.6.25

Realize V₂ as an actual nonidentity subgroup of U. The two summands are
complementary, so its corank in V is three. The binary-overgroup input
identifies the action on V₁; pointwise fixation of V₂ then forces the full
induced centralizer into the odd Frobenius factor. Consequently V₂ belongs
to Γ and the same Q is Sylow in its full centralizer.

Source: Aschbacher–Smith, E.6.25, printed pp.255–256 (PDF pp.266–267).
-/

@[expose] public section

open Subgroup
open scoped IsMulCommutative
open Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterE.Section06.FrobeniusReduction.LocalFactors
variable {G : Type*} [Group G]

/-- The other index in a two-factor decomposition. -/
def otherIndex {n : ℕ} (hn : n = 2) (i : Fin n) : Fin n :=
  ⟨1 - i.val, by omega⟩

theorem otherIndex_ne {n : ℕ} (hn : n = 2) (i : Fin n) : i ≠ otherIndex hn i := by
  intro he
  have := congrArg Fin.val he
  simp only [otherIndex] at this
  omega

theorem eq_or_otherIndex {n : ℕ} (hn : n = 2) (i k : Fin n) :
    k = i ∨ k = otherIndex hn i := by
  by_cases he : k = i
  · exact Or.inl he
  · right
    apply Fin.ext
    have : k.val ≠ i.val := fun h => he (Fin.ext h)
    simp only [otherIndex]
    omega

variable {V U X M : Subgroup G} [IsElementaryAbelian 2 V]

/-- A summand on which the distinguished factor acts trivially lies in U. -/
theorem other_summand_le (hX : RegularCyclicSection M V U X)
    (D : Representation.RegularCyclicNormalClosure.Decomposition
      (automizerRepresentation V) (inducedAutomizer V X))
    (j : Fin D.size) (hij : D.distinguished ≠ j) :
    subspaceGroup (D.summand j) ≤ U := by
  have hXN : X ≤ normalizer (V : Set G) :=
    hX.contained.trans (inf_le_left.trans inf_le_right)
  rintro v ⟨w, hw, rfl⟩
  rw [← hX.fixed]
  refine ⟨w.property, (mem_fixedSpace_inducedAutomizer V X hXN (Additive.ofMul w)).mp ?_⟩
  intro a
  exact D.cross_fixed D.distinguished j hij a (D.contained a.property) _ hw

/-- A positive-dimensional summand is a nonidentity subgroup of G. -/
theorem subspaceGroup_ne_bot_of_finrank_pos (S : Submodule (ZMod 2) (Additive V))
    (hdim : 0 < Module.finrank (ZMod 2) S) : subspaceGroup S ≠ ⊥ := by
  intro he
  have hS : S = ⊥ := by
    apply bot_unique
    intro v hv
    have hv0 := (mem_bot.mp (he ▸ (mem_subspaceGroup S v).mpr hv))
    change v = 0
    exact congrArg Additive.ofMul (Subtype.ext hv0)
  have hzero : Module.finrank (ZMod 2) S = 0 := by
    rw [hS]
    exact finrank_bot (ZMod 2) (Additive V)
  omega

variable [Finite G] {K : GroupClass} {T : Sylow 2 G}

/-- The two independent summands are complementary once the common fixed space vanishes. -/
theorem two_summands_isCompl (h : HypothesisE61 K T M V)
    (hU : U ∈ obstructionFamily M V) (hX : RegularCyclicSection M V U X)
    (D : Representation.RegularCyclicNormalClosure.Decomposition
      (automizerRepresentation V) (inducedAutomizer V X))
    (j : Fin D.size) (hij : D.distinguished ≠ j)
    (htwo : ∀ k, k = D.distinguished ∨ k = j) :
    IsCompl (D.summand D.distinguished) (D.summand j) := by
  refine ⟨D.summands_independent.pairwiseDisjoint hij, codisjoint_iff.mpr ?_⟩
  have hs := decomposition_spans h hU
    (hX.contained.trans (inf_le_left.trans inf_le_right)) hX.fixed D
  apply top_unique
  rw [← hs]
  apply iSup_le
  intro k
  rcases htwo k with rfl | rfl
  · exact le_sup_left
  · exact le_sup_right

/-- The residual lift fixes exactly the complementary summand. -/
theorem residualLift_fixed_other (h : HypothesisE61 K T M V)
    (hU : U ∈ obstructionFamily M V) (hX : RegularCyclicSection M V U X)
    (D : Representation.RegularCyclicNormalClosure.Decomposition
      (automizerRepresentation V) (inducedAutomizer V X))
    (j : Fin D.size) (hij : D.distinguished ≠ j)
    (htwo : ∀ k, k = D.distinguished ∨ k = j)
    (ho : Odd (Nat.card (D.factor D.distinguished))) :
    V ⊓ centralizer (residualLift V (D.factor D.distinguished) : Set G) =
      subspaceGroup (D.summand j) := by
  rw [← subspaceGroup_fixedSpace _ (residualLift_le V (D.factor D.distinguished)),
    inducedAutomizer_residualLift V _ ho]
  have hXN := hX.contained.trans (inf_le_left.trans inf_le_right)
  rw [fixedSpace_factor_eq_other D
    (normalClosure_fixedSpace_eq_bot h hU hXN hX.fixed)
    (decomposition_spans h hU hXN hX.fixed D) D.distinguished j hij htwo]

/-- The source enlargement begins with the actual subgroup V₂ and its full
centralizer. The binary-overgroup input only identifies the action on V₁. -/
theorem exceptional_summand_obstruction (h : HypothesisE61 K T M V)
    (hU : U ∈ obstructionFamily M V) (hX : RegularCyclicSection M V U X)
    (D : Representation.RegularCyclicNormalClosure.Decomposition
      (automizerRepresentation V) (inducedAutomizer V X))
    (j : Fin D.size) (hij : D.distinguished ≠ j)
    (htwo : ∀ k, k = D.distinguished ∨ k = j)
    (hdim : ∀ i, Module.finrank (ZMod 2) (D.summand i) = 3)
    (hmodel : Nonempty (D.factor D.distinguished ≃* Frobenius21.Model))
    (hact : ∀ a ∈ inducedAutomizer V
        (M ⊓ centralizer (subspaceGroup (D.summand j) : Set G)),
      ∃ b ∈ D.factor D.distinguished, ∀ v ∈ D.summand D.distinguished,
        automizerRepresentation V a v = automizerRepresentation V b v) :
    subspaceGroup (D.summand j) ≤ U ∧
      subgroupCorank V (subspaceGroup (D.summand j)) = 3 ∧
      subspaceGroup (D.summand j) ∈ obstructionFamily M V ∧
      ∃ Q : Sylow 2 (centralizer (subspaceGroup (D.summand j) : Set G)),
        (Q : Subgroup (centralizer (subspaceGroup (D.summand j) : Set G))).map
          (centralizer (subspaceGroup (D.summand j) : Set G)).subtype =
            sylowCentralizer (T : Subgroup G) V := by
  have hle := other_summand_le hX D j hij
  have hne := subspaceGroup_ne_bot_of_finrank_pos (D.summand j) (by rw [hdim]; decide)
  have hc := two_summands_isCompl h hU hX D j hij htwo
  have hn := h.localCentralizer_le_normalizer hne (subspaceGroup_le (D.summand j))
  have himage := inducedAutomizer_le_of_summand_action
    (D.summand D.distinguished) (D.summand j) hc.sup_eq_top (D.factor D.distinguished)
    (D.cross_fixed D.distinguished j hij)
    (M ⊓ centralizer (subspaceGroup (D.summand j) : Set G)) hn inf_le_right hact
  have ho : Odd (Nat.card (D.factor D.distinguished)) := by
    obtain ⟨e⟩ := hmodel
    rw [Nat.card_congr e.toEquiv, Frobenius21.card_model]
    decide
  have hodd := Nat.coprime_two_left.mp (ho.coprime_two_left.of_dvd_right
    (Subgroup.card_dvd_of_le himage))
  obtain ⟨hΓ, hQ⟩ := summand_obstruction_and_sylow h hU _ hle hne hodd
  exact ⟨hle, (corank_subspaceGroup_of_isCompl _ _ hc).trans (hdim D.distinguished), hΓ, hQ⟩
end CFSG.Quasithin.ChapterE.Section06.FrobeniusReduction.LocalFactors
