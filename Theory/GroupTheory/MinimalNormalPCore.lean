module

public import Theory.GroupTheory.PGroup.CharacteristicPairReduction
public import Theory.GroupAction.MinimalNormal
public import Theory.ElementaryAbelian.AbelianNormalClosure
public import Theory.PGroupCore

/-!
# Minimal normal subgroups inside a nontrivial prime core

Choose a minimal nontrivial normal subgroup inside the first omega subgroup
of the center of the p-core. This characteristic elementary abelian group
is nontrivial by the p-group center theorem and Cauchy's theorem. Minimality
then gives an elementary abelian minimal normal subgroup of the ambient group.

Source application: Aschbacher–Smith, *The Classification of Quasithin Groups*,
combined 1 March 2004 manuscript, Proposition 2.2.2, p. 519.
-/

open Subgroup
open scoped IsMulCommutative

public theorem exists_minimal_normal_le_pCore {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (hne : pCore p G ≠ ⊥) :
    ∃ U : Subgroup G, U.Normal ∧ U ≠ ⊥ ∧ U ≤ pCore p G ∧
      IsElementaryAbelian p U ∧
      ∀ W : Subgroup G, W.Normal → W ≤ U → W = ⊥ ∨ W = U := by
  let Q := pCore p G
  let : Nontrivial Q := (nontrivial_iff_ne_bot Q).mpr hne
  let E₀ := (omega₁ (center Q) (p := p)).map (center Q).subtype
  let : (omega₁ (center Q) (p := p)).Characteristic := omega₁_characteristic _
  let : IsElementaryAbelian p (omega₁ (center Q) (p := p)) :=
    IsElementaryAbelian.omega₁_of_isMulCommutative _
  let : IsElementaryAbelian p E₀ := IsElementaryAbelian.map_subtype
  let E := E₀.map Q.subtype
  have hE : E.Normal := inferInstance
  have hEne : E ≠ ⊥ := fun h => omega_center_ne_bot (G := Q) pCore_isPGroup
    ((E₀.map_eq_bot_iff_of_injective Q.subtype_injective).mp h)
  let : IsElementaryAbelian p E := IsElementaryAbelian.map_subtype
  obtain ⟨U, ⟨hUn, hUne⟩, hUE, hmin⟩ := exists_minimal_subgroup_of_mem_le
    (fun W : Subgroup G => W.Normal ∧ W ≠ ⊥) E ⟨hE, hEne⟩
  refine ⟨U, hUn, hUne, hUE.trans (map_subtype_le _),
    IsElementaryAbelian.of_le hUE, ?_⟩
  intro W hW hWU
  by_cases hWne : W = ⊥
  · exact Or.inl hWne
  · exact Or.inr (hmin W ⟨hW, hWne⟩ hWU)
