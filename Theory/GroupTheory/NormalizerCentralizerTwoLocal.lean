module
public import Theory.GroupTheory.LocalNormalizerUniqueness
public import Theory.GroupTheory.MaximalTwoLocalOvergroups
public import Theory.GroupTheory.CharacteristicCentralizerFusion

/-!
# Two-local overgroups from centralizers

If a two-group A normalizes B, then A normalizes C_A(B), while B centralizes
it. A nontrivial C_A(B) therefore supplies a maximal two-local containing BA.
Likewise the full normalizer of B normalizes O₂(C_G(B)). If this core is
nontrivial, maximal two-locality identifies any maximal two-local subgroup
contained in N_G(B) with N_G(B) itself.

Source application: Aschbacher–Smith 4.3.3, printed pp.613–614. The core
hypothesis in the second assertion is essential; normality alone is insufficient.
-/

public section
open Subgroup
namespace Subgroup
variable {G : Type*} [Group G]

variable [Finite G] in
/-- A normalized two-group with nontrivial centralizer supplies an actual maximal two-local. -/
theorem local_overgroup_of_nontrivial_two_centralizer
    (B A : Subgroup G) (hp : IsPGroup 2 A)
    (hn : A ≤ normalizer (B : Set G))
    (hne : A ⊓ centralizer (B : Set G) ≠ ⊥) :
    ∃ J : Subgroup G, IsMaximalTwoLocal J ∧ B ⊔ A ≤ J := by
  let Q := A ⊓ centralizer (B : Set G)
  have hAQ : A ≤ normalizer (Q : Set G) :=
    (le_inf A.le_normalizer (hn.trans (normalizer_le_normalizer_centralizer B))).trans
      inf_normalizer_le_normalizer_inf
  have hBQ : B ≤ normalizer (Q : Set G) :=
    (le_centralizer_iff.mp (show Q ≤ centralizer (B : Set G) from inf_le_right)).trans
      (Subgroup.centralizer_le_normalizer _)
  have hlocal : IsTwoLocal (normalizer (Q : Set G)) :=
    ⟨Q,hne,hp.to_le inf_le_left,rfl⟩
  obtain ⟨J,hNJ,hJ⟩ := Finite.exists_le_maximal hlocal
  exact ⟨J,hJ,(sup_le hBQ hAQ).trans hNJ⟩

/-- A nontrivial two-core in the full centralizer makes the full normalizer local.
Maximal two-locality then identifies any maximal two-local subgroup it contains. -/
theorem normalizer_eq_of_centralizer_twoCore_ne_bot
    {H B : Subgroup G} (hH : IsMaximalTwoLocal H)
    (hHN : H ≤ normalizer (B : Set G))
    (hc : pCore 2 (centralizer (B : Set G)) ≠ ⊥) :
    H = normalizer (B : Set G) := by
  obtain ⟨J,hJ,hCJ⟩ := exists_twoLocal_overgroup_normalizer
    (centralizer (B : Set G)) (pCore 2 _) hc pCore_isPGroup
  have hNJ := (normalizer_le_normalizer_centralizer B).trans hCJ
  exact le_antisymm hHN (hNJ.trans (hH.2 hJ (hHN.trans hNJ)))

end Subgroup
