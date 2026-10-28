module

public import CFSG.Quasithin.Chapter2.Section01To03.ComponentRefinement.SurvivingIntersections.MathieuCovers.Quotient
public import CFSG.Quasithin.Chapter2.Section01To03.Selection.Maximal
public import Theory.GroupTheory.LocalNormalizerUniqueness

/-!
# Ambient normalizer obstructions for a component's central two-kernel

Source: Aschbacher–Smith 2.3.7(2,4), printed p.523, and the setup of
2.3.9, printed pp.525–526. A nontrivial two-subgroup centralized by L
cannot have its normalizer contain a Sylow subgroup of M: the unique
maximal two-local hypothesis would put that normalizer, and hence L, in M.
The final theorem applies this to the literal embedded `O₂(L)`.

There is also an obstruction using Γ₀ maximality: if H normalizes a
nontrivial two-subgroup D, its normalizer cannot contain a two-subgroup
strictly larger than the original S. This uses both starred selections
through the proved `gammaZero_overgroup` theorem.

These are restrictions on the actual ambient normalizers. They do not
assert that a nontrivial M₂₂ covering kernel has either normalization
property. Establishing that implication is the remaining M₂₂ obligation.
-/

public section
namespace CFSG.Quasithin.Chapter2.ComponentRefinement
open Subgroup Theory.GroupTheory
variable {G : Type*} [Group G]
variable {H L M : Subgroup G} {S : Sylow 2 H} {z : G}

/-- Uniqueness above an ambient Sylow forbids a Sylow of M from normalizing
any nontrivial two-subgroup centralized by the component outside M. -/
theorem LocalSetup.centralTwoSubgroup_not_normalized_by_sylow
    (h : LocalSetup H L M S z) (T : Sylow 2 G)
    (hTM : (T : Subgroup G) ≤ M)
    (hunique : ∀ K : Subgroup G, IsMaximalTwoLocal K → (T : Subgroup G) ≤ K → K = M)
    (P : Sylow 2 M) (D : Subgroup G) (hD : D ≠ ⊥) (hp : IsPGroup 2 D)
    (hc : L ≤ centralizer (D : Set G)) :
    ¬ (P : Subgroup M).map M.subtype ≤ normalizer (D : Set G) := by
  let := h.finite
  intro hPN
  have hN : normalizer (D : Set G) ≤ M :=
    core_overgroup_le_of_sylow T hTM hunique
      (Chapter1.mem_H_of_isTwoLocal ⟨D, hD, hp, rfl⟩) P hPN
  exact h.outside (hc.trans ((centralizer_le_normalizer _).trans hN))

/-- Actual application of the ambient normalizer obstruction to the kernel
of `componentQuotientCover`. No normalization is inferred from innerness. -/
theorem LocalSetup.twoCore_not_normalized_by_sylow
    (h : LocalSetup H L M S z) (T : Sylow 2 G)
    (hTM : (T : Subgroup G) ≤ M)
    (hunique : ∀ K : Subgroup G, IsMaximalTwoLocal K → (T : Subgroup G) ≤ K → K = M)
    (P : Sylow 2 M) (hk : pCore 2 L ≠ ⊥) :
    ¬ (P : Subgroup M).map M.subtype ≤ normalizer (twoCore L : Set G) := by
  let := h.finite
  let := h.quasisimple
  apply h.centralTwoSubgroup_not_normalized_by_sylow T hTM hunique P (twoCore L)
  · exact fun he => hk ((map_eq_bot_iff_of_injective _ L.subtype_injective).mp he)
  · exact pCore_isPGroup.map L.subtype
  · intro x hx d hd
    obtain ⟨a, ha, rfl⟩ := hd
    exact congrArg Subtype.val
      (mem_center_iff.mp (IsQuasisimple.pCore_le_center 2 ha) ⟨x, hx⟩).symm

/-- Γ₀ maximality rules out a larger two-group in the normalizer of a
nontrivial two-subgroup already normalized by the whole H. -/
theorem LocalSetup.no_larger_twoSubgroup_in_normalizer
    (h : LocalSetup H L M S z) (hgamma : H ∈ gammaZero (Chapter1.He G) M)
    (D : Subgroup G) (hD : D ≠ ⊥) (hp : IsPGroup 2 D)
    (hHD : H ≤ normalizer (D : Set G))
    (V : Subgroup G) (hV : IsPGroup 2 V)
    (hSV : (S : Subgroup H).map H.subtype < V) :
    ¬ V ≤ normalizer (D : Set G) := by
  let := h.finite
  intro hVN
  let N := normalizer (D : Set G)
  have hcore : twoCore N ≠ ⊥ := Chapter1.mem_H_of_isTwoLocal ⟨D, hD, hp, rfl⟩
  have hg := gammaZero_overgroup hgamma hHD hcore
  have hNgamma : N ∈ gamma (Chapter1.He G) M :=
    hg.1.elim (fun a => a.1.1) (fun a => a.1)
  obtain ⟨P, hP⟩ := (gamma_sylow_transport hNgamma S
    ((map_subtype_le _).trans hHD) hg.2.1 h.sylow_le).1
  have hv := inf_eq_sylow_map P hV (hP.symm ▸ hSV.le)
  rw [inf_eq_left.mpr hVN, hP] at hv
  exact hSV.ne hv.symm

/-- The Γ₀ obstruction for the original component kernel. Normalization
of L by H suffices to normalize its characteristic two-core; normalization
by a larger two-group is a conclusion ruled out here, not a setup field. -/
theorem LocalSetup.twoCore_no_larger_normalizer_of_normalized_component
    (h : LocalSetup H L M S z) (hgamma : H ∈ gammaZero (Chapter1.He G) M)
    (hHL : H ≤ normalizer (L : Set G)) (hk : pCore 2 L ≠ ⊥)
    (V : Subgroup G) (hV : IsPGroup 2 V)
    (hSV : (S : Subgroup H).map H.subtype < V) :
    ¬ V ≤ normalizer (twoCore L : Set G) := by
  apply h.no_larger_twoSubgroup_in_normalizer hgamma (twoCore L)
    (fun he => hk ((map_eq_bot_iff_of_injective _ L.subtype_injective).mp he))
    (pCore_isPGroup.map L.subtype) _ V hV hSV
  exact hHL.trans (Subgroup.normalizer_le_normalizer_characteristic_image L (pCore 2 L))

end CFSG.Quasithin.Chapter2.ComponentRefinement
end
