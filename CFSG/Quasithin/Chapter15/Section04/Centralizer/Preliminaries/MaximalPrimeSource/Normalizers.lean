module
public import CFSG.Quasithin.Chapter15.Section04.Centralizer.Preliminaries.MaximalPrimeSource.Preimages
public import CFSG.Quasithin.Chapter1.Section01Overgroups.Sylow
public import CFSG.KnownSimple.CarrierCatalogue

/-!
# Normalizer setup for the maximal-prime argument

A lowercase ξ member is normal in XT, which has characteristic two by
1.1.4(6). Subnormal inheritance makes its own two-core nontrivial. Its
characteristic two-core therefore puts N_G(X) in a maximal two-local M_X.
No equality between that maximal overgroup and N_G(X) is asserted.

In any overgroup of XT, O₂(M) lies in T and normalizes X. The literal
quotient image consequently recovers X as the two-residual of its full
preimage, and normalizers lift across that same quotient map.

Source: Aschbacher–Smith, combined manuscript, printed p.1157,
second paragraph of the proof of 15.4.3.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section04.MaximalPrimeSource
variable {G : Type*} [Group G] [Finite G]

/-- Characteristic two gives the nontrivial characteristic core needed to
place the entire normalizer in a two-local subgroup. -/
theorem xi_twoCore_ne_bot (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) {X : Subgroup G} (hX : X ∈ Xi (T : Subgroup G)) :
    X.pCoreIn 2 ≠ ⊥ := by
  have hne : X ≠ ⊥ := by
    intro he
    have : Subsingleton X := by rw [he]; infer_instance
    exact Xi.core_ne_top hX (Subsingleton.elim _ _)
  have hJ : X ⊔ (T : Subgroup G) ∈ Chapter1.He G :=
    Chapter1.lemma_1_1_4_6 T (hG.evenCharacteristic T) hX.2.2.1
  have hn : (X.subgroupOf (X ⊔ (T : Subgroup G))).Normal :=
    normal_subgroupOf_of_le_normalizer (sup_le X.le_normalizer hX.1)
  have hHe := Chapter1.lemma_1_1_3_1 hJ hne le_sup_left hn.isSubnormal
  intro hb
  apply hne
  apply bot_unique
  intro x hx
  have hc : x ∈ centralizer (X.pCoreIn 2 : Set G) := by
    intro y hy
    have hy1 : y = 1 := by
      change y ∈ X.pCoreIn 2 at hy
      rw [hb] at hy
      exact hy
    simp [hy1]
  exact hb ▸ hHe ⟨hx, hc⟩

/-- The source chooses a maximal two-local overgroup of the normalizer. -/
theorem exists_maximal_normalizer_overgroup
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    {X : Subgroup G} (hX : X ∈ Xi (T : Subgroup G)) :
    ∃ M_X : Subgroup G, IsMaximalTwoLocal M_X ∧
      normalizer (X : Set G) ≤ M_X ∧ X ⊔ (T : Subgroup G) ≤ M_X := by
  have hcore := xi_twoCore_ne_bot hG T hX
  have hlocal : IsTwoLocal (normalizer (X.pCoreIn 2 : Set G)) :=
    ⟨X.pCoreIn 2, hcore, isPGroup_pCoreIn 2 X, rfl⟩
  obtain ⟨M_X, hNM, hM⟩ := Finite.exists_le_maximal hlocal
  have hn : normalizer (X : Set G) ≤ M_X :=
    (normalizer_le_normalizer_characteristic_image X (pCore 2 X)).trans hNM
  exact ⟨M_X, hM, hn, (sup_le X.le_normalizer hX.1).trans hn⟩

omit [Finite G] in
private theorem quotient_kernel_normalizes (T : Sylow 2 G) {X M : Subgroup G}
    (hX : X ∈ Xi (T : Subgroup G)) (hXM : X ⊔ (T : Subgroup G) ≤ M) :
    (QuotientGroup.mk' (pCore 2 M)).ker ≤ normalizer (X.subgroupOf M : Set M) := by
  have hTM : (T : Subgroup G) ≤ M := le_sup_right.trans hXM
  have hcoreT : M.pCoreIn 2 ≤ (T : Subgroup G) := by
    simpa only [Sylow.coe_subtype, map_subgroupOf_eq_of_le hTM] using
      pCoreIn_le_sylow M (T.subtype hTM)
  rw [QuotientGroup.ker_mk', ← subgroupOf_normalizer_eq (le_sup_left.trans hXM)]
  intro x hx
  exact hX.1 (hcoreT (mem_map.mpr ⟨x, hx, rfl⟩))

omit [Finite G] in
/-- The full preimage recovers the original subgroup by O²; the map is
literally M → M/O₂(M). No normality of X in M is required. -/
theorem xi_residual_preimage (T : Sylow 2 G) {X M : Subgroup G}
    (hX : X ∈ Xi (T : Subgroup G)) (hXM : X ⊔ (T : Subgroup G) ≤ M) :
    let q := QuotientGroup.mk' (pCore 2 M)
    let P := (quotientImage M X).comap q
    (pResidual 2 P).map P.subtype = X.subgroupOf M := by
  dsimp only
  let e := subgroupOfEquivOfLe (le_sup_left.trans hXM : X ≤ M)
  have hp : IsPPerfect 2 (X.subgroupOf M) :=
    (show IsPPerfect 2 X from hX.2.1).of_surjective e.symm.toMonoidHom e.symm.surjective
  have hk : IsPGroup 2 (QuotientGroup.mk' (pCore 2 M)).ker := by
    rw [QuotientGroup.ker_mk']; exact pCore_isPGroup
  unfold quotientImage
  rw [comap_map_eq]
  exact embedded_pResidual_sup_kernel _ _ hp hk (quotient_kernel_normalizes T hX hXM)

omit [Finite G] in
/-- Both directions of the source normalizer identity in the literal quotient. -/
theorem xi_quotient_normalizers (T : Sylow 2 G) {X M : Subgroup G}
    (hX : X ∈ Xi (T : Subgroup G)) (hXM : X ⊔ (T : Subgroup G) ≤ M) :
    let q := QuotientGroup.mk' (pCore 2 M)
    (normalizer (quotientImage M X : Set (M ⧸ pCore 2 M))).comap q =
        normalizer (X.subgroupOf M : Set M) ∧
      (normalizer (X.subgroupOf M : Set M)).map q =
        normalizer (quotientImage M X : Set (M ⧸ pCore 2 M)) := by
  dsimp only
  let e := subgroupOfEquivOfLe (le_sup_left.trans hXM : X ≤ M)
  have hp : IsPPerfect 2 (X.subgroupOf M) :=
    (show IsPPerfect 2 X from hX.2.1).of_surjective e.symm.toMonoidHom e.symm.surjective
  have hk : IsPGroup 2 (QuotientGroup.mk' (pCore 2 M)).ker := by
    rw [QuotientGroup.ker_mk']; exact pCore_isPGroup
  exact ⟨comap_normalizer_map_of_pPerfect _ _ hp hk (quotient_kernel_normalizes T hX hXM),
    map_normalizer_of_pPerfect _ (QuotientGroup.mk'_surjective _) _ hp hk
      (quotient_kernel_normalizes T hX hXM)⟩
end CFSG.Quasithin.Chapter15.Section04.MaximalPrimeSource
