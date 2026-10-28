module

public import CFSG.Quasithin.ChapterA.Section04.Signalizers.Subnormal
public import Theory.GroupTheory.PGroup.SubnormalCore

/-!
# Comparing signalizers across two core-product decompositions

Subnormal core monotonicity makes the join of O₂(X) with a Y-signalizer
a two-group. The decomposition of X makes this join an X-signalizer,
putting the original subgroup in C_M(X/O₂(X)). Applying this to O₂(Y)
and using the decomposition of Y proves that Y normalizes X. Sylow
extension in the section centralizer then gives inclusion of maximal
signalizer families. The final theorem retains both source set products.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*,
A.4.3, printed pp. 57–58.
-/

public section

open Subgroup
open scoped Pointwise
namespace CFSG.Quasithin.ChapterA.Section04
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
private theorem actor_normalizes_core (X : Subgroup G) :
    X ≤ normalizer (X.pCoreIn 2 : Set G) :=
  le_normalizer.trans (normalizer_le_normalizer_characteristic_image X (pCore 2 X))

/-- The centralizer assertion of A.4.3(1). -/
theorem signalizer_le_section_of_core_join (X Y M B : Subgroup G)
    (hXM : X ≤ M) (hsub : (X.subgroupOf M).IsSubnormal) (hX : IsPPerfect 2 X)
    (hjoinX : X = (X ⊓ Y) ⊔ X.pCoreIn 2) (hB : IsTwoSignalizer Y M B) :
    B ≤ twoSectionCentralizer X M := by
  let C := X.pCoreIn 2 ⊔ B
  have hcore : X.pCoreIn 2 ≤ M.pCoreIn 2 :=
    pCoreAmbient_mono_of_isSubnormalIn X M 2 hXM hsub
  have hCp : IsPGroup 2 C := by
    have hp := (isPGroup_pCoreIn 2 M).to_sup_of_normal_left' hB.isPGroup
      (hB.le.trans (actor_normalizes_core M))
    exact hp.to_le (sup_le_sup hcore le_rfl)
  have hNC : X ⊓ Y ≤ normalizer (C : Set G) :=
    (le_inf (inf_le_left.trans (actor_normalizes_core X))
      (inf_le_right.trans hB.normalizes)).trans
      (normalizer_inf_normalizer_le_normalizer_sup _ _)
  have hC : IsTwoSignalizer X M C := by
    apply (isTwoSignalizer_iff _ _ _).mpr
    refine ⟨sup_le ((pCoreIn_le 2 X).trans hXM) hB.le, hCp, ?_⟩
    rw [hjoinX]
    exact sup_le hNC (le_sup_left.trans le_normalizer)
  exact le_sup_right.trans (signalizer_le_twoSectionCentralizer X M C hXM hsub hX hC)

/-- Both source equalities imply the normalization assertion of A.4.3(1). -/
theorem normalizes_of_core_joins (X Y M : Subgroup G)
    (hXM : X ≤ M) (hYM : Y ≤ M)
    (hsub : (X.subgroupOf M).IsSubnormal) (hX : IsPPerfect 2 X)
    (hjoinY : Y = (X ⊓ Y) ⊔ Y.pCoreIn 2)
    (hjoinX : X = (X ⊓ Y) ⊔ X.pCoreIn 2) :
    Y ≤ normalizer (X : Set G) := by
  have hcore : IsTwoSignalizer Y M (Y.pCoreIn 2) :=
    (isTwoSignalizer_iff _ _ _).mpr
      ⟨(pCoreIn_le 2 Y).trans hYM, isPGroup_pCoreIn 2 Y, actor_normalizes_core Y⟩
  have hc := (signalizer_le_section_of_core_join X Y M _ hXM hsub hX hjoinX hcore).trans
    (twoSectionCentralizer_le_normalizer X M)
  rw [hjoinY]
  exact sup_le (inf_le_left.trans le_normalizer) hc

omit [Finite G] in
/-- A maximal signalizer contains the two-core of its actor. -/
theorem actor_core_le_maximal_signalizer (Y M B : Subgroup G) (hYM : Y ≤ M)
    (hB : IsMaximalTwoSignalizer Y M B) : Y.pCoreIn 2 ≤ B := by
  have hm := (isMaximalTwoSignalizer_iff _ _ _).mp hB
  have hS : IsTwoSignalizer Y M (Y.pCoreIn 2 ⊔ B) := by
    apply (isTwoSignalizer_iff _ _ _).mpr
    exact ⟨sup_le ((pCoreIn_le 2 Y).trans hYM) hm.1.le,
      (isPGroup_pCoreIn 2 Y).to_sup_of_normal_right' hm.1.isPGroup
        ((pCoreIn_le 2 Y).trans hm.1.normalizes),
      (le_inf (actor_normalizes_core Y) hm.1.normalizes).trans
        (normalizer_inf_normalizer_le_normalizer_sup _ _)⟩
  exact le_sup_left.trans (hm.2 _ hS le_sup_right)

/-- Inclusion of maximal signalizer families, A.4.3(2). -/
theorem maximal_signalizer_of_core_joins (X Y M B : Subgroup G)
    (hXM : X ≤ M) (hYM : Y ≤ M)
    (hsub : (X.subgroupOf M).IsSubnormal) (hX : IsPPerfect 2 X)
    (hjoinY : Y = (X ⊓ Y) ⊔ Y.pCoreIn 2)
    (hjoinX : X = (X ⊓ Y) ⊔ X.pCoreIn 2)
    (hB : IsMaximalTwoSignalizer Y M B) : IsMaximalTwoSignalizer X M B := by
  have hm := (isMaximalTwoSignalizer_iff _ _ _).mp hB
  have hBC := signalizer_le_section_of_core_join X Y M B hXM hsub hX hjoinX hm.1
  obtain ⟨S, hBS⟩ := (hm.1.isPGroup.comap_subtype :
    IsPGroup 2 (B.subgroupOf (twoSectionCentralizer X M))).exists_le_sylow
  let U := (S : Subgroup (twoSectionCentralizer X M)).map (twoSectionCentralizer X M).subtype
  have hBU : B ≤ U := by
    intro b hb
    exact ⟨⟨b, hBC hb⟩, hBS hb, rfl⟩
  have hUX := sylow_twoSectionCentralizer_isSignalizer X M hXM S
  have hUY : IsTwoSignalizer Y M U := by
    apply (isTwoSignalizer_iff _ _ _).mpr
    refine ⟨hUX.le, hUX.isPGroup, ?_⟩
    rw [hjoinY]
    exact sup_le (inf_le_left.trans hUX.normalizes)
      ((actor_core_le_maximal_signalizer Y M B hYM hB).trans (hBU.trans le_normalizer))
  have he : U = B := le_antisymm (hm.2 _ hUY hBU) hBU
  exact (maximal_signalizer_iff_sylow X M B hXM hsub hX).mpr ⟨S, he⟩
/-- A.4.3 with both of the source's set-product equalities. The section
centralizer includes normalization of X in its definition. -/
theorem signalizer_comparison (X Y M : Subgroup G)
    (hXM : X ≤ M) (hYM : Y ≤ M)
    (hsub : (X.subgroupOf M).IsSubnormal) (hX : IsPPerfect 2 X)
    (hprodY : (Y : Set G) = ((X ⊓ Y : Subgroup G) : Set G) * (Y.pCoreIn 2 : Set G))
    (hprodX : (X : Set G) = ((X ⊓ Y : Subgroup G) : Set G) * (X.pCoreIn 2 : Set G)) :
    (∀ B, IsTwoSignalizer Y M B → B ≤ twoSectionCentralizer X M) ∧
      Y ≤ normalizer (X : Set G) ∧
      ∀ B, IsMaximalTwoSignalizer Y M B → IsMaximalTwoSignalizer X M B := by
  have hjoinY : Y = (X ⊓ Y) ⊔ Y.pCoreIn 2 := by
    apply SetLike.coe_injective
    rw [coe_sup_of_set_mul_comm _ _ (set_mul_normalizer_comm _ _
      (inf_le_right.trans (actor_normalizes_core Y)))]
    exact hprodY
  have hjoinX : X = (X ⊓ Y) ⊔ X.pCoreIn 2 := by
    apply SetLike.coe_injective
    rw [coe_sup_of_set_mul_comm _ _ (set_mul_normalizer_comm _ _
      (inf_le_left.trans (actor_normalizes_core X)))]
    exact hprodX
  exact ⟨fun B hB => signalizer_le_section_of_core_join X Y M B hXM hsub hX hjoinX hB,
    normalizes_of_core_joins X Y M hXM hYM hsub hX hjoinY hjoinX,
    fun B hB => maximal_signalizer_of_core_joins X Y M B hXM hYM hsub hX hjoinY hjoinX hB⟩
end CFSG.Quasithin.ChapterA.Section04

end
