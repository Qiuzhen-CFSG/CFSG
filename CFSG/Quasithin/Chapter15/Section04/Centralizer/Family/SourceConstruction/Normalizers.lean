module

public import CFSG.Quasithin.Chapter15.Section04.Centralizer.Family.SourceConstruction.Basic

/-!
# Normalizers of the source family from quotient normality

A nontrivial normal subgroup of a group of characteristic two has nontrivial
two-core: otherwise it has trivial intersection with the ambient two-core,
centralizes that core, and is trivial. Its normalizer consequently lies in
the normalizer of a nontrivial two-group. Maximality among two-locals then
identifies the normalizer with M.

This proves the normalizer and uniqueness deductions in 15.4.12(1–2) from
normality of the actual quotient images. The remaining solvable Thompson
calculation must establish that normality for every source family member.
Even characteristic is used with its original meaning, not as an assumed
normalizer or uniqueness conclusion.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
last paragraph of the proof of Lemma 15.4.12, printed p.1161.
-/

public section
open Subgroup
namespace CFSG.Quasithin.Chapter15.Section04.FamilySource
variable {G : Type*} [Group G]

private theorem normal_core_ne_bot {H : Type*} [Group H]
    (hH : HasCharacteristicTwo H) (N : Subgroup H) [N.Normal] (hne : N ≠ ⊥) :
    pCore 2 N ≠ ⊥ := by
  intro he
  have hle : (pCore 2 H).subgroupOf N ≤ pCore 2 N :=
    le_sSup ⟨inferInstance, pCore_isPGroup.comap_subtype⟩
  have hi : N ⊓ pCore 2 H = ⊥ := by
    apply le_bot_iff.mp
    intro x hx
    have hx' : (⟨x, hx.1⟩ : N) ∈ (⊥ : Subgroup N) := he ▸ hle hx.2
    exact congrArg Subtype.val (mem_bot.mp hx')
  have hc : N ≤ centralizer (pCore 2 H : Set H) :=
    commutator_eq_bot_iff_le_centralizer.mp
      (le_bot_iff.mp ((commutator_le_inf (H₁ := N) (H₂ := pCore 2 H)).trans_eq hi))
  exact hne ((inf_eq_left.mpr (hc.trans hH)).symm.trans hi)

/-- A nontrivial relatively normal subgroup of a characteristic-two group
has nontrivial two-core in ambient coordinates. -/
theorem coreIn_ne_bot_of_normal {M X : Subgroup G}
    (hM : HasCharacteristicTwo M) (hneX : X ≠ ⊥) (hXM : X ≤ M)
    (hn : (X.subgroupOf M).Normal) : X.pCoreIn 2 ≠ ⊥ := by
  let := hn
  have hne : X.subgroupOf M ≠ ⊥ := by
    intro h
    apply hneX
    rw [← map_subgroupOf_eq_of_le hXM, h, Subgroup.map_bot]
  have hcore := normal_core_ne_bot hM (X.subgroupOf M) hne
  intro he
  have heX : pCore 2 X = ⊥ := map_injective X.subtype_injective (by
    simpa only [pCoreIn, Subgroup.map_bot] using he)
  let e := subgroupOfEquivOfLe hXM
  apply hcore
  apply map_injective (f := e.toMonoidHom) e.injective
  rw [pCore_map_iso, heX, Subgroup.map_bot]

/-- Nontriviality of the member's core follows from even characteristic and
relative normality; no Chapter 1 uniqueness theorem is assumed. -/
theorem member_core_ne_bot {T M X : Subgroup G}
    (hM : HasCharacteristicTwo M) (hX : X ∈ Y T) (hXM : X ≤ M)
    (hn : (X.subgroupOf M).Normal) : X.pCoreIn 2 ≠ ⊥ :=
  coreIn_ne_bot_of_normal hM (YFamily.ne_bot hX) hXM hn

/-- Once the actual quotient image is normal, maximal two-locality identifies
the entire ambient normalizer, not merely its intersection with M. -/
theorem member_normalizer_of_image_normal (T : Sylow 2 G) {M X : Subgroup G}
    (hM : IsMaximalTwoLocal M) (hTM : (T : Subgroup G) ≤ M)
    (hEC : HasCharacteristicTwo M) (hX : X ∈ Y (T : Subgroup G)) (hXM : X ≤ M)
    (hn : (image M X).Normal) : normalizer (X : Set G) = M := by
  have hnormal := member_normal_of_image_normal T hTM hX hXM hn
  have hMN := (normal_subgroupOf_iff_le_normalizer hXM).mp hnormal
  have hcore := member_core_ne_bot hEC hX hXM hnormal
  have hncore : normalizer (X : Set G) ≤ normalizer (X.pCoreIn 2 : Set G) :=
    normalizer_le_normalizer_characteristic_image X (pCore 2 X)
  have hlocal : IsTwoLocal (normalizer (X.pCoreIn 2 : Set G)) :=
    ⟨X.pCoreIn 2, hcore, isPGroup_pCoreIn 2 X, rfl⟩
  exact le_antisymm (hncore.trans (hM.2 hlocal (hMN.trans hncore))) hMN

/-- The source uniqueness conclusion follows by applying the same quotient
normality calculation in every maximal two-local overgroup of XT. -/
theorem member_unique_of_images_normal (T : Sylow 2 G) (hEC : IsEvenCharacteristicAt T)
    {M X : Subgroup G} (hM : IsMaximalTwoLocal M)
    (hTM : (T : Subgroup G) ≤ M) (hX : X ∈ Y (T : Subgroup G)) (hXM : X ≤ M)
    (hn : ∀ N : Subgroup G, IsMaximalTwoLocal N → X ⊔ (T : Subgroup G) ≤ N →
      (image N X).Normal) :
    normalizer (X : Set G) = M ∧
      ∀ N : Subgroup G, IsMaximalTwoLocal N → X ⊔ (T : Subgroup G) ≤ N → N = M := by
  have hm := member_normalizer_of_image_normal T hM hTM (hEC M hM hTM) hX hXM
    (hn M hM (sup_le hXM hTM))
  refine ⟨hm, fun N hN hXN => ?_⟩
  have hTN : (T : Subgroup G) ≤ N := le_sup_right.trans hXN
  exact (member_normalizer_of_image_normal T hN hTN (hEC N hN hTN) hX
    (le_sup_left.trans hXN) (hn N hN hXN)).symm.trans hm

end CFSG.Quasithin.Chapter15.Section04.FamilySource
