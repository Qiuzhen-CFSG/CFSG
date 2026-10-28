module
public import CFSG.Quasithin.Chapter10.SourceA5ZeroCentralizerModule
public import Theory.GroupTheory.PGroup.DihedralCentralEnlargements
public import Theory.SpecificGroups.SymmetricFour.Surjectivity

/-!
# The Γ-kernel in the original zero-center A₅ branch

The literal source module V is T-invariant and has normalizer M. Once the four
central enlargements Γ are marked, their pointwise normalizer kernel preserves
V: its two-residual fixes every largest elementary intersection V∩F, and its
Sylow supplement already acts on V. The result is the actual containment K≤M
from the first paragraph of printed p.743.

The independent four-factor construction supplies the family, its T-permutation
marking, and the intersection orders and span. Those geometric premises are
kept explicit here; normalizer control and the desired residual action are
conclusions, not assumptions.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)

/-- The pointwise normalizer of the actual four central enlargements is
contained in the original maximal two-local M. -/
theorem source_a5_zero_normalizer_kernel_le
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hout : ¬ normalizer (ChapterB.baumann (T : Subgroup G) : Set G) ≤ D.maximalLocal)
    (hz : omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (localOrbit T L : Set G) = ⊥)
    (F : Fin 4 → Subgroup G) (E : Fin 4 → Type*) [∀ i, Group (E i)]
    [∀ i, Finite (E i)] [∀ i, IsElementaryAbelian 2 (E i)]
    (eF : ∀ i, F i ≃* DihedralGroup 4 × E i)
    (hTF : ∀ t ∈ (T : Subgroup G), ∀ i,
      ∃ j, (F i).map (MulAut.conj t).toMonoidHom = F j)
    (hcard : ∀ i, Nat.card (D.moduleSubgroup ⊓ F i : Subgroup G) = 4 * Nat.card (E i))
    (hspan : (⨆ i, D.moduleSubgroup ⊓ F i) = D.moduleSubgroup) :
    (⨅ i, normalizer (F i : Set G)) ≤ D.maximalLocal := by
  let := D.module_elementary
  exact (iInf_normalizer_le_of_dihedral_elementary_family T D.moduleSubgroup
    F E eF hTF D.sylow_normalizes_module hcard hspan).trans
      (source_a5_zero_centralizer_module_normalizer D e hn hout hz).le

/-- If the Baumann normalizer escapes M, its compatible Γ-action with the
source eight-element Sylow image is the full symmetric group. -/
theorem source_a5_zero_normalizer_action_surjective
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hout : ¬ normalizer (ChapterB.baumann (T : Subgroup G) : Set G) ≤ D.maximalLocal)
    (hz : omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (localOrbit T L : Set G) = ⊥)
    (F : Fin 4 → Subgroup G) (E : Fin 4 → Type*) [∀ i, Group (E i)]
    [∀ i, Finite (E i)] [∀ i, IsElementaryAbelian 2 (E i)]
    (eF : ∀ i, F i ≃* DihedralGroup 4 × E i)
    (hTF : ∀ t ∈ (T : Subgroup G), ∀ i,
      ∃ j, (F i).map (MulAut.conj t).toMonoidHom = F j)
    (hcard : ∀ i, Nat.card (D.moduleSubgroup ⊓ F i : Subgroup G) = 4 * Nat.card (E i))
    (hspan : (⨆ i, D.moduleSubgroup ⊓ F i) = D.moduleSubgroup)
    (f : normalizer (ChapterB.baumann (T : Subgroup G) : Set G) →* Equiv.Perm (Fin 4))
    (hf : ∀ (n : normalizer (ChapterB.baumann (T : Subgroup G) : Set G)) i, (F i).map (MulAut.conj (n : G)).toMonoidHom = F (f n i))
    (himage : Nat.card (((T : Subgroup G).subgroupOf
      (normalizer (ChapterB.baumann (T : Subgroup G) : Set G))).map f) = 8) :
    Function.Surjective f := by
  let N := normalizer (ChapterB.baumann (T : Subgroup G) : Set G)
  have hkM := source_a5_zero_normalizer_kernel_le D e hn hout hz F E eF hTF hcard hspan
  apply surjective_perm_four_of_kernel_le_and_eight_image f
    ((T : Subgroup G).subgroupOf N) (D.maximalLocal.subgroupOf N)
    (subgroupOf_mono N (le_normalizer_componentOrbit L T)) ?_ ?_ himage
  · intro n hn
    apply hkM
    apply mem_iInf.mpr
    intro i
    apply mem_normalizer_iff_map_conj_eq.mpr
    change (F i).map (MulAut.conj (n : G)).toMonoidHom = F i
    exact (hf n i).trans (by rw [show f n = 1 from hn]; rfl)
  · intro he
    apply hout
    intro n hn
    have hm : (⟨n,hn⟩ : N) ∈ D.maximalLocal.subgroupOf N := he ▸ mem_top _
    exact hm

end CFSG.Quasithin.Chapter10
