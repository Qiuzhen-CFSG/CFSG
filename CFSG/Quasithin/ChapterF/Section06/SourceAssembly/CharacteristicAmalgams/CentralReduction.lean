module

public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.CharacteristicAmalgams.CosetKernel
public import Stellmacher.SectionFiveToSeven.Defs
public import Theory.GroupTheory.PGroup.CharacteristicPairReduction

/-!
# The omega center cannot centralize both Goldschmidt vertices

The common Sylow subgroup has even order, so the subgroup of its central
involutions is nontrivial. If both vertices centralized it, this subgroup
would be normal in both generators and would lie in the ambient two-core.
Thus the remaining central-vertex branch has exactly one centralizing side.

Source: the faithful-amalgam reduction in Aschbacher–Smith F.6.3–F.6.5,
printed pp.304–305; compare the central/noncentral split in Stellmacher §7.
-/

public section
open Subgroup Theory.GroupTheory
open Stellmacher.SectionsFiveToSeven
namespace CFSG.Quasithin.ChapterF
variable {G : Type*} [Group G] [Finite G] {G₁ G₂ : Subgroup G}

/-- At least one original vertex moves the actual common Sylow omega center. -/
theorem IsGoldschmidtTriple.omega_center_moved
    (h : IsGoldschmidtTriple G₁ G₂) (hcore : pCore 2 G = ⊥) :
    ⁅G₁, omegaOneCenter (G₁ ⊓ G₂)⁆ ≠ ⊥ ∨
      ⁅G₂, omegaOneCenter (G₁ ⊓ G₂)⁆ ≠ ⊥ := by
  classical
  let T := G₁ ⊓ G₂
  let W := omegaOneCenter T
  have hTcard : 2 ≤ Nat.card T := by
    have hc := SymmetricThreeTwoCore.card_eq h.quotient_left.some
    have ht := h.local_card_eq_three_mul_intersection
    have hp := Nat.card_pos (α := pCore 2 G₁)
    change 2 ≤ Nat.card (G₁ ⊓ G₂ : Subgroup G)
    omega
  have hTne : T ≠ ⊥ := by intro he; rw [he,card_bot] at hTcard; omega
  let : Nontrivial T := (Subgroup.nontrivial_iff_ne_bot T).mpr hTne
  have hTp : IsPGroup 2 T := by
    obtain ⟨S,hS⟩ := h.intersection_sylow
    change IsPGroup 2 (G₁ ⊓ G₂ : Subgroup G)
    rw [hS]
    exact S.isPGroup'
  have hWne : W ≠ ⊥ := by
    intro he
    apply omega_center_ne_bot hTp
    apply map_injective T.subtype_injective
    simpa only [W,omegaOneCenter,Subgroup.map_bot] using he
  have hWT : W ≤ T := map_subtype_le _
  by_contra! hh
  have hn₁ : G₁ ≤ normalizer (W : Set G) :=
    (commutator_eq_bot_iff_le_centralizer.mp hh.1).trans (Subgroup.centralizer_le_normalizer _)
  have hn₂ : G₂ ≤ normalizer (W : Set G) :=
    (commutator_eq_bot_iff_le_centralizer.mp hh.2).trans (Subgroup.centralizer_le_normalizer _)
  exact hWne (h.common_normal_eq_bot hcore W hWT
    (normal_subgroupOf_of_le_normalizer hn₁) (normal_subgroupOf_of_le_normalizer hn₂))

end CFSG.Quasithin.ChapterF
