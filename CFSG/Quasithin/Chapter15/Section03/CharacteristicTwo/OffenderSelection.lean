module

public import Stellmacher.ElementaryAbelianMaxOrderSpecification
public import Mathlib.Order.Minimal

/-!
# Minimal action images and the terminal Thompson containment

The source's family `B` consists of maximum elementary abelian subgroups
of `S` with minimal nonidentity action image. A finite descending argument
selects such an image below any nontrivial maximum-elementary image. If
every selected image is outside the image of `S₀`, then the Thompson
subgroup of `S₀` centralizes the module, provided `S₀` has the same maximum
elementary order as `S`. The order equality is retained explicitly: it
must follow from the paired-module replacement and offender calculation.

This proves the selection and containment steps, not the offender
classification, the equality of maximum orders, or the final normalizer
contradiction. Minimality refers to images, so it gives no unwarranted
containment between the selected subgroups in the ambient group.

Source: Aschbacher–Smith, combined manuscript (1 March 2004),
proof of Theorem 15.3.25, printed pp.1133–1134 (PDF pp.1150–1151).
-/

namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo
open Subgroup Stellmacher
variable {G H : Type*} [Group G] [Group H]

/-- The family B on p.1133: maximum elementary subgroups with minimal
nonidentity image in the specified action. Minimality concerns images,
not containment of their possibly different inverse images in S. -/
@[expose] public noncomputable def minimalNontrivialActionFamily (S : Subgroup G) (f : G →* H) :
    Set (Subgroup G) :=
  {A | A ∈ elementaryAbelianMaxSubgroups S ∧
    Minimal (fun D : Subgroup H => D ≠ ⊥ ∧
      ∃ B ∈ elementaryAbelianMaxSubgroups S, B.map f = D) (A.map f)}

variable [Finite G] [Finite H]

omit [Finite G] in
/-- Every nontrivial maximum-elementary action image contains a minimal one. -/
public theorem exists_minimal_action_image (S A : Subgroup G) (f : G →* H)
    (hA : A ∈ elementaryAbelianMaxSubgroups S) (hne : A.map f ≠ ⊥) :
    ∃ B ∈ minimalNontrivialActionFamily S f, B.map f ≤ A.map f := by
  obtain ⟨D, hDA, hD⟩ := exists_minimal_le_of_wellFoundedLT
    (fun D : Subgroup H => D ≠ ⊥ ∧
      ∃ B ∈ elementaryAbelianMaxSubgroups S, B.map f = D)
    (A.map f) ⟨hne, A, hA, rfl⟩
  obtain ⟨B, hB, rfl⟩ := hD.1.2
  exact ⟨B, ⟨hB, hD⟩, hDA⟩

omit [Finite G] in
/-- Nontrivial action of J(S) supplies the family used in the terminal argument. -/
public theorem minimal_action_family_nonempty (S : Subgroup G) (f : G →* H)
    (hJ : ¬ elementaryAbelianMaxJ S ≤ f.ker) :
    (minimalNontrivialActionFamily S f).Nonempty := by
  have hex : ∃ A ∈ elementaryAbelianMaxSubgroups S, A.map f ≠ ⊥ := by
    by_contra h
    apply hJ
    apply sSup_le
    intro A hA
    have he : A.map f = ⊥ := by
      by_contra he
      exact h ⟨A, hA, he⟩
    intro a ha
    have hh : f a ∈ A.map f := ⟨a, ha, rfl⟩
    rw [he] at hh
    exact hh
  obtain ⟨A, hA, hne⟩ := hex
  obtain ⟨B, hB, _⟩ := exists_minimal_action_image S A f hA hne
  exact ⟨B, hB⟩

/-- The Thompson containment at the end of p.1134. Equal maximum orders
transfer A(S0) into A(S); minimal-image selection then rules out every
noncentral member. The equality of orders is an explicit obligation. -/
public theorem thompson_le_kernel_of_minimal_images (S S0 : Subgroup G) (f : G →* H)
    (hS0 : S0 ≤ S)
    (horder : elementaryAbelianMaxOrder S0 = elementaryAbelianMaxOrder S)
    (hminimal : ∀ A ∈ minimalNontrivialActionFamily S f,
      ¬ A.map f ≤ S0.map f) :
    elementaryAbelianMaxJ S0 ≤ f.ker := by
  apply sSup_le
  intro A hA
  have hAS : A ∈ elementaryAbelianMaxSubgroups S := by
    refine ⟨hA.1.trans hS0, hA.2.1, ?_⟩
    intro B hBS hBe
    obtain ⟨C, hC⟩ := elementaryAbelianMaxSubgroups_nonempty S
    calc
      Nat.card B ≤ Nat.card C := hC.2.2 B hBS hBe
      _ = elementaryAbelianMaxOrder S := elementaryAbelianMaxSubgroups_card_eq S C hC
      _ = elementaryAbelianMaxOrder S0 := horder.symm
      _ = Nat.card A := (elementaryAbelianMaxSubgroups_card_eq S0 A hA).symm
  have he : A.map f = ⊥ := by
    by_contra hne
    obtain ⟨B, hB, hBA⟩ := exists_minimal_action_image S A f hAS hne
    exact hminimal B hB (hBA.trans (map_mono hA.1))
  intro a ha
  have hh : f a ∈ A.map f := ⟨a, ha, rfl⟩
  rw [he] at hh
  exact hh

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo
