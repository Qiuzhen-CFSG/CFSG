module

public import CFSG.Quasithin.ChapterF.Section06.Basic
public import Theory.GroupTheory.SylowSubnormalIntersection
public import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
# Sylow intersections and the odd quotient of a normal subgroup

Restrict the common Sylow subgroup to an arbitrary subnormal subgroup.
If a local intersection lies in its local two-core, the three intersections
in F.6.7(2) coincide. If both containments hold for an ambient normal subgroup
X, the common-normal-core theorem places `T ∩ X` in `O₂(G)`. This identifies
the kernel intersection with a Sylow subgroup of X, making `XO₂(G)/O₂(G)`
odd by the Sylow index theorem and the second isomorphism theorem.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*,
F.6.7(1)–(2) and the order assertion of F.6.8, printed p.305.
-/

open Subgroup
namespace CFSG.Quasithin.ChapterF
variable {G : Type*} [Group G] [Finite G] {G₁ G₂ : Subgroup G}

public theorem IsGoldschmidtTriple.subnormal_intersection_sylow
    (h : IsGoldschmidtTriple G₁ G₂) (X : Subgroup G) (hX : X.IsSubnormal) :
    ∃ S : Sylow 2 X, (S : Subgroup X) = (G₁ ⊓ G₂).subgroupOf X := by
  obtain ⟨T, hT⟩ := h.intersection_sylow
  rw [hT]
  exact T.exists_subgroupOf_eq_of_subnormal X hX

public theorem IsGoldschmidtTriple.left_intersection_eq_core_intersection
    (h : IsGoldschmidtTriple G₁ G₂) (X : Subgroup G)
    (hle : G₁ ⊓ X ≤ (pCore 2 G₁).map G₁.subtype) :
    G₁ ⊓ X = (pCore 2 G₁).map G₁.subtype ⊓ X ∧
    (pCore 2 G₁).map G₁.subtype ⊓ X = (G₁ ⊓ G₂) ⊓ X := by
  have hlocal := h.local_twoCore_le_intersection
  constructor
  · exact le_antisymm (le_inf hle inf_le_right)
      (inf_le_inf (map_subtype_le _) le_rfl)
  · exact le_antisymm (inf_le_inf hlocal le_rfl)
      (le_inf ((inf_le_inf inf_le_left le_rfl).trans hle) inf_le_right)

public theorem IsGoldschmidtTriple.left_subnormal_intersection_iff
    (h : IsGoldschmidtTriple G₁ G₂) (X : Subgroup G) (hX : X.IsSubnormal) :
    (G₁ ⊓ X ≤ (pCore 2 G₁).map G₁.subtype) ↔
      (G₁ ⊓ X = (pCore 2 G₁).map G₁.subtype ⊓ X ∧
        (pCore 2 G₁).map G₁.subtype ⊓ X = (G₁ ⊓ G₂) ⊓ X ∧
        ∃ S : Sylow 2 X, (S : Subgroup X) = (G₁ ⊓ G₂).subgroupOf X) := by
  constructor
  · intro hle
    obtain ⟨he₁, he₂⟩ := h.left_intersection_eq_core_intersection X hle
    exact ⟨he₁, he₂, h.subnormal_intersection_sylow X hX⟩
  · rintro ⟨he₁, _, _⟩
    exact he₁.le.trans inf_le_left

public theorem IsGoldschmidtTriple.normal_twoCore_intersection_eq
    (h : IsGoldschmidtTriple G₁ G₂) (X : Subgroup G) [X.Normal]
    (h₁ : G₁ ⊓ X ≤ (pCore 2 G₁).map G₁.subtype)
    (h₂ : G₂ ⊓ X ≤ (pCore 2 G₂).map G₂.subtype) :
    pCore 2 G ⊓ X = (G₁ ⊓ G₂) ⊓ X := by
  exact le_antisymm (inf_le_inf h.twoCore_isGreatest.1.1 le_rfl)
    (le_inf (h.normal_intersection_le_twoCore X h₁ h₂) inf_le_right)

public theorem IsGoldschmidtTriple.normal_quotient_odd
    (h : IsGoldschmidtTriple G₁ G₂) (X : Subgroup G) [X.Normal]
    (h₁ : G₁ ⊓ X ≤ (pCore 2 G₁).map G₁.subtype)
    (h₂ : G₂ ⊓ X ≤ (pCore 2 G₂).map G₂.subtype) :
    Odd (Nat.card ((X ⊔ pCore 2 G : Subgroup G) ⧸
      (pCore 2 G).subgroupOf (X ⊔ pCore 2 G))) := by
  obtain ⟨T, hT⟩ := h.intersection_sylow
  obtain ⟨S, hS⟩ := T.exists_subgroupOf_eq_of_normal X
  have he : (pCore 2 G).subgroupOf X = (S : Subgroup X) := by
    apply map_injective X.subtype_injective
    rw [subgroupOf_map_subtype, hS, subgroupOf_map_subtype,
      h.normal_twoCore_intersection_eq X h₁ h₂, hT]
  have hind : ¬ 2 ∣ Nat.card (X ⧸ (pCore 2 G).subgroupOf X) := by
    change ¬ 2 ∣ ((pCore 2 G).subgroupOf X).index
    rw [he]
    exact S.not_dvd_index
  have hodd : Odd (Nat.card (X ⧸ (pCore 2 G).subgroupOf X)) := by
    exact Nat.not_even_iff_odd.mp (by simpa only [even_iff_two_dvd] using hind)
  rwa [Nat.card_congr (QuotientGroup.quotientInfEquivProdNormalQuotient
    X (pCore 2 G)).toEquiv] at hodd

end CFSG.Quasithin.ChapterF
