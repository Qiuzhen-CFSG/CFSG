module
public import Theory.Representation.BinaryConjugationSection.FixedQuotientIndex
public import Theory.Representation.RankOne.QuadraticRecognition.ElementFixedSpaces

/-!
# Individual fixed subgroups at a sharp linear-section index

In a faithful binary SL₂ section, any nonidentity element of a Sylow actor
moves at least one field degree. If the whole actor has exactly that
centralizer index on the original numerator, its centralizer coincides with
the centralizer of every element surviving the actor kernel. The proof uses
the literal coordinate map and retains its denominator; no splitting or
fixed-point lifting is assumed.

Source application: Delgado--Goldschmidt--Stellmacher, Groups and Graphs
(1985), 9.11, printed p.151, using the natural-module fixed-space properties
on p.113. ElementCentralizers applies this to both actual critical sections.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender
open Representation.RankOne.QuadraticRecognition
open scoped MatrixGroups
namespace Representation.BinaryConjugationSection
variable {G F W : Type*} [Group G] [Field F] [Finite F] [CharP F 2]
  [AddCommGroup W] [Module (ZMod 2) W]

/-- Sharpness of the full actor index identifies every nontrivial element centralizer. -/
theorem element_centralizer_eq_of_sharp_linear_index
    {H U K : Subgroup G} [Finite U]
    (q : H →* SL(2,F)) (σ : Representation (ZMod 2) SL(2,F) W)
    (c : BinaryConjugationSection H U K (σ.comp q))
    (hf : Function.Injective σ) (T : Sylow 2 SL(2,F))
    {n : ℕ} (hF : Nat.card F = 2^n)
    (A : Subgroup G) (hAH : A ≤ H) (hAT : (A.subgroupOf H).map q ≤ T)
    (hi : (centralizer (A : Set G)).relIndex U = Nat.card F)
    {a : G} (ha : a ∈ A) (hne : q ⟨a,hAH ha⟩ ≠ 1) :
    U ⊓ centralizer (zpowers a : Set G) = U ⊓ centralizer (A : Set G) := by
  let : Finite W := Finite.of_surjective (fun u => (c.coordinates u).toAdd)
    (Multiplicative.toAdd.surjective.comp c.onto)
  let aH : H := ⟨a,hAH ha⟩
  have hcyc : (zpowers a).subgroupOf H = zpowers aH := by
    apply Subgroup.map_injective H.subtype_injective
    rw [map_subgroupOf_eq_of_le (zpowers_le.mpr (hAH ha)),MonoidHom.map_zpowers]
    rfl
  have hlo : Nat.card F ≤ (centralizer (zpowers a : Set G)).relIndex U := by
    have hh := c.fixed_quotient_card_le_centralizer_index σ q (zpowers a)
    rw [hcyc,MonoidHom.map_zpowers] at hh
    rw [hF]
    exact (sl2_element_fixed_index σ hf T (hAT (mem_map_of_mem q ha)) hne hF).trans hh
  have hle : (centralizer (A : Set G)).subgroupOf U ≤
      (centralizer (zpowers a : Set G)).subgroupOf U :=
    comap_mono (centralizer_le (zpowers_le.mpr ha))
  have he : (centralizer (A : Set G)).subgroupOf U =
      (centralizer (zpowers a : Set G)).subgroupOf U := by
    by_contra hn
    have hh := index_strictAnti (lt_of_le_of_ne hle hn)
    change (centralizer (zpowers a : Set G)).relIndex U <
      (centralizer (A : Set G)).relIndex U at hh
    rw [hi] at hh
    omega
  ext u
  constructor
  · rintro ⟨hu,hc⟩
    exact ⟨hu,show (⟨u,hu⟩ : U) ∈ (centralizer (A : Set G)).subgroupOf U from he.symm ▸ hc⟩
  · rintro ⟨hu,hc⟩
    exact ⟨hu,hle (x := ⟨u,hu⟩) hc⟩
end Representation.BinaryConjugationSection
