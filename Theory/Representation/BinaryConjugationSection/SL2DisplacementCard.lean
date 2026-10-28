module
public import Theory.Representation.RankOne.QuadraticRecognition.NaturalDefinition
public import Theory.Representation.BinaryOffender.CommutatorRank
public import Theory.Representation.BinaryOffender.MovedDimension
public import Theory.Representation.BinaryConjugationSection.CommutatorImage
public import Theory.Representation.BinaryConjugationSection.ImageDimensions

/-!
# Displacement order in a natural binary SL₂ section

A Sylow two-subgroup moves exactly one field line in a natural module.
Quadraticity gives the upper bound; the common fixed space of each nonidentity
Sylow element gives the matching lower bound by rank-nullity. Pulling this
through literal conjugation coordinates bounds the order of the original
group commutator from below by the defining field order.

This is the natural-module calculation used in DGS, Groups and Graphs
(1985), 9.11, printed p.151. It applies to the original section and actor map.
-/

@[expose] public noncomputable section
open Subgroup Representation Representation.BinaryOffender
open scoped MatrixGroups
namespace Representation.RankOne.QuadraticRecognition
variable {F W : Type*} [Field F] [Finite F] [CharP F 2]
  [AddCommGroup W] [Module (ZMod 2) W] [Finite W]

/-- A full Sylow moves exactly one field line in the source natural module. -/
theorem sourceNatural_sylow_commutator_card
    (ρ : Representation (ZMod 2) SL(2,F) W) (hf : Function.Injective ρ)
    (T : Sylow 2 SL(2,F)) {n : ℕ} (hn : 0 < n) (hF : Nat.card F = 2^n)
    (hnat : IsSourceNatural ρ T n) :
    Nat.card (subspaceCommutator ρ ⊤ T) = Nat.card F := by
  let : Algebra (ZMod 2) F := ZMod.algebra F 2
  obtain ⟨_,hc,hu,_⟩ := sourceNatural_coordinates_and_consequences ρ hf T hn hF hnat
  have hq : subspaceCommutator ρ ⊤ T ≤ fixedSpace ρ T := by
    apply Submodule.span_le.mpr
    rintro _ ⟨a,ha,v,_,rfl⟩ b
    exact hnat.2.2 b b.property a ha v
  have hT : (T : Subgroup SL(2,F)) ≠ ⊥ := by
    intro he
    have ht := Nat.card_congr (Matrix.SpecialLinearGroup.sylowEquivAdditive F 2 T).toEquiv
    change Nat.card F = Nat.card (T : Subgroup SL(2,F)) at ht
    rw [he,card_bot,hF] at ht
    have hh : 1 < 2^n := one_lt_pow₀ (by decide) (by omega : n ≠ 0)
    omega
  obtain ⟨a,ha,hane⟩ := SetLike.exists_of_lt (bot_lt_iff_ne_bot.mpr hT)
  have hne : a ≠ 1 := by simpa only [mem_bot] using hane
  have hdimW : Module.finrank (ZMod 2) W = 2*n := by
    have hh := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := W)
    rw [hnat.1,Nat.card_zmod] at hh
    exact (Nat.pow_right_injective (by decide : 1 < (2 : ℕ)) hh).symm
  have hdimF : Module.finrank (ZMod 2) (fixedSpace ρ T) = n := by
    have hh := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := fixedSpace ρ T)
    rw [hc,Nat.card_zmod] at hh
    exact (Nat.pow_right_injective (by decide : 1 < (2 : ℕ)) hh).symm
  have hcod := fixedCodim_add_finrank ρ (zpowers a)
  rw [hu a ha hne,hdimF,hdimW,fixedCodim_zpowers_eq_displacement_rank] at hcod
  have hrange : LinearMap.range (ρ a - LinearMap.id) ≤ subspaceCommutator ρ ⊤ T := by
    rintro _ ⟨v,rfl⟩
    exact Submodule.subset_span ⟨a,ha,v,Submodule.mem_top,rfl⟩
  have he : subspaceCommutator ρ ⊤ T = fixedSpace ρ T := by
    apply Submodule.eq_of_le_of_finrank_le hq
    have hh := Submodule.finrank_mono hrange
    rw [hdimF]
    omega
  rw [he,hc,hF]

end Representation.RankOne.QuadraticRecognition

namespace Representation.BinaryConjugationSection
open Representation.RankOne.QuadraticRecognition
variable {G F W : Type*} [Group G] [Field F] [Finite F] [CharP F 2]
  [AddCommGroup W] [Module (ZMod 2) W]

/-- An actor with full Sylow image moves at least one field line in the
literal group section, before quotienting by its coordinate kernel. -/
theorem natural_section_commutator_card_ge
    {H S K : Subgroup G} [Finite S]
    (q : H →* SL(2,F)) (ρ : Representation (ZMod 2) SL(2,F) W)
    (c : BinaryConjugationSection H S K (ρ.comp q))
    (hf : Function.Injective ρ) (T : Sylow 2 SL(2,F))
    {n : ℕ} (hn : 0 < n) (hF : Nat.card F = 2^n)
    (hnat : IsSourceNatural ρ T n)
    (A : Subgroup G) (hAH : A ≤ H) (hA : (A.subgroupOf H).map q = T) :
    Nat.card F ≤ Nat.card (⁅A,S⁆ : Subgroup G) := by
  let : Finite W := Finite.of_surjective (fun x => (c.coordinates x).toAdd)
    (Multiplicative.toAdd.surjective.comp c.onto)
  have hRS : ⁅A,S⁆ ≤ S := le_normalizer_iff_commutator_le_right.mp
    (hAH.trans c.normalized)
  let : Finite (⁅A,S⁆ : Subgroup G) := Finite.of_injective (inclusion hRS) (inclusion_injective _)
  have htop : c.imageSpace S = ⊤ := by
    apply top_unique
    intro w _
    obtain ⟨s,hs⟩ := c.onto (Multiplicative.ofAdd w)
    exact (c.mem_imageSpace_iff S w).mpr ⟨s,s.property,congrArg Multiplicative.toAdd hs⟩
  have hc : Nat.card (c.imageSpace ⁅A,S⁆) = Nat.card F := by
    rw [c.imageSpace_commutator A S hAH le_rfl,htop,subspaceCommutator_comp_map,hA]
    exact sourceNatural_sylow_commutator_card ρ hf T hn hF hnat
  rw [←hc,c.imageSpace_card_eq_relIndex _ hRS]
  exact Nat.le_of_dvd Nat.card_pos (relIndex_dvd_card K _)

end Representation.BinaryConjugationSection
