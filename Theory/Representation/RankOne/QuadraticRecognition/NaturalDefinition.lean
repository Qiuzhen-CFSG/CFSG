module
public import Theory.Representation.RankOne.QuadraticRecognition.SL2ProperActor
public import Theory.Representation.RankOne.QuadraticRecognition.CentralQuotientBounds
public import Theory.Representation.SL2.MinimalBinaryDegree
public import Theory.SpecificGroups.SL2.TwoCore

/-!
# Consequences of the source natural-module definition

A faithful binary SL₂ module of order 2^(2n), quadratic on a Sylow,
has no global fixed space: quotienting by that space preserves faithfulness
because O₂(SL₂)=1, and the quadratic quotient still has dimension at least
2n. The noncentral minimum-degree theorem then gives irreducibility.
A nonzero Sylow displacement is fixed by the Sylow, so irreducibility
proves generation by Sylow fixed vectors. Recognition now gives the exact
fixed orders, individual fixed spaces, complementary conjugate fixed spaces,
transitivity on nonzero vectors and equivariant natural coordinates.

No generation or residual-fixed-space premise is added to the source
natural definition. All positive field degrees, including n=1, are covered.
Source: DGS85, *Groups and Graphs*, definition p.112 and properties (i)–(iv),
p.113. CriticalRecognition applies these results to the literal local
central quotient supplied by an earlier source theorem such as (6.3).
-/

public noncomputable section
open Subgroup Representation.BinaryOffender
open scoped MatrixGroups
namespace Representation.RankOne.QuadraticRecognition
variable {F V : Type*} [Field F] [Finite F] [CharP F 2]
  [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
local instance : Algebra (ZMod 2) F := ZMod.algebra F 2
local instance (C : Submodule (ZMod 2) V) : Finite (V ⧸ C) :=
  Finite.of_surjective _ C.mkQ_surjective

private theorem sylow_ne_bot (S : Sylow 2 SL(2,F)) {n : ℕ} (hn : 0 < n)
    (hF : Nat.card F=2^n) : (S : Subgroup SL(2,F)) ≠ ⊥ := by
  have hc : Nat.card S = 2^n := (Nat.card_congr
    (Matrix.SpecialLinearGroup.sylowEquivAdditive F 2 S).symm.toEquiv).trans hF
  intro he
  change Nat.card (S : Subgroup SL(2,F)) = 2^n at hc
  rw [he,card_bot] at hc
  have hp : 1 < 2^n := one_lt_pow₀ (by decide) (by omega)
  omega

/-- A faithful quadratic Sylow action has degree at least twice the field degree.
A single involution moves at least one field degree and its image is fixed. -/
theorem sl2_quadratic_sylow_degree_lower
    (ρ : Representation (ZMod 2) SL(2,F) V) (hf : Function.Injective ρ)
    (S : Sylow 2 SL(2,F)) (hq : IsQuadratic ρ S)
    {n : ℕ} (hn : 0 < n) (hF : Nat.card F=2^n) :
    2*n ≤ Module.finrank (ZMod 2) V := by
  obtain ⟨a,ha,ha1⟩ := (S : Subgroup SL(2,F)).bot_or_exists_ne_one.resolve_left (sylow_ne_bot S hn hF)
  have hA : zpowers a ≠ ⊥ := fun he => ha1 (by simpa only [he,mem_bot] using mem_zpowers a)
  have hb := sl2_actor_field_bound ρ hf S (zpowers a) (zpowers_le.mpr ha) hA hF
  rw [hF,Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod] at hb
  have hlo : n ≤ fixedCodim ρ (zpowers a) :=
    (Nat.pow_le_pow_iff_right (by decide : 1 < (2:ℕ))).mp hb
  have hle : LinearMap.range (ρ a - LinearMap.id) ≤ fixedSpace ρ (zpowers a) := by
    rintro _ ⟨v,rfl⟩
    rw [mem_fixedSpace_zpowers_iff]
    exact hq a ha a ha v
  have hd := Submodule.finrank_mono hle
  rw [←fixedCodim_zpowers_eq_displacement_rank] at hd
  have he := fixedCodim_add_finrank ρ (zpowers a)
  omega

omit [Finite V] in
private theorem generation_of_irreducible {G : Type*} [Group G]
    (ρ : Representation (ZMod 2) G V) [ρ.IsIrreducible]
    (A : Subgroup G) (hA : fixedSpace ρ A ≠ ⊥) : GeneratedByFixedSpace ρ A := by
  let W := ⨆ g : G, (fixedSpace ρ A).map (ρ g)
  have hstable (a : G) : W.map (ρ a) ≤ W := by
    rw [Submodule.map_iSup]
    apply iSup_le
    intro g
    rw [←Submodule.map_comp]
    change (fixedSpace ρ A).map (ρ a * ρ g) ≤ W
    rw [←map_mul]
    exact le_iSup (fun g : G => (fixedSpace ρ A).map (ρ g)) (a*g)
  let U : Subrepresentation ρ := {
    toSubmodule := W
    apply_mem_toSubmodule a v hv := hstable a ⟨v,hv,rfl⟩ }
  have hAW : fixedSpace ρ A ≤ W := by
    have h := le_iSup (fun g : G => (fixedSpace ρ A).map (ρ g)) 1
    simpa only [map_one,show (1 : Module.End (ZMod 2) V)=LinearMap.id from rfl,Submodule.map_id] using h
  rcases (eq_bot_or_eq_top U) with h | h
  · exact False.elim (hA (bot_unique (hAW.trans (congrArg Subrepresentation.toSubmodule h).le)))
  · exact congrArg Subrepresentation.toSubmodule h

/-- The source's three-clause natural-module definition already implies the
corrected generation and zero global fixed space; these are not extra inputs. -/
theorem sourceNatural_generation_and_fixed
    (ρ : Representation (ZMod 2) SL(2,F) V) (hf : Function.Injective ρ)
    (S : Sylow 2 SL(2,F)) {n : ℕ} (hn : 0 < n) (hF : Nat.card F=2^n)
    (hnat : IsSourceNatural ρ S n) :
    GeneratedByFixedSpace ρ S ∧ fixedSpace ρ ⊤ = ⊥ ∧ ρ.IsIrreducible := by
  have hdim : Module.finrank (ZMod 2) V = 2*n := by
    have hh := hnat.1
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod] at hh
    exact Nat.pow_right_injective (by decide : 1 < (2:ℕ)) hh
  have hq := quadratic_of_equivariant_surjection ρ (globalFixedQuotient ρ)
    (fixedSpace ρ ⊤).mkQ (fixedSpace ρ ⊤).mkQ_surjective
    (fun g v => (globalFixedQuotient_mk ρ g v).symm) S hnat.2.2
  have hfq := globalFixedQuotient_faithful ρ hf (Matrix.SL2.twoCore_eq_bot F)
  have hdq := sl2_quadratic_sylow_degree_lower (globalFixedQuotient ρ) hfq S hq hn hF
  have hadd := (fixedSpace ρ ⊤).finrank_quotient_add_finrank
  have hfix : fixedSpace ρ ⊤ = ⊥ := by
    apply Submodule.finrank_eq_zero.mp
    change 2*n ≤ Module.finrank (ZMod 2) (V ⧸ fixedSpace ρ ⊤) at hdq
    omega
  let : Nontrivial V := Module.nontrivial_of_finrank_pos (R := ZMod 2) (by omega)
  have hinv : ρ.invariants = ⊥ := by
    apply bot_unique
    intro v hv
    exact hfix.le (fun g => hv g)
  let : ρ.IsIrreducible := SL2.irreducible_of_fixed_free_minimal_binary_degree
    ρ hinv (by omega) hF hdim.le
  have hS : fixedSpace ρ S ≠ ⊥ := by
    obtain ⟨a,ha,ha1⟩ := (S : Subgroup SL(2,F)).bot_or_exists_ne_one.resolve_left (sylow_ne_bot S hn hF)
    have hρa : ρ a ≠ 1 := fun h => ha1 (hf (h.trans ρ.map_one.symm))
    obtain ⟨v,hv⟩ : ∃ v, ρ a v ≠ v := by
      by_contra! hh
      exact hρa (LinearMap.ext hh)
    intro he
    have hh : ρ a v-v ∈ fixedSpace ρ S := fun b => hnat.2.2 b b.property a ha v
    rw [he,Submodule.mem_bot,sub_eq_zero] at hh
    exact hv hh
  exact ⟨generation_of_irreducible ρ S hS,hfix,inferInstance⟩

/-- All p.113 properties follow from the faithful source natural definition,
including field degree one, without separately assuming fixed-space generation. -/
theorem sourceNatural_coordinates_and_consequences
    (ρ : Representation (ZMod 2) SL(2,F) V) (hf : Function.Injective ρ)
    (S : Sylow 2 SL(2,F)) {n : ℕ} (hn : 0 < n) (hF : Nat.card F=2^n)
    (hnat : IsSourceNatural ρ S n) :
    ρ.IsIrreducible ∧ Nat.card (fixedSpace ρ S)=2^n ∧
    (∀ t ∈ (S : Subgroup SL(2,F)), t ≠ 1 → fixedSpace ρ (zpowers t)=fixedSpace ρ S) ∧
    (∀ g ∉ normalizer (S : Set SL(2,F)),
      IsCompl (fixedSpace ρ S) (fixedSpace ρ (g • S : Sylow 2 SL(2,F)))) ∧
    (∀ v w : V, v ≠ 0 → w ≠ 0 → ∃ g, ρ g v=w) ∧
    ∃ E : V ≃ₗ[ZMod 2] (Fin 2 → F), ∀ g v, E (ρ g v)=Matrix.mulVec g.val (E v) := by
  obtain ⟨hg,hfix,hi⟩ := sourceNatural_generation_and_fixed ρ hf S hn hF hnat
  have hdim : Module.finrank (ZMod 2) V = 2*n := by
    have hh := hnat.1
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod] at hh
    exact Nat.pow_right_injective (by decide : 1 < (2:ℕ)) hh
  have hS : fixedSpace ρ S ≠ ⊥ := by
    intro hh
    have hhg := hg
    simp only [GeneratedByFixedSpace,hh,Submodule.map_bot,iSup_const] at hhg
    have hd0 : Module.finrank (ZMod 2) V=0 := by
      simpa only [finrank_bot,finrank_top] using congrArg (fun C : Submodule (ZMod 2) V => Module.finrank (ZMod 2) C) hhg.symm
    omega
  have hpos : 0 < Module.finrank (ZMod 2) (fixedSpace ρ S) :=
    Nat.pos_of_ne_zero (fun he => hS (Submodule.finrank_eq_zero.mp he))
  have hsum := fixedCodim_add_finrank ρ S
  have hSc : Nat.card S=2^n := (Nat.card_congr
    (Matrix.SpecialLinearGroup.sylowEquivAdditive F 2 S).symm.toEquiv).trans hF
  have hstrict : Nat.card (V ⧸ fixedSpace ρ S) < Nat.card S^2 := by
    rw [hSc,Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod,←pow_mul]
    apply (Nat.pow_lt_pow_iff_right (by decide : 1 < (2:ℕ))).mpr
    change fixedCodim ρ S < n*2
    omega
  obtain ⟨_,E,he⟩ := sl2_strict_actor_natural ρ hf S S le_rfl hnat.2.2 hg hfix hF hstrict
  obtain ⟨hc,hu⟩ := sl2_natural_fixed_spaces ρ S hnat.2.2 hg hfix E
  refine ⟨hi,hc.trans hF,hu,?_,?_,E,he⟩
  · intro g hgn
    exact sl2_sylow_fixed_isCompl ρ S (g • S)
      (fun h => hgn (Sylow.smul_eq_iff_mem_normalizer.mp h.symm)) hnat.2.2 hg hfix
  · intro v w hv hw
    exact transitive_of_natural_coordinates ρ E he hv hw
end Representation.RankOne.QuadraticRecognition
