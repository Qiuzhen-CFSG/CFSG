module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.Noncommuting.TerminalSmallExclusion

/-!
# Quadratic bounds from faithful Sylow action in the complete local catalogue

The already proved nonlinear exclusions reduce any hypothetical violation
of the lower index bound to a linear group. In SL₂, a nonzero two-actor
moves at least one full field degree; the field-two case only needs
faithfulness on the given Sylow. Thus the lower bound needs no full
faithfulness or residual-fixed-space assumption. Equality excludes every
nonlinear row, including D₁₀ separately from the Chapter 5 catalogue.

`EndpointIndices` applies these bounds to the actual two endpoint
quotients and proves their reciprocal index equalities and linear models.
Source: DGS, *Groups and Graphs* (1985), (7.1), pp.126–127, using the
corrected quadratic bounds in (5.12).
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender
open Representation.RankOne.QuadraticRecognition
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.DGS85.Noncommuting
variable {D W : Type*} [Group D] [Finite D]
  [AddCommGroup W] [Module (ZMod 2) W] [Finite W]

local instance (C : Submodule (ZMod 2) W) : Finite (W ⧸ C) :=
  Finite.of_surjective _ C.mkQ_surjective

private theorem sl2_sylow_faithful_bound
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (σ : Representation (ZMod 2) SL(2,F) W) (T : Sylow 2 SL(2,F))
    (A : Subgroup SL(2,F)) (hAT : A ≤ T)
    (hd : Disjoint σ.ker (T : Subgroup SL(2,F)))
    {n : ℕ} (hc : Nat.card F = 2^n) :
    Nat.card A ≤ Nat.card (W ⧸ fixedSpace σ A) := by
  by_cases hAb : A = ⊥
  · rw [hAb,card_bot]
    exact Nat.card_pos
  obtain ⟨a,ha,ha1⟩ := A.bot_or_exists_ne_one.resolve_left hAb
  have hnt : σ a ≠ 1 := fun hh => ha1 (mem_bot.mp (hd.le_bot ⟨hh,hAT ha⟩))
  have hdim : n ≤ fixedCodim σ A := by
    by_cases hn : 1 < n
    · exact SL2.two_subgroup_fixedCodim_lower σ ⟨a,hnt⟩ hn hc A
        (T.isPGroup'.to_le hAT) hAb
    · have hpos : 0 < fixedCodim σ A := by
        by_contra hh
        have hfix := (fixedCodim_eq_zero_iff σ A).mp (by omega)
        apply hnt
        apply LinearMap.ext
        intro w
        exact (show w ∈ fixedSpace σ A from hfix.symm ▸ Submodule.mem_top) ⟨a,ha⟩
      omega
  have hfield : Nat.card F ≤ Nat.card (W ⧸ fixedSpace σ A) := by
    rw [hc,Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod]
    exact Nat.pow_le_pow_right (by decide) hdim
  have hTcard : Nat.card T = Nat.card F := Nat.card_congr
    (Matrix.SpecialLinearGroup.sylowEquivAdditive F 2 T).symm.toEquiv
  exact ((card_le_of_le hAT).trans_eq hTcard).trans hfield

private theorem linear_sylow_faithful_bound
    {n : ℕ} (hm : ClassicalGroup.IsPSL D 2 (2^n))
    (σ : Representation (ZMod 2) D W) (T : Sylow 2 D) (A : Subgroup D)
    (hAT : A ≤ T) (hd : Disjoint σ.ker (T : Subgroup D)) :
    Nat.card A ≤ Nat.card (W ⧸ fixedSpace σ A) := by
  obtain ⟨F,hF,hfin,hcard,⟨e⟩⟩ := hm
  let := hF
  let := hfin
  let := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using hcard)
  let e' := e.trans (Theory.PSL2.sl2QuotientEquiv F).symm
  let ρ := σ.comp e'.symm.toMonoidHom
  let S := T.mapSurjective (f := e'.toMonoidHom) e'.surjective
  have hdis : Disjoint ρ.ker (S : Subgroup SL(2,F)) := by
    apply disjoint_iff.mpr
    apply bot_unique
    rintro _ ⟨hk,x,hx,rfl⟩
    have hxk : x ∈ σ.ker := by simpa [ρ] using hk
    have hx1 := mem_bot.mp (hd.le_bot ⟨hxk,hx⟩)
    simp only [hx1,map_one,mem_bot]
  have hbound := sl2_sylow_faithful_bound ρ S (A.map e'.toMonoidHom) (map_mono hAT) hdis hcard
  have hfixed : fixedSpace ρ (A.map e'.toMonoidHom) = fixedSpace σ A := by
    rw [fixedSpace_comp_map,map_map]
    have he : e'.symm.toMonoidHom.comp e'.toMonoidHom = MonoidHom.id D := by ext x; simp
    rw [he,map_id]
  rwa [card_map_of_injective e'.injective,hfixed] at hbound

/-- The original local catalogue and faithful Sylow action imply the lower index estimate. -/
theorem rankOne_sylow_faithful_quadratic_bound (hm : IsRankOneModel D)
    (σ : Representation (ZMod 2) D W) (T : Sylow 2 D) (A : Subgroup D)
    (hAT : A ≤ T) (hA : 1 < Nat.card A) (hq : IsQuadratic σ A)
    (hg : GeneratedByFixedSpace σ T) (hd : Disjoint σ.ker (T : Subgroup D)) :
    Nat.card A ≤ Nat.card (W ⧸ fixedSpace σ A) := by
  by_contra hn
  have hb : Nat.card (W ⧸ fixedSpace σ A) ≤ Nat.card A := by omega
  rcases terminal_action_model_alternatives hm σ T A hAT hA hq hg hd hb with
    ⟨n,_,he⟩ | he
  · exact hn (linear_sylow_faithful_bound he σ T A hAT hd)
  · exact small_unitary_fixed_generated_index_obstruction he σ T A hAT hA hq hg hd hb

/-- A nontrivial quadratic actor with sharp index forces an actual linear quotient model. -/
theorem rankOne_linear_of_sylow_faithful_sharp_index (hm : IsRankOneModel D)
    (σ : Representation (ZMod 2) D W) (T : Sylow 2 D) (A : Subgroup D)
    (hAT : A ≤ T) (hA : 1 < Nat.card A) (hq : IsQuadratic σ A)
    (hg : GeneratedByFixedSpace σ T) (hd : Disjoint σ.ker (T : Subgroup D))
    (hb : Nat.card (W ⧸ fixedSpace σ A) ≤ Nat.card A) :
    ∃ n, 0 < n ∧ ClassicalGroup.IsPSL D 2 (2^n) := by
  rcases terminal_action_model_alternatives hm σ T A hAT hA hq hg hd hb with he | he
  · exact he
  · exact (small_unitary_fixed_generated_index_obstruction he σ T A hAT hA hq hg hd hb).elim

end CFSG.Quasithin.ChapterF.Source.DGS85.Noncommuting
