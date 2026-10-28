module

public import CFSG.Quasithin.Chapter16.Section04To05.FusionRestrictions.ResidualSymmetry.Conjugator.ActorGeometry
public import CFSG.Quasithin.Chapter16.Section01To02.SourceHypothesis
public import CFSG.KnownSimple.CarrierCatalogue
public import CFSG.Quasithin.Chapter16.Section01To02.LiePreliminaries.RankOneRoots
public import Theory.AtlasPort.ExceptionalIsomorphisms.Support

/-!
# Rank-one reductions for unequal selected residuals

Inverse transport equates the orders of the two embedded residuals. Thus
neither can be trivial in the unequal case. A two-group fixed subgroup of
the actual inverse normalizer action would make its modified residual
trivial, independently of whether the O³ modification is active.

The rank-one root calculations therefore exclude every Suzuki quotient,
including its nonsplit central covers, and every inner inverse action for
binary PSL₂. The remaining PSL₂ action is outer and its degree is even by
the proved field-automorphism calculation. These conclusions retain the
quotient by O₂(L); no central covering kernel is discarded.

This does not construct the rank witness for the outer PSL₂ and unitary
branches. Those ambient constructions remain with the Lie-family assembly.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
16.1.1–4, printed pp.1169–1171, and 16.5.5–6, printed p.1197.
-/

@[expose] public section

open Subgroup Theory.GroupTheory
open CFSG.Quasithin.Chapter16

namespace CFSG.Quasithin.Chapter16.Intersections.ResidualSymmetry.Conjugator.Lie

variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {z g : G} {L R : Subgroup G}

/-- Neither selected residual can vanish when they are unequal. -/
theorem inverse_ne_bot (d : ResidualInputs T z L g R)
    (hne : modifiedCentralizerResidual L (MulAut.conj g⁻¹ z) ≠
      modifiedCentralizerResidual L (MulAut.conj g z)) :
    modifiedCentralizerResidual L (MulAut.conj g⁻¹ z) ≠ ⊥ := by
  intro hb
  have hc := d.residual_card_eq
  rw [hb, card_bot] at hc
  exact hne (hb.trans (eq_bot_of_card_eq _ hc.symm).symm)

omit [Finite G] in
private theorem modified_eq_bot_of_fixed_two (t : G) (ht : t ∈ normalizer (L : Set G))
    (hp : IsPGroup 2 (L.normalizerMonoidHom ⟨t, ht⟩).fixedSubgroup) :
    modifiedCentralizerResidual L t = ⊥ := by
  let a := L.normalizerMonoidHom ⟨t, ht⟩
  have he : a.fixedSubgroup.map L.subtype = L ⊓ centralizer ({t} : Set G) := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      refine ⟨y.property, mem_centralizer_singleton_iff.mpr ?_⟩
      have hf := congrArg Subtype.val ((MulAut.mem_fixedSubgroup _ _).mp hy)
      change t * (y : G) * t⁻¹ = y at hf
      exact (mul_inv_eq_iff_eq_mul.mp hf).symm
    · intro hx
      refine ⟨⟨x, hx.1⟩, (MulAut.mem_fixedSubgroup _ _).mpr ?_, rfl⟩
      apply Subtype.ext
      change t * x * t⁻¹ = x
      rw [← mem_centralizer_singleton_iff.mp hx.2, mul_inv_cancel_right]
  have hp' : IsPGroup 2 (L ⊓ centralizer ({t} : Set G) : Subgroup G) :=
    he ▸ hp.map L.subtype
  have hb : pResidual 2 (L ⊓ centralizer ({t} : Set G) : Subgroup G) = ⊥ :=
    le_bot_iff.mp (sInf_le ⟨inferInstance, hp'.to_quotient ⊥⟩)
  apply eq_bot_iff.mpr
  apply (modifiedCentralizerResidual_le L t).trans
  simp only [involutionTwoResidual, hb, Subgroup.map_bot, le_refl]

/-- (E1) passes to the component by relative subnormality in C_G(z). -/
theorem component_oddCore (hG : HasEvenTypeCentralizers G)
    (d : ResidualInputs T z L g R) : pPrimeCore 2 L = ⊥ := by
  have hc := Subgroup.IsSubnormal.pPrimeCore_eq_bot
    (hG.oddCore z d.setup.involution)
    (L.subgroupOf (involutionCentralizer z)) d.setup.component.2.1
  have hm := pPrimeCore_map_iso 2 (subgroupOfEquivOfLe d.setup.component.1)
  simpa only [hc, Subgroup.map_bot] using hm.symm

/-- An unequal selected pair cannot have a two-group inverse fixed subgroup. -/
theorem inverse_fixed_not_two (d : ResidualInputs T z L g R)
    (hne : modifiedCentralizerResidual L (MulAut.conj g⁻¹ z) ≠
      modifiedCentralizerResidual L (MulAut.conj g z)) :
    ¬ IsPGroup 2 (L.normalizerMonoidHom
      ⟨MulAut.conj g⁻¹ z, d.inverse_mem_normalizer⟩).fixedSubgroup := by
  intro hp
  exact inverse_ne_bot d hne
    (modified_eq_bot_of_fixed_two _ d.inverse_mem_normalizer hp)

/-- Every Suzuki quotient, including the exceptional covers of Sz(8), is
excluded by its actual involution fixed subgroup being a two-group. -/
theorem not_suzuki (hG : HasEvenTypeCentralizers G)
    (d : ResidualInputs T z L g R)
    (hne : modifiedCentralizerResidual L (MulAut.conj g⁻¹ z) ≠
      modifiedCentralizerResidual L (MulAut.conj g z))
    {m : ℕ} (hm : 1 ≤ m)
    (e : (L ⧸ pCore 2 L) ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m) : False := by
  let : IsQuasisimple L := d.setup.component.quasisimple
  obtain ⟨_, _, _, _, _, _, _, _, _, hp, _⟩ :=
    LiePreliminaries.suzuki_involution_roots (component_oddCore hG d) hm e _
      (d.inverse_action_order hne)
  exact inverse_fixed_not_two d hne hp

/-- In binary PSL₂ the unequal case forces the actual inverse action to be outer. -/
theorem inverse_outer_of_binary_psl2 (hG : HasEvenTypeCentralizers G)
    (d : ResidualInputs T z L g R)
    (hne : modifiedCentralizerResidual L (MulAut.conj g⁻¹ z) ≠
      modifiedCentralizerResidual L (MulAut.conj g z))
    {n : ℕ} (hn : 2 ≤ n)
    (e : (L ⧸ pCore 2 L) ≃* BenderSuzuki.MatrixGroups.PSL2BinaryMatrixGroup n) :
    ¬ ∃ x : L, L.normalizerMonoidHom
      ⟨MulAut.conj g⁻¹ z, d.inverse_mem_normalizer⟩ = MulAut.conj x := by
  intro hi
  let : IsQuasisimple L := d.setup.component.quasisimple
  obtain ⟨_, _, _, _, _, _, _, _, _, hp, _⟩ :=
    LiePreliminaries.psl2_inner_involution_roots (component_oddCore hG d) hn e _
      (d.inverse_action_order hne) hi
  exact inverse_fixed_not_two d hne hp

private noncomputable def binaryEquiv {H : Type*} [Group H] {n : ℕ} (hn : 0 < n)
    (h : ClassicalGroup.IsPSL H 2 (2 ^ n)) :
    H ≃* BenderSuzuki.MatrixGroups.PSL2BinaryMatrixGroup n :=
  Classical.choice <| by
    obtain ⟨F, hF, hfin, hcard, ⟨e⟩⟩ := h
    let := Fintype.ofFinite F
    let := Fintype.ofFinite (BenderSuzuki.PFAppendixIII.BinaryGaloisField n)
    let f : F ≃+* BenderSuzuki.PFAppendixIII.BinaryGaloisField n :=
      FiniteField.ringEquivOfCardEq (by
        rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card,
          hcard, BenderSuzuki.Converse.card_binaryGaloisField n (by omega)])
    exact ⟨e.trans (Atlas.fieldEquivPSL 2 f)⟩

/-- The remaining PSL₂ degree is even, as proved by the actual field action. -/
theorem psl2_degree_even (hG : HasEvenTypeCentralizers G)
    (d : ResidualInputs T z L g R)
    (hne : modifiedCentralizerResidual L (MulAut.conj g⁻¹ z) ≠
      modifiedCentralizerResidual L (MulAut.conj g z))
    {n : ℕ} (hn : 2 ≤ n)
    (hmodel : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n)) : Even n := by
  let : IsQuasisimple L := d.setup.component.quasisimple
  let e := binaryEquiv (by omega : 0 < n) hmodel
  obtain ⟨m, _, he, _⟩ := LiePreliminaries.psl2_quotient_outer_fixed_model
    (component_oddCore hG d) hn e _ (d.inverse_action_order hne)
      (inverse_outer_of_binary_psl2 hG d hne hn e)
  exact ⟨m, by omega⟩


/-- The outer conclusion on an arbitrary field presentation of binary PSL₂. -/
theorem inverse_outer_of_psl2 (hG : HasEvenTypeCentralizers G)
    (d : ResidualInputs T z L g R)
    (hne : modifiedCentralizerResidual L (MulAut.conj g⁻¹ z) ≠
      modifiedCentralizerResidual L (MulAut.conj g z))
    {n : ℕ} (hn : 2 ≤ n)
    (hmodel : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n)) :
    ¬ ∃ x : L, L.normalizerMonoidHom
      ⟨MulAut.conj g⁻¹ z, d.inverse_mem_normalizer⟩ = MulAut.conj x :=
  inverse_outer_of_binary_psl2 hG d hne hn (binaryEquiv (by omega) hmodel)

/-- Exhaust the Bender alternatives in the unequal case. The eliminated
Suzuki and odd-degree PSL₂ cases require no additional ambient model input. -/
theorem bender_remaining (hG : HasEvenTypeCentralizers G)
    (d : ResidualInputs T z L g R)
    (hne : modifiedCentralizerResidual L (MulAut.conj g⁻¹ z) ≠
      modifiedCentralizerResidual L (MulAut.conj g z))
    (hb : ClassificationModels.IsBenderModel (L ⧸ pCore 2 L)) :
    (∃ n : ℕ, 2 ≤ n ∧ Even n ∧
      ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n) ∧
      ¬ ∃ x : L, L.normalizerMonoidHom
        ⟨MulAut.conj g⁻¹ z, d.inverse_mem_normalizer⟩ = MulAut.conj x) ∨
    (∃ n : ℕ, 2 ≤ n ∧ ClassicalGroup.IsPSU (L ⧸ pCore 2 L) 3 (2 ^ n)) := by
  cases hb with
  | linear n hn he =>
    exact Or.inl ⟨n, hn, psl2_degree_even hG d hne hn he, he,
      inverse_outer_of_psl2 hG d hne hn he⟩
  | unitary n hn he => exact Or.inr ⟨n, hn, he⟩
  | suzuki m hm he => exact (not_suzuki hG d hne hm he.some).elim

end CFSG.Quasithin.Chapter16.Intersections.ResidualSymmetry.Conjugator.Lie
