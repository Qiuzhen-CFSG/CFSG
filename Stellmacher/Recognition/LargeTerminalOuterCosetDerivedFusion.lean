module

public import Stellmacher.Recognition.LargeTerminalOuterCosetGeometry
public import Stellmacher.Recognition.LargeTerminalDerivedCentralizer
public import Stellmacher.Recognition.LargeTerminalOuterCosetBlockMover
public import Stellmacher.Recognition.LargeTerminalOuterCosetSelection

/-!
# Fusing outer-coset involutions into the derived residual

Write D for the derived first residual and E for the terminal module.
For an involution f in E intersected with the residual, outside C_Q(D),
the sixteen involutions of Df split into two blocks of eight according to
membership in E. If a conjugation carries the E-block outside E while
preserving the coset, cardinality makes its image the whole other block.
Every involution of Df then fuses into E, hence into its conjugate D.

The final theorem uses the proved five-coset selection and terminal block
mover to conjugate each outer core involution into D. The earlier conditional
interfaces record the two steps separately. The supplied subgroup of order
five and its fixed subgroup suffice; no ambient Sylow-five status or global
simplicity assumption is needed for this local conclusion.

Source: Thompson VI, printed p.630, the five involutory outer cosets and
the paragraph choosing H outside C_Q(Z*).
-/

namespace Stellmacher.Recognition
open Later SectionsFiveToSeven Subgroup
universe u

/-- A mover from the terminal block into its complement fuses all sixteen
involutions of the distinguished derived coset into the derived residual. -/
public theorem LargeTerminalContext.derived_coset_fusion_of_terminal_block_mover
    {G : Type u} [Group G] [Finite G] {S : Sylow 2 G}
    (ctx : LargeTerminalContext S) (f : G) (hfE : f ∈ ctx.terminalModule)
    (hfR : f ∈ ctx.firstResidual)
    (hfc : f ∉ centralizer (DerivedAmbient ctx.firstResidual : Set G))
    (hf : orderOf f = 2)
    (g : G)
    (hmove : ∀ b : G, b * f⁻¹ ∈ DerivedAmbient ctx.firstResidual →
      b ∈ ctx.terminalModule →
      (MulAut.conj g b) * f⁻¹ ∈ DerivedAmbient ctx.firstResidual ∧
        MulAut.conj g b ∉ ctx.terminalModule)
    (x : G) (hx : x * f⁻¹ ∈ DerivedAmbient ctx.firstResidual)
    (hxorder : orderOf x = 2) :
    ∃ t : G, t ∈ DerivedAmbient ctx.firstResidual ∧ IsConj x t := by
  classical
  let D := DerivedAmbient ctx.firstResidual
  let E := ctx.terminalModule
  let T := {x : G | x * f⁻¹ ∈ D ∧ orderOf x = 2}
  let B := T ∩ (E : Set G)
  obtain ⟨hB, hrest⟩ := ctx.derived_coset_terminal_partition f hfE hfR hfc hf
  change B.ncard = 8 at hB
  change (T \ (E : Set G)).ncard = 8 at hrest
  have himage : MulAut.conj g '' B ⊆ T \ (E : Set G) := by
    rintro _ ⟨b, hb, rfl⟩
    obtain ⟨hcoset, hout⟩ := hmove b hb.1.1 hb.2
    exact ⟨⟨hcoset, ((MulAut.conj g).orderOf_eq b).trans hb.1.2⟩, hout⟩
  have heq : MulAut.conj g '' B = T \ (E : Set G) := by
    apply Set.eq_of_subset_of_ncard_le himage
    rw [Set.ncard_image_of_injective _ (MulAut.conj g).injective, hB, hrest]
  by_cases hxE : x ∈ E
  · exact ctx.terminal_module_isConj_derived x hxE
  · obtain ⟨b, hb, rfl⟩ := heq.symm ▸ (show x ∈ T \ (E : Set G) from
      ⟨⟨hx, hxorder⟩, hxE⟩)
    obtain ⟨t, ht, hbt⟩ := ctx.terminal_module_isConj_derived b hb.2
    exact ⟨t, ht, (isConj_iff.mpr ⟨g, rfl⟩ : IsConj b (MulAut.conj g b)).symm.trans hbt⟩


/-- Outer-coset fusion follows from selection of the distinguished derived
coset and a mover between its two blocks of eight involutions. -/
public theorem LargeTerminalContext.outer_coset_derived_fusion_of_selection_and_mover
    {G : Type u} [Group G] [Finite G] {S : Sylow 2 G}
    (ctx : LargeTerminalContext S) (f : G) (hfE : f ∈ ctx.terminalModule)
    (hfR : f ∈ ctx.firstResidual)
    (hfc : f ∉ centralizer (DerivedAmbient ctx.firstResidual : Set G))
    (hf : orderOf f = 2)
    (hselect : ∀ x : G, x ∈ twoCoreIn ctx.second →
      x ∉ centralizer (DerivedAmbient ctx.firstResidual : Set G) → orderOf x = 2 →
      ∃ a : G, (MulAut.conj a x) * f⁻¹ ∈ DerivedAmbient ctx.firstResidual)
    (hmove : ∃ g : G, ∀ b : G, b * f⁻¹ ∈ DerivedAmbient ctx.firstResidual →
      b ∈ ctx.terminalModule →
      (MulAut.conj g b) * f⁻¹ ∈ DerivedAmbient ctx.firstResidual ∧
        MulAut.conj g b ∉ ctx.terminalModule) :
    ∀ x : G, x ∈ twoCoreIn ctx.second →
      x ∉ centralizer (DerivedAmbient ctx.firstResidual : Set G) → orderOf x = 2 →
      ∃ t : G, t ∈ DerivedAmbient ctx.firstResidual ∧ IsConj x t := by
  obtain ⟨g, hg⟩ := hmove
  intro x hxQ hxc hx
  obtain ⟨a, ha⟩ := hselect x hxQ hxc hx
  obtain ⟨t, ht, hconj⟩ := ctx.derived_coset_fusion_of_terminal_block_mover
    f hfE hfR hfc hf g hg (MulAut.conj a x) ha (((MulAut.conj a).orderOf_eq x).trans hx)
  exact ⟨t, ht, (isConj_iff.mpr ⟨a, rfl⟩ : IsConj x (MulAut.conj a x)).trans hconj⟩

/-- Every involution of the second core outside the centralizer of the
derived first residual is conjugate into that derived residual. The
five-coset selection and the mover between the two blocks of eight are
derived from the terminal context and the supplied five-fixed data. -/
public theorem LargeTerminalContext.outer_coset_derived_fusion
    {G : Type u} [Group G] [Finite G] {S : Sylow 2 G}
    (ctx : LargeTerminalContext S) (hS : Nat.card S = 4096)
    (A : Subgroup G) (hA : Nat.card A = 5)
    (hAN : A ≤ normalizer (ctx.firstResidual : Set G))
    (hcard : Nat.card ((centralizer (A : Set G)).subgroupOf (twoCoreIn ctx.second)) = 4)
    (hfixed : (centralizer (A : Set G)).subgroupOf ctx.firstResidual ≤
      center ctx.firstResidual)
    (hncyc : ¬ IsCyclic ((centralizer (A : Set G)).subgroupOf (twoCoreIn ctx.second))) :
    ∀ x : G, x ∈ twoCoreIn ctx.second →
      x ∉ centralizer (DerivedAmbient ctx.firstResidual : Set G) → orderOf x = 2 →
      ∃ t : G, t ∈ DerivedAmbient ctx.firstResidual ∧ IsConj x t := by
  obtain ⟨f, hfE, hfR, _, hfc, hf⟩ := ctx.exists_terminal_module_outer_involution
  apply ctx.outer_coset_derived_fusion_of_selection_and_mover f hfE hfR hfc hf
  · intro x hxQ hxc hx
    obtain ⟨a, _, ha⟩ := ctx.outer_involution_coset_selection hS A hA hAN hcard
      hfixed hncyc f hfR hfc hf x hxQ hxc hx
    exact ⟨a, ha⟩
  · obtain ⟨g, _, _, hg⟩ := ctx.exists_terminal_block_mover f hfE hfR hfc
    exact ⟨g, hg⟩

end Stellmacher.Recognition
