module

public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.Swapped.LinearTwo.ModuleAlternatives.FactorSpaces
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.FFBranch.Recognition.ClassificationComparison.FFAlternatives.SourceAlternatives
public import Theory.Representation.BinaryOffender.FixedQuotientKernel
public import Theory.Representation.BinaryOffender.IrreducibleMovedGeneration

/-!
# Removing fixed vectors from the maximal FF section

Once the source component commutator is the whole module, the maximal
avoiding H-submodule is maximal proper. Its literal quotient is therefore
H-irreducible. A normal subgroup generating this quotient by commutators
has zero fixed space. This applies to the normal component orbit K₀,
without asserting irreducibility for either individual component.

Consequently the fixed-space quotient in B.5.6 can be identified with the
original section by its actual projection. This lifts direct sums and
intertwining module identifications. Displacements in one invariant summand
vanish on the other, yielding cross-factor fixation with the original
subgroup inclusions retained. Selecting the classified factors and their
concrete natural or orthogonal models is a separate obligation.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), B.5.6(3),
printed p.105, and proof of 13.8.16(1), p.952 (PDF p.969).
-/

@[expose] public noncomputable section
open Subgroup Representation Representation.BinaryOffender
namespace CFSG.Quasithin.Chapter13.Section08.Components.Swapped.LinearTwo.ModuleAlternatives.FFFactors
open CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison.FFAlternatives
variable {D V : Type*} [Group D] [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) D V)

/-- The marked component's own action on its literal commutator space.
It is defined even when the component is moved by the ambient group. -/
def factorRepresentation (A : Subgroup D) :
    Representation (ZMod 2) A (subspaceCommutator ρ ⊤ A) :=
  (invariantSubspace ρ A (subspaceCommutator ρ ⊤ A)
    (subspaceCommutator_invariant ρ ⊤ A)).toRepresentation

@[simp] theorem factorRepresentation_apply (A : Subgroup D) (a : A)
    (v : subspaceCommutator ρ ⊤ A) :
    (factorRepresentation ρ A a v : V) = ρ a v := rfl

theorem quotient_full_commutator (N : Subrepresentation ρ) (A : Subgroup D)
    (hfull : subspaceCommutator ρ ⊤ A = ⊤) :
    subspaceCommutator N.quotientRepresentation ⊤ A = ⊤ := by
  have h := quotient_seed_commutator ρ N ⊤ A hfull
  simpa only [Submodule.map_top, LinearMap.range_eq_top.mpr N.toSubmodule.mkQ_surjective] using h

theorem maximal_avoiding_irreducible (N : Subrepresentation ρ)
    (hN : N ≠ ⊤)
    (hmax : ∀ Y : Subrepresentation ρ, N ≤ Y → Y ≠ ⊤ → Y = N) :
    N.quotientRepresentation.IsIrreducible := by
  have hn : N.toSubmodule ≠ ⊤ := fun he => hN (Subrepresentation.toSubmodule_injective he)
  let : Nontrivial (V ⧸ N.toSubmodule) := Submodule.Quotient.nontrivial_iff.mpr hn
  refine ⟨?_⟩
  intro S
  let T : Subrepresentation ρ := {
    toSubmodule := S.toSubmodule.comap N.toSubmodule.mkQ
    apply_mem_toSubmodule g v hv := S.apply_mem_toSubmodule g hv
  }
  have hNT : N ≤ T := by
    intro v hv
    change N.toSubmodule.mkQ v ∈ S
    have hz : N.toSubmodule.mkQ v = 0 := (Submodule.Quotient.mk_eq_zero _).mpr hv
    rw [hz]
    exact S.toSubmodule.zero_mem
  by_cases ht : T = ⊤
  · right
    apply Subrepresentation.toSubmodule_injective
    apply top_unique
    intro w _
    obtain ⟨v, rfl⟩ := N.toSubmodule.mkQ_surjective w
    exact (show v ∈ T from ht.symm ▸ (show v ∈ (⊤ : Subrepresentation ρ) from by trivial))
  · left
    have he := hmax T hNT ht
    apply Subrepresentation.toSubmodule_injective
    apply le_bot_iff.mp
    intro w hw
    obtain ⟨v, rfl⟩ := N.toSubmodule.mkQ_surjective w
    exact (Submodule.Quotient.mk_eq_zero _).mpr (show v ∈ N from he ▸ hw)

theorem maximal_component_section_irreducible (N : Subrepresentation ρ) (A : Subgroup D)
    (hfull : subspaceCommutator ρ ⊤ A = ⊤)
    (hN : ¬ subspaceCommutator ρ ⊤ A ≤ N.toSubmodule)
    (hmax : ∀ Y : Subrepresentation ρ, N ≤ Y →
      ¬ subspaceCommutator ρ ⊤ A ≤ Y.toSubmodule → Y = N) :
    N.quotientRepresentation.IsIrreducible := by
  apply maximal_avoiding_irreducible ρ N
  · intro he
    exact hN (he ▸ le_top)
  · intro Y hNY hY
    apply hmax Y hNY
    rw [hfull]
    intro ht
    exact hY (Subrepresentation.toSubmodule_injective (top_unique ht))

theorem fixedSpace_eq_bot_of_irreducible [ρ.IsIrreducible]
    (A : Subgroup D) [A.Normal]
    (hfull : subspaceCommutator ρ ⊤ A = ⊤) : fixedSpace ρ A = ⊥ := by
  let C : Subrepresentation ρ := {
    toSubmodule := fixedSpace ρ A
    apply_mem_toSubmodule g v hv := by
      have hg : g ∈ normalizer (A : Set D) := by
        rw [Subgroup.normalizer_eq_top]
        trivial
      exact (normalizer_le_stabilizer_fixedSpace ρ A hg v).mpr hv
  }
  rcases eq_bot_or_eq_top C with hc | hc
  · exact congrArg Subrepresentation.toSubmodule hc
  · have hfix : fixedSpace ρ A = ⊤ := congrArg Subrepresentation.toSubmodule hc
    have hz : subspaceCommutator ρ ⊤ A = ⊥ := by
      apply le_bot_iff.mp
      apply Submodule.span_le.mpr
      rintro _ ⟨a, ha, v, _, rfl⟩
      have hv : v ∈ fixedSpace ρ A := hfix ▸ Submodule.mem_top
      change ρ a v - v = 0
      exact sub_eq_zero.mpr (hv ⟨a, ha⟩)
    exact False.elim (top_ne_bot (α := Subrepresentation ρ)
      (Subrepresentation.toSubmodule_injective (hfull.symm.trans hz)))

theorem overgroup_invariants_eq_bot [ρ.IsIrreducible]
    (A J : Subgroup D) [A.Normal] (hAJ : A ≤ J)
    (hfull : subspaceCommutator ρ ⊤ A = ⊤) : fixedSpace ρ J = ⊥ := by
  apply le_bot_iff.mp
  rw [← fixedSpace_eq_bot_of_irreducible ρ A hfull]
  intro v hv a
  exact hv ⟨a, hAJ a.property⟩

/-- The equivalence is the literal quotient map, restricted to the chosen space. -/
def fixedQuotientSpaceEquiv (hfix : ρ.invariants = ⊥) (W : Subrepresentation ρ) :
    W.toSubmodule ≃ₗ[ZMod 2] ((fixed ρ).quotientImage W).toSubmodule := by
  let f : W.toSubmodule →ₗ[ZMod 2] ((fixed ρ).quotientImage W).toSubmodule :=
    (((fixed ρ).toSubmodule.mkQ).comp W.toSubmodule.subtype).codRestrict _
      (fun w => ⟨w, w.property, rfl⟩)
  apply LinearEquiv.ofBijective f
  constructor
  · intro x y he
    apply Subtype.ext
    have hq : (fixed ρ).toSubmodule.mkQ (x : V) = (fixed ρ).toSubmodule.mkQ (y : V) :=
      congrArg Subtype.val he
    have hm := (Submodule.Quotient.eq (fixed ρ).toSubmodule).mp hq
    change (x : V) - y ∈ ρ.invariants at hm
    rw [hfix, Submodule.mem_bot] at hm
    exact sub_eq_zero.mp hm
  · rintro ⟨w, x, hx, rfl⟩
    exact ⟨⟨x, hx⟩, rfl⟩

@[simp] theorem fixedQuotientSpaceEquiv_apply (hfix : ρ.invariants = ⊥)
    (W : Subrepresentation ρ) (w : W.toSubmodule) :
    (fixedQuotientSpaceEquiv ρ hfix W w).val =
      ρ.invariants.mkQ w := rfl

def fixedQuotientActionEquiv (hfix : ρ.invariants = ⊥)
    (W : Subrepresentation ρ) (A : Subgroup D) :
    ActionEquiv (W.toRepresentation.comp A.subtype)
      (((fixed ρ).quotientImage W).toRepresentation.comp A.subtype) where
  groupEquiv := MulEquiv.refl A
  linearEquiv := fixedQuotientSpaceEquiv ρ hfix W
  intertwines _ _ := rfl

theorem lift_quotient_complement (hfix : ρ.invariants = ⊥)
    (X Y : Subrepresentation ρ)
    (h : IsCompl ((fixed ρ).quotientImage X).toSubmodule
      ((fixed ρ).quotientImage Y).toSubmodule) : IsCompl X.toSubmodule Y.toSubmodule := by
  let e : V ≃ₗ[ZMod 2] (V ⧸ ρ.invariants) :=
    (ρ.invariants.quotEquivOfEqBot hfix).symm
  have he : e.toLinearMap = ρ.invariants.mkQ :=
    Submodule.coe_quotEquivOfEqBot_symm _ hfix
  have hx : X.toSubmodule.map e.toLinearMap = ((fixed ρ).quotientImage X).toSubmodule := by
    rw [he]; rfl
  have hy : Y.toSubmodule.map e.toLinearMap = ((fixed ρ).quotientImage Y).toSubmodule := by
    rw [he]; rfl
  apply (Submodule.orderIsoMapComap e).isCompl_iff.mpr
  change IsCompl (X.toSubmodule.map e.toLinearMap) (Y.toSubmodule.map e.toLinearMap)
  rwa [hx, hy]

/-- In a direct sum of invariant spaces, displacements landing in the first
space vanish on the second. -/
theorem cross_fixed_of_disjoint (X Y : Subrepresentation ρ) (A : Subgroup D)
    (hd : Disjoint X.toSubmodule Y.toSubmodule)
    (hm : subspaceCommutator ρ ⊤ A ≤ X.toSubmodule) :
    Y.toSubmodule ≤ fixedSpace ρ A := by
  intro v hv a
  apply sub_eq_zero.mp
  apply (Submodule.mem_bot (R := ZMod 2)).mp
  rw [← disjoint_iff.mp hd]
  exact ⟨hm (Submodule.subset_span ⟨a, a.property, v, Submodule.mem_top, rfl⟩),
    Y.toSubmodule.sub_mem (Y.apply_mem_toSubmodule a hv) hv⟩

theorem sourceFactorCase_moved_le {A : Subgroup D} {X : Subrepresentation ρ}
    (h : SourceFactorCase ρ A X) : subspaceCommutator ρ ⊤ A ≤ X.toSubmodule := by
  cases h with
  | natural hm _ => exact hm.ge
  | doubleNatural _ _ hm _ => exact hm.ge
  | exceptional hm _ => exact hm

/-- This uses the full source case, including exceptional factors. The fixed
space must first be removed using the genuine maximal H-section. -/
theorem classified_cross_fixed (hfix : ρ.invariants = ⊥) (c : SourceTwoFactorCase ρ) :
    c.secondSpace.toSubmodule ≤ fixedSpace ρ c.first ∧
      c.firstSpace.toSubmodule ≤ fixedSpace ρ c.second := by
  have hc := lift_quotient_complement ρ hfix c.firstSpace c.secondSpace c.decomposition
  exact ⟨cross_fixed_of_disjoint ρ _ _ _ hc.disjoint
    (sourceFactorCase_moved_le ρ c.firstCase),
    cross_fixed_of_disjoint ρ _ _ _ hc.disjoint.symm
      (sourceFactorCase_moved_le ρ c.secondCase)⟩

/-- Keep the original component inclusions when using the classified factors. -/
theorem classified_marked_cross_fixed (hfix : ρ.invariants = ⊥)
    (c : SourceTwoFactorCase ρ) (A B : Subgroup D)
    (hA : A ≤ c.first) (hB : B ≤ c.second) :
    subspaceCommutator ρ ⊤ B ≤ fixedSpace ρ A ∧
      subspaceCommutator ρ ⊤ A ≤ fixedSpace ρ B := by
  have hc := classified_cross_fixed ρ hfix c
  have hm (X Y : Subgroup D) (hXY : X ≤ Y) :
      subspaceCommutator ρ ⊤ X ≤ subspaceCommutator ρ ⊤ Y := by
    apply Submodule.span_mono
    rintro _ ⟨x, hx, v, hv, rfl⟩
    exact ⟨x, hXY hx, v, hv, rfl⟩
  constructor
  · intro v hv a
    exact hc.1 (sourceFactorCase_moved_le ρ c.secondCase (hm B c.second hB hv))
      ⟨a, hA a.property⟩
  · intro v hv b
    exact hc.2 (sourceFactorCase_moved_le ρ c.firstCase (hm A c.first hA hv))
      ⟨b, hB b.property⟩

theorem classified_marked_disjoint (hfix : ρ.invariants = ⊥)
    (c : SourceTwoFactorCase ρ) (A B : Subgroup D)
    (hA : A ≤ c.first) (hB : B ≤ c.second) :
    Disjoint (subspaceCommutator ρ ⊤ A) (subspaceCommutator ρ ⊤ B) := by
  have hc := lift_quotient_complement ρ hfix c.firstSpace c.secondSpace c.decomposition
  apply hc.disjoint.mono
  · apply Submodule.span_le.mpr
    rintro _ ⟨a, ha, v, hv, rfl⟩
    exact sourceFactorCase_moved_le ρ c.firstCase (Submodule.subset_span ⟨a, hA ha, v, hv, rfl⟩)
  · apply Submodule.span_le.mpr
    rintro _ ⟨b, hb, v, hv, rfl⟩
    exact sourceFactorCase_moved_le ρ c.secondCase (Submodule.subset_span ⟨b, hB hb, v, hv, rfl⟩)

end CFSG.Quasithin.Chapter13.Section08.Components.Swapped.LinearTwo.ModuleAlternatives.FFFactors
