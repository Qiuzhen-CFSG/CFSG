module

public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.Assembly
public import CFSG.Quasithin.Chapter12.Section08.Preliminary.NormalL1

/-!
# Separation of the natural seed before local recognition

A proper H-invariant subspace of any literal U/V₁ conjugation section
pulls back to an H-invariant subgroup I of U. Natural simplicity forces
V ∩ I to be V₁ or V. In the latter case the H-conjugates of V generate U,
contradicting properness. Thus the seed meets the subspace in exactly V₁.
The proof uses the original natural marking and no source conclusion record.

This is the coordinate-independent form of the argument in
Source/Rechoice/SourceCompletion/ModuleSeparation.lean, moved before
recognition for use in the 14.7.40 natural-module reduction.

Source: Aschbacher–Smith, 14.7.2(1), printed p.1043.
-/

public noncomputable section
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
open Subgroup Representation Chapter12.Section08 CriticalFusion.Source
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3} {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]

/-- Every proper invariant subspace meets the original seed in its point. -/
theorem seed_intersection
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    {ρ : Representation (ZMod 2) F.H W}
    (c : BinaryConjugationSection F.H F.U (F.Vi 1) ρ)
    (A : Submodule (ZMod 2) W)
    (hA : ∀ g w, w ∈ A → ρ g w ∈ A) (hproper : A ≠ ⊤) :
    ∀ v : F.U, (v : G) ∈ V →
      ((c.coordinates v).toAdd ∈ A ↔ (v : G) ∈ F.Vi 1) := by
  let := h.chosen.elementary
  let := F.localKernel_tilde_seed_elementary
  let I : Subgroup G :=
    (A.toAddSubgroup.toSubgroup.comap c.coordinates).map F.U.subtype
  have memI (u : F.U) : (u : G) ∈ I ↔
      (c.coordinates u).toAdd ∈ A := by
    constructor
    · rintro ⟨v, hv, he⟩
      exact (Subtype.ext he : v = u) ▸ hv
    · intro hu
      exact ⟨u, hu, rfl⟩
  have hIU : I ≤ F.U := by rintro _ ⟨u, _, rfl⟩; exact u.property
  have hPI : F.Vi 1 ≤ I := by
    intro v hv
    apply (memI ⟨v, c.kernel_le hv⟩).mpr
    rw [(c.coordinates_eq_one_iff _).mpr hv]
    exact A.zero_mem
  have hclosed (h : F.H) {v : G} (hv : v ∈ I) : (h : G) * v * (h : G)⁻¹ ∈ I := by
    let u : F.U := ⟨v, hIU hv⟩
    apply (memI ⟨_, (mem_normalizer_iff.mp
      (c.normalized h.property) v).mp u.property⟩).mpr
    rw [c.equivariant h u]
    exact hA h _ ((memI u).mp hv)
  have hHI : F.H ≤ normalizer (I : Set G) := by
    intro h hh
    apply mem_normalizer_iff.mpr
    intro v
    constructor
    · exact hclosed ⟨h, hh⟩
    · intro hv
      simpa only [Subgroup.coe_inv, inv_inv, mul_assoc, inv_mul_cancel_left,
        mul_inv_cancel_right, inv_mul_cancel, mul_one] using
        hclosed (⟨h, hh⟩ : F.H)⁻¹ hv
  have hLVI : F.Li L 1 ≤ normalizer ((V ⊓ I : Subgroup G) : Set G) :=
    le_normalizer_inf ((F.Li_le L 1).trans (inf_le_left.trans h.chosen.normalizes))
      (((F.Li_le L 1).trans inf_le_right).trans hHI)
  have split := F.invariant_subgroup_of_ambient_natural h.naturalMarking
    (by decide : 3 ≤ 3) (V ⊓ I) (le_inf (F.le_seed 1) hPI) inf_le_left hLVI
  have hinter : V ⊓ I = F.Vi 1 := by
    rcases split with he | he
    · exact he
    · exfalso
      apply hproper
      have hVI : V ≤ I := he.ge.trans inf_le_right
      have hUI : F.U ≤ I := conjugateSpanBy_le hVI hHI
      apply top_unique
      intro w _
      obtain ⟨u, hu⟩ := c.onto (Multiplicative.ofAdd w)
      have hw := (memI u).mp (hUI u.property)
      rw [hu] at hw
      exact hw
  intro v hv
  constructor
  · intro ha
    exact hinter ▸ (show (v : G) ∈ V ⊓ I from ⟨hv, (memI v).mpr ha⟩)
  · intro hp
    rw [(c.coordinates_eq_one_iff _).mpr hp]
    exact A.zero_mem

/-- The constructed literal section has the seed-separation property,
without requiring a recognized quotient or a source datum. -/
theorem exists_separated_section
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U) :
    ∃ (W : Type u) (_ : AddCommGroup W) (_ : Module (ZMod 2) W)
      (ρ : Representation (ZMod 2) F.H W)
      (c : BinaryConjugationSection F.H F.U (F.Vi 1) ρ),
      ∀ A : Submodule (ZMod 2) W,
        (∀ g w, w ∈ A → ρ g w ∈ A) → A ≠ ⊤ →
        ∀ v : F.U, (v : G) ∈ V →
          ((c.coordinates v).toAdd ∈ A ↔ (v : G) ∈ F.Vi 1) := by
  let := h.chosen.elementary
  let := hab
  let := elementary_U F
  obtain ⟨ρ, ⟨c⟩⟩ := exists_section F
  exact ⟨Additive (F.U ⧸ (F.Vi 1).subgroupOf F.U), inferInstance, inferInstance,
    ρ, c, fun A hA hp => seed_intersection h c A hA hp⟩

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
