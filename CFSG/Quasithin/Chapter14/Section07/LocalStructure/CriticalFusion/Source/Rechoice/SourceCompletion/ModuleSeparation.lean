module

public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Rechoice.SourceCompletion.SeedAction
public import CFSG.Quasithin.Chapter12.Section08.Preliminary.NormalL1

/-!
# The genuine module-separation conclusion of14.7.2(1)

Pull a proper H-invariant subspace back to the original group U. Its
intersection with V is invariant under L₁, so natural simplicity makes it
V₁ or V. The latter would contain all H-conjugates of V and therefore all
of U, contradicting properness. This proves the precise ModuleSeparation
input using the actual coordinate map and no additional source premise.

Source: Aschbacher–Smith,14.7.2(1),printed p.1043.
-/

public section
noncomputable section
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Rechoice.SourceCompletion
open Subgroup Representation Chapter12.Section08
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3} {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
  (d : Data T L V F W)

/-- Every proper H-submodule intersects the natural seed exactly in the point. -/
theorem moduleSeparation : d.ModuleSeparation := by
  let := d.natural.chosen.elementary
  let := F.localKernel_tilde_seed_elementary
  intro A hA hproper
  let I : Subgroup G :=
    (A.toAddSubgroup.toSubgroup.comap d.conjugationSection.coordinates).map F.U.subtype
  have memI (u : F.U) : (u : G) ∈ I ↔
      (d.conjugationSection.coordinates u).toAdd ∈ A := by
    constructor
    · rintro ⟨v, hv, he⟩
      exact (Subtype.ext he : v = u) ▸ hv
    · intro hu
      exact ⟨u, hu, rfl⟩
  have hIU : I ≤ F.U := by rintro _ ⟨u, _, rfl⟩; exact u.property
  have hPI : F.Vi 1 ≤ I := by
    intro v hv
    apply (memI ⟨v, d.conjugationSection.kernel_le hv⟩).mpr
    rw [(d.conjugationSection.coordinates_eq_one_iff _).mpr hv]
    exact A.zero_mem
  have hclosed (h : F.H) {v : G} (hv : v ∈ I) : (h : G) * v * (h : G)⁻¹ ∈ I := by
    let u : F.U := ⟨v, hIU hv⟩
    apply (memI ⟨_, (mem_normalizer_iff.mp
      (d.conjugationSection.normalized h.property) v).mp u.property⟩).mpr
    rw [d.conjugationSection.equivariant h u]
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
    le_normalizer_inf ((F.Li_le L 1).trans (inf_le_left.trans d.natural.chosen.normalizes))
      (((F.Li_le L 1).trans inf_le_right).trans hHI)
  have split := F.invariant_subgroup_of_ambient_natural d.natural.naturalMarking
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
      obtain ⟨u, hu⟩ := d.conjugationSection.onto (Multiplicative.ofAdd w)
      have hw := (memI u).mp (hUI u.property)
      rw [hu] at hw
      exact hw
  intro v hv
  constructor
  · intro ha
    exact hinter ▸ (show (v : G) ∈ V ⊓ I from ⟨hv, (memI v).mpr ha⟩)
  · intro hp
    rw [(d.conjugationSection.coordinates_eq_one_iff _).mpr hp]
    exact A.zero_mem

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Rechoice.SourceCompletion
