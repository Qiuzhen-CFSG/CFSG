module

public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.SylowGeometry.CoreElimination.BlockSieve.SourceInputs
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.SylowGeometry.CoreElimination.BlockSieve.AlternatingFive

/-!
# Specializing the module comparisons to the source geometry

The actual radical O₂(XU) contains Z and centralizes it. Consequently,
for a component L normalized by R, its local Z-orbit inside LR embeds
in both the internal H-module and the C.2.7 omega module. Radicality in
LR is precisely the C.2.2(3) input to this comparison. Both local action
kernels equal the intrinsic O₂(LR).

The last two theorems connect the fixed-space obstruction to the given
Sylow subgroup of H. The alternating-five specialization still requires
the actual section and embedding to be constructed from the block.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), C.2.2(3)
and C.2.7, printed pp.144–147; 15.4.20, printed p.1164.
-/

public section
namespace CFSG.Quasithin.Chapter15.Section04.LocalSetup.CoreElimination.BlockSieve
open Subgroup Stellmacher Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
variable {G : Type*} [Group G] [Finite G]
variable {d : Source.Geometry G} {i j : Bool} {H U K : Subgroup G}

/-- Compare the actual orbit and omega modules in LR. The two supplied
premises are R-normalization and the local radical assertion of C.2.2(3). -/
theorem Input.local_module_comparison (h : Input d i j H U K) (L : Subgroup H)
    (hn : (sourceRadical d U).subgroupOf H ≤ normalizer (L : Set H))
    (hr : IsPRadical 2 (((sourceRadical d U).subgroupOf H).subgroupOf
      (L ⊔ (sourceRadical d U).subgroupOf H))) :
    let D := L ⊔ (sourceRadical d U).subgroupOf H
    let Z := d.Z.subgroupOf H
    (normalClosure (Z.subgroupOf D : Set D)).map D.subtype = conjugateModule L Z ∧
      conjugateModule L Z ≤ TwoFactors.FFBranch.moduleClosure Z ∧
      conjugateModule L Z ≤ (omegaCoreModule D).map D.subtype ∧
      centralizer (normalClosure (Z.subgroupOf D : Set D) : Set D) = pCore 2 D ∧
      centralizer (omegaCoreModule D : Set D) = pCore 2 D := by
  let R := (sourceRadical d U).subgroupOf H
  let D := L ⊔ R
  let Z := d.Z.subgroupOf H
  let : IsElementaryAbelian 2 Z := h.seed_inputs.2.1
  have hZR : Z ≤ R := fun _ hz => h.seed_le_radical hz
  have hZD : Z ≤ D := hZR.trans le_sup_right
  have hRC : R ≤ centralizer (Z : Set H) := by
    intro r hr z hz
    exact Subtype.ext (mem_centralizer_iff.mp (h.radical_centralizes_seed hr) z hz)
  have hQR := local_core_le_radical D R le_sup_right hr
  have hseed := seed_le_omegaCoreModule D R Z h.seed_le_core hQR hRC
  obtain ⟨he, hVH, hVW⟩ := local_orbit_comparison D L R Z le_sup_left le_sup_right hZD
    (sup_le L.le_normalizer hn) rfl h.seed_le_core hQR hRC
  have hC : IsPGroup 2 (centralizer (Z : Set H)) := by
    rw [show centralizer (Z : Set H) = (h.placed.sylow : Subgroup H) from
      h.seed_inputs.2.2.1]
    exact h.placed.sylow.isPGroup'
  exact ⟨he, hVH, hVW, comparison_centralizers D Z hZD hseed hC⟩

/-- No element outside the actual Sylow image can fix its entire fixed
space on the source's internal module. -/
theorem Input.no_fixedSpace_enlargement (h : Input d i j H U K) :
    let V := TwoFactors.FFBranch.moduleClosure (d.Z.subgroupOf H)
    letI := h.module_properties.1
    let ρ := coreAction V h.module_properties.2.2.2
    ∀ g : H ⧸ pCore 2 H,
      g ∉ (h.placed.sylow : Subgroup H).map (QuotientGroup.mk' _) →
      (∀ v ∈ fixedSpace ρ ((h.placed.sylow : Subgroup H).map (QuotientGroup.mk' _)),
        ρ g v = v) → False := by
  let := h.module_properties.1
  dsimp only
  intro g hg hfix
  exact BlockSieve.no_fixedSpace_enlargement _ _ h.module_properties.2.2.2
    (fun _ hz => le_normalClosure hz) h.placed.sylow h.seed_inputs.2.2.1 g hg hfix

/-- The source geometry excludes an actual alternating-five central section
on its internal module. Constructing the section from a block remains necessary. -/
theorem Input.not_alternatingFive_centralSection (h : Input d i j H U K) :
    let V := TwoFactors.FFBranch.moduleClosure (d.Z.subgroupOf H)
    letI := h.module_properties.1
    let ρ := coreAction V h.module_properties.2.2.2
    ∀ (f : alternatingGroup (Fin 5) →* (H ⧸ pCore 2 H)), Function.Injective f →
      ∀ (W : Subrepresentation (ρ.comp f))
        (q : W.toSubmodule →ₗ[ZMod 2] BinaryPermutation.natural (Fin 5)),
        (∀ g w, q (W.toRepresentation g w) =
          BinaryPermutation.naturalRepresentation (Fin 5) g.val (q w)) →
        (∀ g w, q w = 0 → W.toRepresentation g w = w) →
        (∀ g v, ρ (f g) v - v ∈ W) → False := by
  let := h.module_properties.1
  dsimp only
  intro f hf W q hq hker hquot
  exact BlockSieve.not_alternatingFive_centralSection _ _ h.module_properties.2.2.2
    (fun _ hz => le_normalClosure hz) h.placed.sylow h.seed_inputs.2.2.1
    f hf W q hq hker hquot

end CFSG.Quasithin.Chapter15.Section04.LocalSetup.CoreElimination.BlockSieve
