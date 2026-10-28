module

public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.SylowGeometry.CoreElimination.BlockSieve.ExchangedCases.SL3Geometry.SourceCases.Branch
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.SylowGeometry.CoreElimination.BlockSieve.ExchangedCases.SL3Geometry.SourceCases.Reduction

/-!
# The complete SL₃ source-case reduction

We apply the universal C.1.34 implication to the genuine C.2.7(g) MS-pair
inside D=LR. The supplied binary quotient is transported from K₁ to its
intrinsic component in D. The specified Sylow image proves R≤S.
Cases (1)–(4) then construct actual core-center sections, transported back
to the component in H; case (5) supplies the central omega alternative.

The earlier theorem parameter is the complete universal C.1.34 statement,
including both MS2 alternatives and all five natural/dual configurations.
Its proof and the C.2.7(g) branch remain the source assembly's obligations.
This module does not identify the full internal H-module with the local
omega module. Local radicality is not needed for this section construction;
the parent owns its discharge and the final contradiction assembly.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), C.1.31–34,
printed pp.135–137; C.2.7(1)–(3), pp.145–147; 15.4.20, p.1164.
-/

@[expose] public section
open Subgroup Stellmacher CFSG.Quasithin.ChapterC
namespace CFSG.Quasithin.Chapter15.Section04.LocalSetup.CoreElimination.BlockSieve.ExchangedCases.SL3Geometry.SourceCases
universe u
variable {G : Type u} [Group G] [Finite G]
variable {d : Source.Geometry G} {i j : Bool} {H U K K₁ : Subgroup G} {r : G}

omit [Finite G] in
/-- The source radical lies in every local Sylow with the prescribed image. -/
theorem source_radical_le_local_sylow (h : Input d i j H U K) (L : Subgroup H)
    (S : Sylow 2 (L ⊔ (sourceRadical d U).subgroupOf H : Subgroup H))
    (hS : (S : Subgroup _).map (L ⊔ (sourceRadical d U).subgroupOf H : Subgroup H).subtype =
      (h.placed.sylow : Subgroup H) ⊓ (L ⊔ (sourceRadical d U).subgroupOf H)) :
    ((sourceRadical d U).subgroupOf H).subgroupOf (L ⊔ (sourceRadical d U).subgroupOf H) ≤
      (S : Subgroup _) := by
  intro x hx
  have hxU := h.radical_le_sylow hx
  have hximage : ((x : H) : G) ∈ (h.placed.sylow : Subgroup H).map H.subtype :=
    h.placed.sylow_image.symm ▸ hxU
  obtain ⟨y, hy, he⟩ := hximage
  have hxP : (x : H) ∈ (h.placed.sylow : Subgroup H) :=
    (Subtype.ext he : y = (x : H)) ▸ hy
  have hxmap : (x : H) ∈ (S : Subgroup _).map
      (L ⊔ (sourceRadical d U).subgroupOf H : Subgroup H).subtype := by
    rw [hS]
    exact ⟨hxP, x.property⟩
  obtain ⟨z, hz, hez⟩ := hxmap
  exact (Subtype.ext hez : z = x) ▸ hz

/-- After C.2.2 supplies local radicality, the actual star kernel is the
local core. This uses the proved local-module comparison, not an identification
of the full H-module with the local omega module. -/
theorem source_starKernel_eq_core (h : Input d i j H U K) (L : Subgroup H)
    (hn : (sourceRadical d U).subgroupOf H ≤ normalizer (L : Set H))
    (hr : IsPRadical 2 (((sourceRadical d U).subgroupOf H).subgroupOf
      (L ⊔ (sourceRadical d U).subgroupOf H))) :
    starKernel L ((sourceRadical d U).subgroupOf H) =
      pCore 2 (L ⊔ (sourceRadical d U).subgroupOf H : Subgroup H) :=
  (h.local_module_comparison L hn hr).2.2.2.2

/-- Transport the actual supplied binary quotient through both intrinsic
realizations of the selected component. -/
noncomputable def selected_local_quotient_equiv (s : Selected H U K K₁ r)
    (binary : (K₁ ⧸ pCore 2 K₁) ≃* Natural.Actor) :
    (((K₁.subgroupOf H).subgroupOf
      (K₁.subgroupOf H ⊔ (sourceRadical d U).subgroupOf H)) ⧸
      pCore 2 ((K₁.subgroupOf H).subgroupOf
        (K₁.subgroupOf H ⊔ (sourceRadical d U).subgroupOf H))) ≃* Natural.Actor := by
  let e := subgroupOfEquivOfLe
    (show K₁.subgroupOf H ≤ K₁.subgroupOf H ⊔ (sourceRadical d U).subgroupOf H from le_sup_left)
  exact (QuotientGroup.congr _ _ e (pCore_map_iso 2 e)).trans
    (s.internalQuotientEquiv.symm.trans binary)

/-- C.1.34 gives the required disjunction for every Sylow having the actual
intersection image. The classifier parameter is universal, with all source
hypotheses and all five conclusions; no section is an input hypothesis. -/
theorem source_cases (classification : UniversalClassification.{u})
    (h : Input d i j H U K) (s : Selected H U K K₁ r) (κ : GroupClass.{u})
    (hc : ComponentHypotheses κ H ((sourceRadical d U).subgroupOf H)
      (d.M₁.subgroupOf H) (K₁.subgroupOf H))
    (branch : SL3Branch κ (K₁.subgroupOf H) ((sourceRadical d U).subgroupOf H)
      (d.M₁.subgroupOf H))
    (binary : (K₁ ⧸ pCore 2 K₁) ≃* Natural.Actor)
    (S : Sylow 2 (K₁.subgroupOf H ⊔ (sourceRadical d U).subgroupOf H : Subgroup H))
    (hS : (S : Subgroup _).map
      (K₁.subgroupOf H ⊔ (sourceRadical d U).subgroupOf H : Subgroup H).subtype =
        (h.placed.sylow : Subgroup H) ⊓ (K₁.subgroupOf H ⊔ (sourceRadical d U).subgroupOf H)) :
    Nonempty (CoreCenterSection (K₁.subgroupOf H) 1) ∨
      Nonempty (CoreCenterSection (K₁.subgroupOf H) 2) ∨
      omegaOneCenterAmbient (S : Subgroup
        (K₁.subgroupOf H ⊔ (sourceRadical d U).subgroupOf H : Subgroup H)) ≤ center _ := by
  let L := K₁.subgroupOf H
  let R := (sourceRadical d U).subgroupOf H
  let D := L ⊔ R
  let LD := L.subgroupOf D
  let RD := R.subgroupOf D
  have hLD : LD.IsCComponent := hc.component.subgroupOf le_sup_left
  obtain ⟨e, he⟩ := classification κ D LD RD branch.1 (ZMod 2) 1 (by decide)
    (by simp) ⟨selected_local_quotient_equiv s binary⟩ S (source_radical_le_local_sylow h L S hS)
  rcases Alternatives.sections_or_central hLD S he with hm | hm | hz
  · obtain ⟨m⟩ := hm
    exact Or.inl ⟨transportSection (subgroupOfEquivOfLe (show L ≤ D from le_sup_left)).symm m⟩
  · obtain ⟨m⟩ := hm
    exact Or.inr (Or.inl
      ⟨transportSection (subgroupOfEquivOfLe (show L ≤ D from le_sup_left)).symm m⟩)
  · exact Or.inr (Or.inr hz)

end CFSG.Quasithin.Chapter15.Section04.LocalSetup.CoreElimination.BlockSieve.ExchangedCases.SL3Geometry.SourceCases
