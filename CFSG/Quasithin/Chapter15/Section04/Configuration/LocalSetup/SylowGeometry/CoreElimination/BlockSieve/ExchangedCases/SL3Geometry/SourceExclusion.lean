module

public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.SylowGeometry.CoreElimination.BlockSieve.ExchangedCases.SL3Geometry.SourceCases
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.SylowGeometry.CoreElimination.BlockSieve.ExchangedCases.SL3Geometry.Local
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.SylowGeometry.CoreElimination.BlockSieve.ExchangedCases.LinearThreeModels

/-!
# The SL₃ branch is impossible in the contrary Sylow configuration

The actual selected component and the source radical construct a local Sylow
subgroup with the prescribed intersection image. The complete universal C.1.34
implication then produces either a natural core-center section or the central
omega conclusion. The first two alternatives contradict the faithful internal
H-module; the last puts the component in the seed's Sylow centralizer.

Thus no local Sylow, natural section or central-omega conclusion is an extra
input. Local radicality identifies the starred component with its original
core quotient; comparison with the swapped embedding forces the binary SL₃
model. The stronger endpoint retains only the earlier C.1.34 implication,
the genuine C.2.7(g) branch and the local radical consequence of C.2.2(3).

Source: Aschbacher–Smith, combined manuscript (1 March 2004), C.1.34,
printed pp.136–137, and the characteristic-two paragraph of 15.4.20, p.1164.
-/

public section

open Subgroup
namespace CFSG.Quasithin.Chapter15.Section04.LocalSetup.CoreElimination.BlockSieve.ExchangedCases.SL3Geometry
universe u
variable {G : Type u} [Group G] [Finite G]
variable {d : Source.Geometry G} {i j : Bool} {H U K K₁ : Subgroup G} {r : G}

private noncomputable def quotientImageEquiv
    {D : Type u} [Group D] [Finite D] (L : Subgroup D) (hL : L.IsCComponent)
    (N : Subgroup D) [N.Normal] (hN : N = pCore 2 D) :
    (L ⧸ pCore 2 L) ≃* L.map (QuotientGroup.mk' N) := by
  subst N
  exact cComponentTwoCoreQuotientEquiv hL

/-- Local radicality identifies the selected component's original core
quotient with its image in the starred local group. -/
noncomputable def source_componentStarEquiv
    (h : Input d i j H U K) (s : Selected H U K K₁ r)
    (hn : (sourceRadical d U).subgroupOf H ≤ normalizer (K₁.subgroupOf H : Set H))
    (hr : IsPRadical 2 (((sourceRadical d U).subgroupOf H).subgroupOf
      (K₁.subgroupOf H ⊔ (sourceRadical d U).subgroupOf H))) :
    (K₁ ⧸ pCore 2 K₁) ≃* SourceCases.starComponent
      (K₁.subgroupOf H) ((sourceRadical d U).subgroupOf H) := by
  let L := K₁.subgroupOf H
  let R := (sourceRadical d U).subgroupOf H
  let D := L ⊔ R
  let e := (subgroupOfEquivOfLe (show L ≤ D from le_sup_left)).symm
  let eqv : (K₁ ⧸ pCore 2 K₁) ≃* ((L.subgroupOf D) ⧸ pCore 2 (L.subgroupOf D)) :=
    s.internalQuotientEquiv.trans (QuotientGroup.congr _ _ e (pCore_map_iso 2 e))
  have hk := SourceCases.source_starKernel_eq_core h (K₁.subgroupOf H) hn hr
  exact eqv.trans (quotientImageEquiv (L.subgroupOf D)
    (s.component.2.subgroupOf le_sup_left) (SourceCases.starKernel L R) hk)

/-- All five cases of the full C.1.34 implication contradict the original
source module, using the selected component and its literal binary quotient. -/
theorem not_source_SL3Branch
    (classification : SourceCases.UniversalClassification.{u})
    (h : Input d i j H U K) (s : Selected H U K K₁ r) (κ : GroupClass.{u})
    (hc : ComponentHypotheses κ H ((sourceRadical d U).subgroupOf H)
      (d.M₁.subgroupOf H) (K₁.subgroupOf H))
    (branch : SourceCases.SL3Branch κ (K₁.subgroupOf H)
      ((sourceRadical d U).subgroupOf H) (d.M₁.subgroupOf H))
    (binary : (K₁ ⧸ pCore 2 K₁) ≃* Natural.Actor) : False := by
  obtain ⟨S, hS⟩ := source_local_sylow h s hc.normalized
  rcases SourceCases.source_cases classification h s κ hc branch binary S hS with
    ⟨m⟩ | ⟨m⟩ | hz
  · exact not_source_coreCenterSection h s m.some
  · exact not_source_coreCenterSection h s m.some
  · exact not_source_local_central_omega h s S hS hz

/-- The C.2.7(g) field and the actual swapped model force the binary quotient,
so C.1.34 excludes this branch without any chosen model as an input. The
remaining radical premise is exactly the normalized-component consequence
of C.2.2(3) in the local product. -/
theorem not_source_SL3Branch_of_local_radical
    (classification : SourceCases.UniversalClassification.{u})
    (h : Input d i j H U K) (s : Selected H U K K₁ r) (κ : GroupClass.{u})
    (hc : ComponentHypotheses κ H ((sourceRadical d U).subgroupOf H)
      (d.M₁.subgroupOf H) (K₁.subgroupOf H))
    (branch : SourceCases.SL3Branch κ (K₁.subgroupOf H)
      ((sourceRadical d U).subgroupOf H) (d.M₁.subgroupOf H))
    (hr : IsPRadical 2 (((sourceRadical d U).subgroupOf H).subgroupOf
      (K₁.subgroupOf H ⊔ (sourceRadical d U).subgroupOf H))) : False := by
  obtain ⟨F, hF, hfin, n, hn, hcard, e, _⟩ := branch.2
  let model := (source_componentStarEquiv h s hc.normalized hr).trans e
  obtain ⟨_, ⟨binary⟩, _, _⟩ := slThree_models_of_swapped hn hcard model s.model
  exact not_source_SL3Branch classification h s κ hc branch binary

end CFSG.Quasithin.Chapter15.Section04.LocalSetup.CoreElimination.BlockSieve.ExchangedCases.SL3Geometry
