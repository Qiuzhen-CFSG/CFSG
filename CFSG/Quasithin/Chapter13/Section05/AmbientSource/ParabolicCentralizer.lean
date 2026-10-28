module

public import CFSG.Quasithin.Chapter13.Section05.PlaneGeometry.TwoBlocks.SourceContainment.ParabolicGeneration
public import CFSG.Quasithin.Chapter13.Section05.AmbientSource.Centralizer
public import CFSG.Quasithin.Chapter13.Section07.ModelExclusions.NaturalModels
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.Consequences
public import CFSG.Quasithin.ChapterA.Section02.SourceAssembly.Complete

/-!
# The original seed-centralizer containment in the ordinary A₆ branch

The literal plane actor supplies its cubic image and two-group kernel.
Its full ambient plane-normalizer invariance follows from source plane
noncentrality. The new parabolic conjugate-generation theorem places the
seed centralizer in N_G(L), and the genuine Chapter12 chosen-module TI
theorem places it in N_G(V). The natural coordinates discharge its trivial
relative centralizer premise; original A and C are supplied by their
complete source producers.

The only earlier source premises retained are Hypothesis12.2.1 and the
point-core/plane noncentrality, for the actual original T,L,V and flag.
Source: Aschbacher--Smith,13.5.4(4), printed p.916.
-/

@[expose] public section
open Subgroup BinaryPermutation
namespace CFSG.Quasithin.Chapter13.Section05.AmbientSource
open Section08.SourceCompletion PlaneGeometry.TwoBlocks
universe u
variable {G:Type u} [Group G] [Finite G] {T:Sylow 2 G}
  {L V V₁ V₂ V₃ M G₁:Subgroup G}

/-- The literal earlier centralizer input, with parabolic generation and
all plane-actor action inputs discharged. -/
theorem source_parabolic_centralizer
    (d:NaturalSetup T L V V₁ V₂ V₃ M G₁)
    (e:(L⧸pCore 2 L)≃*alternatingGroup (Fin 6))
    (h1221:Chapter12.Section02.Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hm:⁅(normalizer (V₁:Set G)).pCoreIn 2,V₂⁆≠⊥) :
    centralizer (V₃:Set G)≤M⊓normalizer (V:Set G) := by
  have hc:V⊓centralizer (L:Set G)=⊥:=by
    have hh:=congrArg (Subgroup.map V.subtype) (Section07.ModelExclusions.NaturalModels.centralizer_bot d)
    change ((centralizer (L:Set G)).subgroupOf V).map V.subtype=(⊥:Subgroup V).map V.subtype at hh
    rwa [subgroupOf_map_subtype,Subgroup.map_bot,inf_comm] at hh
  obtain ⟨hx,hk⟩:=Ordinary.planeActor_action_source d e
  exact source_centralizer_of_noncentrality d (planeActor (L:=L) (V₂:=V₂))
    (planeActor_le.trans inf_le_right) (planeActor_normalized d) planeActor_twoPerfect hx hk hm
    (Ordinary.source_parabolic_generation d e)
    (d.chosen.ti_of_centralizer_eq_bot h1221
      (fun X _ _=>ChapterA.Section02.theoremA_knownSimple (G:=X))
      (fun X _ _=>ChapterA.Section02.theoremC_knownSimple (G:=X)) hc)

end CFSG.Quasithin.Chapter13.Section05.AmbientSource
