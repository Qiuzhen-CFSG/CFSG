module
public import CFSG.Quasithin.ChapterF.Section05.ExceptionalLocal.FusionFacts
public import CFSG.Quasithin.ChapterF.Section05.ModelEdge
public import Theory.SpecificGroups.OmegaSixThree.EdgeCardinality

/-!
# The original F.5 local normalizer escapes the vertex

The graph centralizer inside the concrete model vertex has order1440, as
computed from its36 neighbors. A graph-marked source vertex comparison carries
any hypothetical contained Sylow R of the source graph centralizer into this
model centralizer. The original fusion results give R order64, contradicting
Lagrange's theorem. Since the original R normalizes A₂, H=N_G(A₂) also escapes
the vertex. This removes the properness input needed to orient H≃S₄×S₄.

Only the actual vertex comparison and its literal graph mark remain explicit;
the original source hypotheses discharge all fusion and Sylow cardinalities.
Source: Aschbacher--Smith F.5.4--F.5.7, printed pp.301--303.
-/

public section

namespace CFSG.Quasithin.ChapterF.Section05.ExceptionalLocal
open Subgroup Theory.GroupTheory
open GreenBook.LieModels.UnitaryFour
open CompletionRecognition
open OmegaSixThree.OrthogonalityGraph (modelSystem)
local notation "hn" => Nat.le_refl 1
variable {G G0 : Type*} [Group G] [Group G0] [Finite G]
variable (c : RankTwoAmalgam.FaithfulCompletion (Extension.amalgam 1 hn) (G := G0))
  (i : G0 →* G) (z : pointParabolic 1 hn) (h : Source.Hypotheses c i z)
  (eV : modelSystem.vertexGroup ≃* i.range)
  (hgraph : (eV modelGraphElement : G) = Source.graphElement c i)
include h hgraph

/-- A graph-centralizer Sylow subgroup of order64 cannot be contained in the
source vertex, whose marked graph centralizer has order1440. -/
theorem source_Rimage_not_le_vertex (R : Sylow 2 (C c i)) :
    ¬ Rimage c i R ≤ i.range := by
  intro hRM
  let j : Rimage c i R →* modelSystem.vertexGroup :=
    eV.symm.toMonoidHom.comp (Subgroup.inclusion hRM)
  have hj (r : Rimage c i R) : eV (j r) = Subgroup.inclusion hRM r :=
    eV.apply_symm_apply _
  let C0 := centralizer ({modelGraphElement} : Set modelSystem.vertexGroup)
  have hC (r : Rimage c i R) : j r ∈ C0 := by
    apply mem_centralizer_singleton_iff.mpr
    apply eV.injective
    rw [map_mul,map_mul,hj]
    apply Subtype.ext
    change r.val * (eV modelGraphElement : G) = (eV modelGraphElement : G) * r.val
    rw [hgraph]
    exact mem_centralizer_singleton_iff.mp (Rimage_le_C c i R r.property)
  let f : Rimage c i R →* C0 := j.codRestrict C0 hC
  have hjinj : Function.Injective j :=
    eV.symm.injective.comp (Subgroup.inclusion_injective hRM)
  have hfinj : Function.Injective f := by
    intro a b hab
    exact hjinj (congrArg Subtype.val hab)
  have hd := Subgroup.card_dvd_of_injective f hfinj
  have hRcard : Nat.card (Rimage c i R) = 64 :=
    normalizer_R_card c i z (sourceMarkedShort c i) (source_fusionFacts c i z h) R
  have hCcard : Nat.card C0 = 1440 := OmegaSixThree.card_vertex_graph_centralizer
  rw [hRcard,hCcard] at hd
  exact (by decide : ¬64 ∣ 1440) hd

/-- The original local normalizer escapes the actual source vertex. This
removes the properness premise in the source local-intersection comparison. -/
theorem source_H_not_le_vertex (R : Sylow 2 (C c i))
    (hR : Tf c i ≤ (R : Subgroup (C c i))) : ¬ H c i ≤ i.range := by
  intro hH
  exact source_Rimage_not_le_vertex c i z h eV hgraph R
    ((source_R_le_H c i z h R hR).trans hH)

end CFSG.Quasithin.ChapterF.Section05.ExceptionalLocal
