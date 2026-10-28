module
public import CFSG.Quasithin.ChapterF.Section05.ExceptionalLocal.FusionClasses
public import CFSG.Quasithin.ChapterF.Section05.ExceptionalLocal.FusionEndpointClasses
public import CFSG.Quasithin.ChapterF.Section05.ExceptionalLocal.FusionEndpointsCore
public import CFSG.Quasithin.ChapterF.Section05.ExceptionalLocal.NormalizerCore

/-!
# The original F.5 fusion facts, with all source inputs discharged

The literal doubled completion determines the marked short involution.
The independent Sylow, endpoint and conjugacy calculations construct every
field of `FusionFacts` from the original source hypotheses. In particular,
exceptionality is proved by transfer and no local recognition or fusion
premise remains.

As an immediate consumer, the completed record proves that every chosen
Sylow overgroup of the graph centralizer's marked two-subgroup normalizes
the actual second elementary core. The final generation theorem then needs
only the later F.5.5 graph-centralizer description.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, F.4.33–38
and F.5.3–6, printed pp.291–294 and 300–304.
-/

@[expose] public noncomputable section
namespace CFSG.Quasithin.ChapterF.Section05.ExceptionalLocal
open Subgroup Theory.GroupTheory
open GreenBook.LieModels.UnitaryFour
local notation "hn" => Nat.le_refl 1
variable {G G0 : Type*} [Group G] [Group G0] [Finite G]
variable (c : RankTwoAmalgam.FaithfulCompletion (Extension.amalgam 1 hn) (G := G0))
  (i : G0 →* G)

/-- The full original F.5 fusion input, with every local premise discharged. -/
theorem source_fusionFacts (z : pointParabolic 1 hn)
    (h : Source.Hypotheses c i z) :
    FusionFacts c i z (sourceMarkedShort c i) where
  sylow := source_sylowImage_isSylow c i z h
  sylow_card := source_sylowImage_card c i h.embedding_injective
  tf_card := source_Tf_card c i h.embedding_injective
  tf_sylow b := source_Tf_sylow_of_endpoint_equiv c i h.embedding_injective b
    (source_E_equiv c i h.embedding_injective b)
  root_centralizer := source_root_centralizer c i z h
  t_mem := source_short_mem_sylowImage c i
  t_order := source_short_order c i h.embedding_injective
  t_commutator := source_short_commutator c i h.embedding_injective
  t_commutes_graph := source_short_commutes_graph c i
  t_commutes_root := source_short_commutes_root c i z h
  t_sylow := source_short_sylow_of_hypotheses c i z h
  t_centralizer_iso := source_short_Tcentralizer_iso c i h.embedding_injective
  two_classes := source_two_involution_classes c i z h
  graph_fuses_t := source_short_fusion_of_hypotheses c i z h
  root_fuses_graph_root := source_root_product_fusion c i z h
  root_fuses_graph_t_root := source_root_short_product_fusion c i z h
  t_fuses_t_root := source_short_root_conjugator c i z h
  E_iso b := ⟨source_E_equiv c i h.embedding_injective b⟩
  Dendpoint_iso b := ⟨source_Dendpoint_equiv c i h.embedding_injective b⟩
  A_elementary := source_A_elementary c i h.embedding_injective
  A_card := source_A_card c i h.embedding_injective
  root_mem_A := source_root_mem_A c i z h
  root_class_A_point := source_root_class_A_point c i z h
  root_class_A_plane := source_root_class_A_plane c i z h
  root_class_Q_plane := source_root_class_Q_plane c i z h


/-- The original graph-centralizer Sylow overgroup normalizes the literal A₂. -/
theorem source_R_le_H (z : pointParabolic 1 hn)
    (h : Source.Hypotheses c i z)
    (R : Sylow 2 (C c i)) (hR : Tf c i ≤ (R : Subgroup (C c i))) :
    Rimage c i R ≤ H c i :=
  normalizer_R_le_H c i z (sourceMarkedShort c i) (source_fusionFacts c i z h) R hR

/-- The F.5.5 centralizer description is now the only earlier source premise
needed by the controlled F.5.6 generation argument. -/
theorem source_generation_of_graph_centralizer (z : pointParabolic 1 hn)
    (h : Source.Hypotheses c i z)
    (R : Sylow 2 (C c i)) (hR : Tf c i ≤ (R : Subgroup (C c i)))
    (hcentral : C c i = Rimage c i R ⊔ D c i) :
    i.range ⊔ H c i = ⊤ :=
  source_generation_of_centralizer_description c i z h R hR
    (source_R_le_H c i z h R hR) hcentral

end CFSG.Quasithin.ChapterF.Section05.ExceptionalLocal
