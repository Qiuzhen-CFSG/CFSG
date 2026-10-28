module

public import CFSG.Quasithin.ChapterF.Section05.ExceptionalLocal.Data
public import CFSG.Quasithin.ChapterF.Section04.SourceCompletion.UnitaryTwo.Extension

/-!
# Transport and intersections for the exceptional source groups

Injectivity identifies the literal endpoint centralizers with images of the
model centralizers. The ordinary fixed groups consequently lie in them and
generate a subgroup of C_G(f). The full endpoint intersection is the marked
overlap, by the existing coprime-index calculation in the completion.

The final lemma converts the exceptional source condition into a strict
Sylow overgroup of C_T(f), once the F.4.33 two-group fact is supplied. This
is the Sylow arrangement used in F.4.37 and F.5.4; it makes no recognition
assumption.

Source: Aschbacher--Smith, F.4.37(2)--(4), printed p.293, and F.5, pp.300--302.
-/

@[expose] public noncomputable section

namespace CFSG.Quasithin.ChapterF.Section05.ExceptionalLocal

open Subgroup Theory.GroupTheory
open GreenBook.LieModels.UnitaryFour
open UnitaryTwo.GraphCentralizer
local notation "hn" => Nat.le_refl 1

variable {G G0 : Type*} [Group G] [Group G0]
variable (c : RankTwoAmalgam.FaithfulCompletion (Extension.amalgam 1 hn) (G := G0))
  (i : G0 →* G)

theorem endpointMap_injective (hi : Function.Injective i) (b : Bool) :
    Function.Injective (endpointMap c i b) := by
  cases b
  · exact hi.comp c.left_injective
  · exact hi.comp c.right_injective

theorem endpointMap_graph (b : Bool) :
    endpointMap c i b (modelGraph b) = Source.graphElement c i := by
  cases b
  · rfl
  · exact congrArg i (DFunLike.congr_fun c.compatible graphInvolution).symm

/-- Both images retain the same distinguished overlap element. -/
theorem graph_mem_M (b : Bool) : Source.graphElement c i ∈ M c i b :=
  ⟨modelGraph b, endpointMap_graph c i b⟩

theorem graph_mem_C : Source.graphElement c i ∈ C c i :=
  mem_centralizer_singleton_iff.mpr rfl

theorem graph_mem_E (b : Bool) : Source.graphElement c i ∈ E c i b :=
  ⟨graph_mem_M c i b, graph_mem_C c i⟩

/-- No alternate abstract centralizer replaces the marked endpoint image. -/
theorem E_eq_map_centralizer (hi : Function.Injective i) (b : Bool) :
    E c i b = (centralizer ({modelGraph b} : Set (modelEndpoint b))).map
      (endpointMap c i b) := by
  apply le_antisymm
  · rintro _ ⟨⟨x, rfl⟩, hx⟩
    refine ⟨x, mem_centralizer_singleton_iff.mpr ?_, rfl⟩
    apply endpointMap_injective c i hi b
    rw [map_mul, map_mul, endpointMap_graph]
    exact mem_centralizer_singleton_iff.mp hx
  · rintro _ ⟨x, hx, rfl⟩
    refine ⟨⟨x, rfl⟩, mem_centralizer_singleton_iff.mpr ?_⟩
    rw [← endpointMap_graph c i b]
    exact (map_mul (endpointMap c i b) _ _).symm.trans
      ((congrArg (endpointMap c i b) (mem_centralizer_singleton_iff.mp hx)).trans
        (map_mul (endpointMap c i b) _ _))

theorem Dendpoint_le_E (b : Bool) : Dendpoint c i b ≤ E c i b := by
  rintro _ ⟨x, hx, rfl⟩
  refine ⟨⟨ordinaryInclusion b x, rfl⟩, mem_centralizer_singleton_iff.mpr ?_⟩
  change endpointMap c i b (ordinaryInclusion b x) * Source.graphElement c i =
    Source.graphElement c i * endpointMap c i b (ordinaryInclusion b x)
  rw [← endpointMap_graph c i b]
  exact (map_mul (endpointMap c i b) _ _).symm.trans
    ((congrArg (endpointMap c i b) (mem_centralizer_singleton_iff.mp hx)).trans
      (map_mul (endpointMap c i b) _ _))

theorem D_le_C : D c i ≤ C c i :=
  sup_le ((Dendpoint_le_E c i false).trans inf_le_right)
    ((Dendpoint_le_E c i true).trans inf_le_right)

theorem M_le_completion (b : Bool) : M c i b ≤ i.range := by
  cases b <;> rintro _ ⟨x, rfl⟩
  · exact ⟨c.left x, rfl⟩
  · exact ⟨c.right x, rfl⟩

theorem D_le_completion : D c i ≤ i.range :=
  sup_le ((Dendpoint_le_E c i false).trans (inf_le_left.trans (M_le_completion c i false)))
    ((Dendpoint_le_E c i true).trans (inf_le_left.trans (M_le_completion c i true)))

theorem A_le_E (b : Bool) : A c i b ≤ E c i b := pCoreIn_le 2 _

theorem A_isPGroup (b : Bool) : IsPGroup 2 (A c i b) := isPGroup_pCoreIn 2 _

theorem E_le_normalizer_A (b : Bool) : E c i b ≤ normalizer (A c i b : Set G) := by
  simpa only [A, pCoreIn, normalizer_eq_top, ← MonoidHom.range_eq_map, range_subtype]
    using (pCore 2 (E c i b)).le_normalizer_map (E c i b).subtype

/-- Only relative normality in Eᵢ is asserted. -/
theorem A_normal_in_E (b : Bool) : ((A c i b).subgroupOf (E c i b)).Normal :=
  (normal_subgroupOf_iff_le_normalizer (A_le_E c i b)).mpr (E_le_normalizer_A c i b)

theorem E_plane_le_H : E c i true ≤ H c i := E_le_normalizer_A c i true

/-- The Sylow centralizer is the literal intersection inside G. -/
theorem TfImage_eq : TfImage c i = Source.sylowImage c i ⊓ C c i :=
  subgroupOf_map_subtype _ _

theorem sylowImage_le_M (b : Bool) : Source.sylowImage c i ≤ M c i b := by
  rintro _ ⟨x, _, rfl⟩
  cases b
  · exact ⟨(Extension.amalgam 1 hn).left x, rfl⟩
  · exact ⟨(Extension.amalgam 1 hn).right x,
      congrArg i (DFunLike.congr_fun c.compatible x).symm⟩

theorem TfImage_le_E (b : Bool) : TfImage c i ≤ E c i b := by
  rw [TfImage_eq]
  exact inf_le_inf (sylowImage_le_M c i b) le_rfl

/-- The entire marked overlap, not its two-core, is the intersection. -/
theorem M_intersection (hi : Function.Injective i) :
    M c i false ⊓ M c i true = (i.comp c.middle).range := by
  have hl : c.left.range.map i = (i.comp c.left).range := MonoidHom.range_comp _ _ |>.symm
  have hr : c.right.range.map i = (i.comp c.right).range := MonoidHom.range_comp _ _ |>.symm
  change (i.comp c.left).range ⊓ (i.comp c.right).range = _
  rw [← hl, ← hr, ← map_inf _ _ i hi,
    SourceCompletion.UnitaryTwo.Extension.Completion.overlap c]
  exact (MonoidHom.range_comp _ _).symm

theorem E_intersection (hi : Function.Injective i) :
    E c i false ⊓ E c i true = (i.comp c.middle).range ⊓ C c i := by
  rw [E, E, inf_inf_inf_comm, inf_idem, M_intersection c i hi]

theorem Rimage_le_C (R : Sylow 2 (C c i)) : Rimage c i R ≤ C c i :=
  map_subtype_le _

/-- The exceptional hypothesis yields the strict Sylow enlargement used by
F.4.37. The source proof of the remaining two-group premise is F.4.33. -/
theorem exists_strict_sylow [Finite G]
    (hT : IsPGroup 2 (Source.sylowImage c i)) (hex : Source.Exceptional c i) :
    ∃ R : Sylow 2 (C c i), Tf c i < (R : Subgroup (C c i)) := by
  have hp : IsPGroup 2 (Tf c i) := hT.comap_subtype
  obtain ⟨R, hR⟩ := hp.exists_le_sylow
  refine ⟨R, lt_of_le_of_ne hR ?_⟩
  intro he
  exact hex ⟨R, he.symm⟩

end CFSG.Quasithin.ChapterF.Section05.ExceptionalLocal
