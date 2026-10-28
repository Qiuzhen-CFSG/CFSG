module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingTrivial.ResidualSection
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.LocalStructure.EarlierInputs
public import Theory.GroupTheory.PResidual.SylowSupplement

/-!
# The local actor and its nonzero neighborhood section

The intrinsic local actor has exactly the original vertex two-core, and
contains every short-distance neighboring two-span. Its two-residual
cannot centralize the neighborhood: the centralizer lies in the full
local kernel, so the residual and an edge Sylow would put the entire
local actor inside a two-closed edge. This contradicts its source
nonclosedness. Consequently the literal residual-centralizer section is
nonzero, with no recognition or fixed-generation hypothesis.

Source: DGS, *Groups and Graphs* (1985), 6.0--6.2 and 9.1--9.3,
printed pp.118--119 and 141--142. The section application is in
`CommutingTrivial.ResidualSource`.
-/

@[expose] public noncomputable section
open Subgroup Representation Representation.BinaryOffender
open Representation.NormalElementaryQuotient
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingTrivial
open Subgroup.CosetGeometry.RankTwo Theory.GroupTheory.AmalgamGraph
variable {G : Type*} [Group G] {P : Fin 2 → Subgroup G} {B : Subgroup G}

/-- The actual vertex core is contained in the intrinsic local actor. -/
theorem core_le_graphLocalGroup (h : LocallyRankOneTriple P B) (v : Vertex (family P)) :
    Q (family P) v ≤ graphLocalGroup (family P) v := by
  let := finite_endpoints h
  obtain ⟨T⟩ := Sylow.nonempty (p := 2) (G := stabilizer (family P) v)
  exact (pCoreIn_le_sylow _ T).trans (sylow_le_sylowGenerated _ T)

/-- The local-actor core is the original vertex core, with its ambient inclusion. -/
theorem graphLocalGroup_core (h : LocallyRankOneTriple P B) (v : Vertex (family P)) :
    (graphLocalGroup (family P) v).pCoreIn 2 = Q (family P) v := by
  let := finite_endpoints h
  apply le_antisymm
  · exact pCoreIn_mono_of_normalizes (sylowGenerated_le _) (sylowGenerated_normalized _)
  · exact le_pCoreIn_of_normalizes (isPGroup_pCoreIn 2 _) (core_le_graphLocalGroup h v)
      ((sylowGenerated_le _).trans (stabilizer_normalizes_Q (family P) v))

/-- The whole short-distance two-actor lies in the actual local group. -/
theorem neighbor_le_graphLocalGroup (h : LocallyRankOneTriple P B)
    (hS : ∀ v : Vertex (family P), ∃ T : Sylow 2 (U (family P) v),
      (T : Subgroup (U (family P) v)).map (U (family P) v).subtype = Q (family P) v)
    (v w : Vertex (family P)) (hb : 1 < b (family P))
    (hd : (graph (family P)).dist v w + 1 ≤ b (family P)) :
    V (family P) v 1 ≤ graphLocalGroup (family P) w := by
  let := finite_endpoints h
  have hp : IsPGroup 2 (V (family P) v 1) :=
    (isPGroup_pCoreIn 2 (stabilizer (family P) v)).to_le
      (V_le_Q (family P) h.generate (fun x => (source_Z_Q_U h x).1) hS v hb)
  have hVR := V_le_stabilizer (family P) h.generate v w hd
  obtain ⟨T, hT⟩ := (hp.comap_subtype (K := stabilizer (family P) w)).exists_le_sylow
  intro x hx
  exact sylow_le_sylowGenerated _ T (mem_map_of_mem _
    (hT (show (⟨x, hVR hx⟩ : stabilizer (family P) w) ∈
      (V (family P) v 1).subgroupOf (stabilizer (family P) w) from hx)))

/-- The two-residual of the source local actor moves the whole neighboring span. -/
theorem local_residual_not_centralizes_neighborhood (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (hS : ∀ i, ∃ T : Sylow 2 (P i), (T : Subgroup (P i)).map (P i).subtype ≤ B)
    {v w : Vertex (family P)} (hvw : (graph (family P)).Adj v w) :
    ¬ (pResidual 2 (graphLocalGroup (family P) v)).map
      (graphLocalGroup (family P) v).subtype ≤ centralizer (V (family P) v 1 : Set G) := by
  let := finite_endpoints h
  let H := graphLocalGroup (family P) v
  let R := stabilizer (family P) v
  let E := stabilizer (family P) v ⊓ stabilizer (family P) w
  have hHR : H ≤ R := sylowGenerated_le _
  let : Finite H := Finite.of_injective (inclusion hHR) (inclusion_injective _)
  let : Finite E := Finite.of_injective (inclusion (show E ≤ R from inf_le_left))
    (inclusion_injective _)
  intro hc
  have hres : (pResidual 2 H).map H.subtype ≤ E :=
    (le_inf ((map_subtype_le _).trans hHR) hc).trans
      ((neighborhood_centralizer_le_U h v).trans (ballKernel_one_le_edge (family P) hvw))
  obtain ⟨T, hT⟩ := source_edge_vertex_sylow h hS hvw
  let K := H.subgroupOf R
  have hTK : (T : Subgroup R) ≤ K := fun x hx =>
    sylow_le_sylowGenerated R T (mem_map_of_mem R.subtype hx)
  let e : K ≃* H := subgroupOfEquivOfLe hHR
  let TH : Sylow 2 H := (T.subtype hTK).mapSurjective (f := e.toMonoidHom) e.surjective
  have hm : (TH : Subgroup H).map H.subtype = (T : Subgroup R).map R.subtype := by
    change (((T : Subgroup R).subgroupOf K).map e.toMonoidHom).map H.subtype = _
    rw [map_map]
    have he : H.subtype.comp e.toMonoidHom = R.subtype.comp K.subtype := rfl
    rw [he, ← map_map, map_subgroupOf_eq_of_le hTK]
  have hgen := congrArg (map H.subtype) (pResidual_sup_sylow_eq_top TH)
  rw [Subgroup.map_sup, hm, ← MonoidHom.range_eq_map, range_subtype] at hgen
  have hHE : H ≤ E := hgen ▸ sup_le hres hT
  exact graphLocalGroup_not_closed h hB hS v
    (core_sylow_of_le E H hHE (source_edge_core_sylow h hB hvw))

/-- Any coordinates for the literal residual-centralizer section are nonzero. -/
theorem local_residual_section_nontrivial (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (hS : ∀ i, ∃ T : Sylow 2 (P i), (T : Subgroup (P i)).map (P i).subtype ≤ B)
    {v w : Vertex (family P)} (hvw : (graph (family P)).Adj v w)
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    (ρ : Representation (ZMod 2) (graphLocalGroup (family P) v) W)
    (c : BinaryConjugationSection (graphLocalGroup (family P) v) (V (family P) v 1)
      (V (family P) v 1 ⊓ centralizer ((pResidual 2 (graphLocalGroup (family P) v)).map
        (graphLocalGroup (family P) v).subtype : Set G)) ρ) : Nontrivial W := by
  apply not_subsingleton_iff_nontrivial.mp
  intro hs
  let := hs
  apply local_residual_not_centralizes_neighborhood h hB hS hvw
  rw [le_centralizer_iff]
  intro z hz
  exact ((c.coordinates_eq_one_iff ⟨z, hz⟩).mp (Subsingleton.elim _ _)).2

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingTrivial
