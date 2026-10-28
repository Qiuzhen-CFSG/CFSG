module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.NoncommutingProfile.BTwoSeedIntersections
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.NoncommutingProfile.BTwoSeedField
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.LocalStructure.LinearMarking
public import Theory.SpecificGroups.SL2.SylowCharacteristicImage
public import Theory.SpecificGroups.SL2.SylowConsequences
public import Theory.GroupTheory.AmalgamGraph.LinearPathKernel

/-!
# Saturation and the beta field in the linear branch of (10.7)

The already constructed seed contains both adjacent-core intersections and
is normal in the alpha stabilizer. The earlier (6.5) obstruction therefore
forces it to escape the beta core. In an actual binary SL₂ beta quotient,
normalizer invariance makes its image the whole edge Sylow. Intersecting
that supplement with the alpha core proves seed saturation.

The same Sylow image and the conjugacy of the two factors identify their
index with the beta field order. Applying the elementary seed and square
calculations gives the source quotient of order q_beta squared, with
q_alpha at most q_beta. The fields are kept separate. Selection of the
linear beta model in the general source argument remains an obligation;
here its actual quotient equivalence is an explicit branch input.

Source: Delgado--Goldschmidt--Stellmacher, Groups and Graphs (1985),
(10.7), printed pp.158--159, and the linear rank-one facts (5.1).
-/

public noncomputable section
open Subgroup
open scoped Pointwise commutatorElement MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.DGS85.NoncommutingProfile
open Subgroup.CosetGeometry.RankTwo Theory.GroupTheory.AmalgamGraph Noncommuting
variable {G : Type*} [Group G] {P : Fin 2 → Subgroup G} {B : Subgroup G}
local notation "F" => family P
variable {k W : Type*} [Field k] [Finite k] [CharP k 2]
  [AddCommGroup W] [Module (ZMod 2) W]
variable {K : Type*} [Field K] [Finite K] [CharP K 2]

private theorem linear_edge_image
    (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (hS : ∀ i, ∃ T : Sylow 2 (P i), (T : Subgroup (P i)).map (P i).subtype ≤ B)
    {a b : Vertex F} (hab : (graph F).Adj a b)
    (e : (graphLocalGroup F a ⧸ pCore 2 (graphLocalGroup F a)) ≃* SL(2,K))
    (J : Subgroup G)
    (hJS : J ≤ (stabilizer F a ⊓ stabilizer F b).pCoreIn 2)
    (hnJ : stabilizer F a ⊓ stabilizer F b ≤ normalizer (J : Set G))
    (heJ : ¬ J ≤ Q F a) :
    (stabilizer F a ⊓ stabilizer F b).pCoreIn 2 = J ⊔ Q F a ∧
      (Q F a).relIndex J = Nat.card K := by
  let := finite_endpoints h
  let L := graphLocalGroup F a
  let E := stabilizer F a ⊓ stabilizer F b
  let : Finite L := Finite.of_injective (inclusion (sylowGenerated_le _)) (inclusion_injective _)
  obtain ⟨T,hT⟩ := source_edge_vertex_sylow h hS hab
  have hES := sylow_image_eq_edge_core (stabilizer F a) E inf_le_left
    (source_edge_core_sylow h hB hab) T hT
  obtain ⟨R,hR⟩ := T.exists_map_subtype_eq_of_le (H := L) (sylowGenerated_le _)
    (sylow_le_sylowGenerated _ T)
  have hRS : (R : Subgroup L).map L.subtype = E.pCoreIn 2 := hR.trans hES
  have hSL : E.pCoreIn 2 ≤ L := hRS ▸ map_subtype_le _
  have hJL : J ≤ L := hJS.trans hSL
  have hQL : Q F a ≤ L := (graph_Q_le_edgeCore h hab).trans hSL
  have hRs : (R : Subgroup L) = (E.pCoreIn 2).subgroupOf L := by
    apply map_injective L.subtype_injective
    rw [hRS,map_subgroupOf_eq_of_le hSL]
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))
  have hq : Function.Surjective q := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hc : L.pCoreIn 2 = Q F a := sylowGenerated_core _
  have hk : q.ker = (Q F a).subgroupOf L := by
    rw [←hc]
    change q.ker = ((pCore 2 L).map L.subtype).comap L.subtype
    rw [comap_map_eq_self_of_injective L.subtype_injective]
    ext x
    change e (QuotientGroup.mk' (pCore 2 L) x) = 1 ↔ x ∈ pCore 2 L
    rw [e.map_eq_one_iff]
    exact QuotientGroup.eq_one_iff x
  let J₀ := J.subgroupOf L
  have hJR : J₀ ≤ (R : Subgroup L) := by rw [hRs]; exact comap_mono hJS
  have he : ¬ J₀ ≤ q.ker := by
    rw [hk]
    intro hh
    apply heJ
    have hm := map_mono (f := L.subtype) hh
    rwa [map_subgroupOf_eq_of_le hJL,map_subgroupOf_eq_of_le hQL] at hm
  have hn : normalizer (R : Set L) ≤ normalizer (J₀ : Set L) := by
    have hN : normalizer (R : Set L) = (normalizer (E.pCoreIn 2 : Set G)).subgroupOf L := by
      rw [←R.coe_coe,hRs]
      exact (subgroupOf_normalizer_eq hSL).symm
    rw [hN]
    intro x hx
    have hxE : (x : G) ∈ E := by
      change (x : G) ∈ stabilizer F a ⊓ stabilizer F b
      rw [←source_edge_core_normalizer h hB hab]
      exact ⟨sylowGenerated_le _ x.property,hx⟩
    exact le_normalizer_comap L.subtype (hnJ hxE)
  have hi := Matrix.SpecialLinearGroup.normalizer_invariant_image_eq_sylow R q hq J₀ hJR he hn
  constructor
  · have hh := congrArg (Subgroup.comap q) hi
    rw [comap_map_eq,comap_map_eq,sup_eq_left.mpr (show q.ker ≤ (R : Subgroup L) from by
      rw [hk,hRs]; exact comap_mono (graph_Q_le_edgeCore h hab))] at hh
    have hm := congrArg (Subgroup.map L.subtype) hh
    rw [Subgroup.map_sup,hk,map_subgroupOf_eq_of_le hJL,
      map_subgroupOf_eq_of_le hQL,hRS] at hm
    exact hm.symm
  · have hh := relIndex_ker (K := J₀) q
    rw [hk,relIndex_subgroupOf hJL,hi] at hh
    exact hh.trans (Nat.card_congr
      (Matrix.SpecialLinearGroup.sylowEquivAdditive K 2 (R.mapSurjective hq)).symm.toEquiv)

/-- The actual linear beta quotient saturates the seed and computes the
index of the beta core in the alpha core. No span or index is assumed. -/
theorem BTwoCenterActionData.linear_seed_eq_core_and_index
    (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (hS : ∀ i, ∃ T : Sylow 2 (P i), (T : Subgroup (P i)).map (P i).subtype ≤ B)
    (hSyl : ∀ x, Stellmacher.IsSylowSubgroupIn (Q F x) (U F x))
    (hb : b F = 2) {v m w t : Vertex F}
    (c : BTwoCenterActionData F v m w k W)
    (ht : (graph F).Adj v t) (hne : t ≠ m)
    (hnot : ¬ stabilizer F v ≤ normalizer ((Q F m ⊓ Q F v : Subgroup G) : Set G))
    (e : (graphLocalGroup F m ⧸ pCore 2 (graphLocalGroup F m)) ≃* SL(2,K)) :
    centralSeed F v m t = Q F v ∧ (Q F m).relIndex (Q F v) = Nat.card K := by
  let J := centralSeed F v m t
  have hIJ := c.seed_eq_core_intersections h hSyl hb ht hne
  have hJQ : J ≤ Q F v := by rw [show J = centralSeed F v m t from rfl,hIJ]; exact sup_le inf_le_left inf_le_left
  have hNJ : Q F v ⊓ Q F m ≤ J := by
    change _ ≤ centralSeed F v m t
    rw [hIJ]
    exact le_sup_left
  have hnJ := c.seed_stabilizer_normalized h hSyl hb ht hne
  have heJ : ¬ J ≤ Q F m := by
    intro hh
    have he : J = Q F v ⊓ Q F m := le_antisymm (le_inf hJQ hh) hNJ
    apply hnot
    change stabilizer F v ≤ normalizer (J : Set G) at hnJ
    simpa only [he,inf_comm] using hnJ
  obtain ⟨hgen,hi⟩ := linear_edge_image h hB hS c.middle.symm e J
    (hJQ.trans (by simpa only [inf_comm] using graph_Q_le_edgeCore h c.middle))
    (inf_le_right.trans hnJ) heJ
  have hcover : Q F v ≤ J ⊔ Q F m := by
    rw [←hgen]
    simpa only [inf_comm] using graph_Q_le_edgeCore h c.middle
  have hn : Q F m ≤ normalizer (J : Set G) :=
    ((source_Z_Q_U h m).2.trans ((ballKernel_one_le_edge F c.middle.symm).trans inf_le_right)).trans hnJ
  have hsat : J = Q F v := by
    apply le_antisymm hJQ
    intro x hx
    have hxprod : x ∈ (J : Set G) * (Q F m : Set G) := by
      rw [←coe_mul_of_right_le_normalizer_left _ _ hn]
      exact hcover hx
    obtain ⟨j,hj,y,hy,rfl⟩ := hxprod
    have hyQ : y ∈ Q F v := by
      simpa only [inv_mul_cancel_left] using (Q F v).mul_mem ((Q F v).inv_mem (hJQ hj)) hx
    exact J.mul_mem hj (hNJ ⟨hyQ,hy⟩)
  exact ⟨hsat,hsat ▸ hi⟩



/-- The literal adjacent-core factor has the beta field order. -/
theorem BTwoCenterActionData.linear_seed_factor_index
    (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (hS : ∀ i, ∃ T : Sylow 2 (P i), (T : Subgroup (P i)).map (P i).subtype ≤ B)
    (hSyl : ∀ x, Stellmacher.IsSylowSubgroupIn (Q F x) (U F x))
    (hb : b F = 2) {v m w t : Vertex F}
    (c : BTwoCenterActionData F v m w k W)
    (ht : (graph F).Adj v t) (hne : t ≠ m)
    (hnot : ¬ stabilizer F v ≤ normalizer ((Q F m ⊓ Q F v : Subgroup G) : Set G))
    (e : (graphLocalGroup F m ⧸ pCore 2 (graphLocalGroup F m)) ≃* SL(2,K)) :
    (D F m t).relIndex (Q F v ⊓ Q F m) = Nat.card K := by
  have hs := c.linear_seed_eq_core_and_index h hB hS hSyl hb ht hne hnot e
  obtain ⟨g,hg,hop⟩ := c.exists_opposite_lift h ht hne
  obtain ⟨d,_,_⟩ := c.exists_oppositeGeometry h hSyl hb g hg hop
  let N := Q F v ⊓ Q F m
  let T := Q F v ⊓ Q F t
  have hgen : N ⊔ T = Q F v := (c.seed_eq_core_intersections h hSyl hb ht hne).symm.trans hs.1
  have hnT : Q F v ≤ normalizer (T : Set G) :=
    (le_inf (Q F v).le_normalizer
      (((source_Z_Q_U h v).2.trans ((ballKernel_one_le_edge F ht).trans inf_le_right)).trans
        (CommutingNontrivial.stabilizer_normalizes_Q F t))).trans inf_normalizer_le_normalizer_inf
  let : (T.subgroupOf (Q F v)).Normal :=
    (normal_subgroupOf_iff_le_normalizer (show T ≤ Q F v from inf_le_left)).mpr hnT
  have hi := relIndex_sup_right (N.subgroupOf (Q F v)) (T.subgroupOf (Q F v))
  rw [←subgroupOf_sup (show N ≤ Q F v from inf_le_left) (show T ≤ Q F v from inf_le_left),
    relIndex_subgroupOf (show N ⊔ T ≤ Q F v from hgen.le),
    relIndex_subgroupOf (show N ≤ Q F v from inf_le_left),hgen] at hi
  have hD : D F m t = N ⊓ T := by
    apply le_antisymm
    · exact le_inf (le_inf d.separated inf_le_left) (le_inf d.separated inf_le_right)
    · exact le_inf (inf_le_left.trans inf_le_right) (inf_le_right.trans inf_le_right)
  have hm := relIndex_map_map_of_injective (f := (MulAut.conj (g : G)).toMonoidHom)
    (Q F m) (Q F v) (MulAut.conj (g : G)).injective
  have hgv : (g : G) • v = v := c.actor_le g.property
  rw [←Q_translate,←Q_translate,hg,hgv] at hm
  calc
    (D F m t).relIndex N = T.relIndex N := by rw [hD,inf_relIndex_left]
    _ = T.relIndex (Q F v) := hi.symm
    _ = (Q F t).relIndex (Q F v) := inf_relIndex_left _ _
    _ = Nat.card K := hm.trans hs.2


/-- The elementary quotient and its exact beta-field order in (10.7).
The alpha field supplies a lower bound, not an equality of fields. -/
theorem BTwoCenterActionData.linear_central_core_structure
    (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (hS : ∀ i, ∃ T : Sylow 2 (P i), (T : Subgroup (P i)).map (P i).subtype ≤ B)
    (hb : b F = 2) {v m w t : Vertex F}
    (c : BTwoCenterActionData F v m w k W)
    (hactor : c.actor = graphLocalGroup F v)
    (hcentral : Z F m ≤ centerIn (graphLocalGroup F m))
    (ht : (graph F).Adj v t) (hne : t ≠ m)
    (hcomm : ⁅V F m 1,Q F m⁆ ≤ Z F m)
    (hnot : ¬ stabilizer F v ≤ normalizer ((Q F m ⊓ Q F v : Subgroup G) : Set G))
    (e : (graphLocalGroup F m ⧸ pCore 2 (graphLocalGroup F m)) ≃* SL(2,K)) :
    Nat.card k ≤ Nat.card K ∧
      ∃ hN : ((D F m t).subgroupOf (Q F v)).Normal,
        letI := hN
        IsElementaryAbelian 2 (Q F v ⧸ (D F m t).subgroupOf (Q F v)) ∧
        Nat.card (Q F v ⧸ (D F m t).subgroupOf (Q F v)) = Nat.card K ^ 2 := by
  have hSyl := source_kernel_sylow h hB hS
  have hs := (c.linear_seed_eq_core_and_index h hB hS hSyl hb ht hne hnot e).1
  have hi : (D F m t).relIndex (V F m 1 ⊓ Q F v) = Nat.card K :=
    (c.seed_factor_index_eq h hSyl hb ht hne).symm.trans
      (c.linear_seed_factor_index h hB hS hSyl hb ht hne hnot e)
  have hbound := c.central_seed_field_bound h hB hS hb hactor hcentral ht hne hcomm hnot
  rw [hi] at hbound
  obtain ⟨hN,hE⟩ := c.central_seed_elementary h hB hS hb hactor hcentral ht hne hcomm
  obtain ⟨_,hcard⟩ := c.central_seed_card_square h hB hS hb hactor hcentral ht hne hcomm
  rw [hi] at hcard
  have hh : ∃ hN : ((D F m t).subgroupOf (centralSeed F v m t)).Normal,
      letI := hN
      IsElementaryAbelian 2 (centralSeed F v m t ⧸ (D F m t).subgroupOf (centralSeed F v m t)) ∧
      Nat.card (centralSeed F v m t ⧸ (D F m t).subgroupOf (centralSeed F v m t)) = Nat.card K ^ 2 :=
    ⟨hN,hE,hcard⟩
  rw [hs] at hh
  exact ⟨hbound,hh⟩

end CFSG.Quasithin.ChapterF.Source.DGS85.NoncommutingProfile
