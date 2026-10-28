module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.NoncommutingProfile.BTwoSeedIntersections
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.NoncommutingProfile.BTwoSeedField
public import Theory.GroupTheory.SylowLocalCore
public import Mathlib.GroupTheory.SpecificGroups.Dihedral
public import Theory.GroupTheory.AmalgamGraph.LinearPathKernel

/-!
# The seed in the order-ten dihedral beta branch

A nontrivial subgroup of a Sylow subgroup of D₁₀ fills that Sylow, which
has order two. The earlier core-intersection obstruction makes the actual
seed image nontrivial. Lifting this image and intersecting with Q_alpha
therefore saturates the seed. The two conjugate core factors then have
index two over D_alpha. The defining-field bound forces q_alpha = 2,
and Q_alpha/D_alpha is elementary of order four.

These are necessary consequences of the dihedral branch, not its exclusion.
The original endpoint application retains the exceptional Sz(2) enlargement
until the already proved Suzuki obstruction excludes it.
Source: DGS, Groups and Graphs (1985), proof of (10.7), pp.158--159.
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

private theorem dihedral_edge_image
    (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (hS : ∀ i, ∃ T : Sylow 2 (P i), (T : Subgroup (P i)).map (P i).subtype ≤ B)
    {a b : Vertex F} (hab : (graph F).Adj a b)
    (e : (graphLocalGroup F a ⧸ pCore 2 (graphLocalGroup F a)) ≃* DihedralGroup 5)
    (J : Subgroup G)
    (hJS : J ≤ (stabilizer F a ⊓ stabilizer F b).pCoreIn 2)
    (heJ : ¬ J ≤ Q F a) :
    (stabilizer F a ⊓ stabilizer F b).pCoreIn 2 = J ⊔ Q F a ∧
      (Q F a).relIndex J = 2 := by
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
  let T := R.mapSurjective hq
  have hTcard : Nat.card T = 2 := by
    rw [T.card_eq_multiplicity,DihedralGroup.nat_card]
    rw [Nat.factorization_mul (by decide) (by decide),
      Nat.prime_two.factorization, Nat.prime_five.factorization]
    norm_num
  have hmap : J₀.map q ≤ (T : Subgroup (DihedralGroup 5)) := map_mono hJR
  have hne : J₀.map q ≠ ⊥ := by
    intro hh
    exact he ((Subgroup.map_eq_bot_iff _).mp hh)
  have hi : J₀.map q = (R : Subgroup L).map q := by
    apply eq_of_le_of_card_ge hmap
    have hgt : 1 < Nat.card (J₀.map q) := (one_lt_card_iff_ne_bot _).mpr hne
    change Nat.card T ≤ _
    omega
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
    exact hh.trans hTcard

/-- The actual dihedral beta quotient saturates the seed and computes the
index of the beta core in the alpha core. No span or index is assumed. -/
theorem BTwoCenterActionData.dihedral_seed_eq_core_and_index
    (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (hS : ∀ i, ∃ T : Sylow 2 (P i), (T : Subgroup (P i)).map (P i).subtype ≤ B)
    (hSyl : ∀ x, Stellmacher.IsSylowSubgroupIn (Q F x) (U F x))
    (hb : b F = 2) {v m w t : Vertex F}
    (c : BTwoCenterActionData F v m w k W)
    (ht : (graph F).Adj v t) (hne : t ≠ m)
    (hnot : ¬ stabilizer F v ≤ normalizer ((Q F m ⊓ Q F v : Subgroup G) : Set G))
    (e : (graphLocalGroup F m ⧸ pCore 2 (graphLocalGroup F m)) ≃* DihedralGroup 5) :
    centralSeed F v m t = Q F v ∧ (Q F m).relIndex (Q F v) = 2 := by
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
  obtain ⟨hgen,hi⟩ := dihedral_edge_image h hB hS c.middle.symm e J
    (hJQ.trans (by simpa only [inf_comm] using graph_Q_le_edgeCore h c.middle))
    heJ
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



/-- The literal adjacent-core factor has order two. -/
theorem BTwoCenterActionData.dihedral_seed_factor_index
    (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (hS : ∀ i, ∃ T : Sylow 2 (P i), (T : Subgroup (P i)).map (P i).subtype ≤ B)
    (hSyl : ∀ x, Stellmacher.IsSylowSubgroupIn (Q F x) (U F x))
    (hb : b F = 2) {v m w t : Vertex F}
    (c : BTwoCenterActionData F v m w k W)
    (ht : (graph F).Adj v t) (hne : t ≠ m)
    (hnot : ¬ stabilizer F v ≤ normalizer ((Q F m ⊓ Q F v : Subgroup G) : Set G))
    (e : (graphLocalGroup F m ⧸ pCore 2 (graphLocalGroup F m)) ≃* DihedralGroup 5) :
    (D F m t).relIndex (Q F v ⊓ Q F m) = 2 := by
  have hs := c.dihedral_seed_eq_core_and_index h hB hS hSyl hb ht hne hnot e
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
    _ = 2 := hm.trans hs.2


/-- The dihedral row forces the alpha field to have order two and the
actual elementary core quotient to have order four. -/
theorem BTwoCenterActionData.dihedral_central_core_structure
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
    (e : (graphLocalGroup F m ⧸ pCore 2 (graphLocalGroup F m)) ≃* DihedralGroup 5) :
    Nat.card k = 2 ∧
      ∃ hN : ((D F m t).subgroupOf (Q F v)).Normal,
        letI := hN
        IsElementaryAbelian 2 (Q F v ⧸ (D F m t).subgroupOf (Q F v)) ∧
        Nat.card (Q F v ⧸ (D F m t).subgroupOf (Q F v)) = 4 := by
  have hSyl := source_kernel_sylow h hB hS
  have hs := (c.dihedral_seed_eq_core_and_index h hB hS hSyl hb ht hne hnot e).1
  have hi : (D F m t).relIndex (V F m 1 ⊓ Q F v) = 2 :=
    (c.seed_factor_index_eq h hSyl hb ht hne).symm.trans
      (c.dihedral_seed_factor_index h hB hS hSyl hb ht hne hnot e)
  have hbound := c.central_seed_field_bound h hB hS hb hactor hcentral ht hne hcomm hnot
  rw [hi] at hbound
  obtain ⟨hN,hE⟩ := c.central_seed_elementary h hB hS hb hactor hcentral ht hne hcomm
  obtain ⟨_,hcard⟩ := c.central_seed_card_square h hB hS hb hactor hcentral ht hne hcomm
  rw [hi] at hcard
  have hh : ∃ hN : ((D F m t).subgroupOf (centralSeed F v m t)).Normal,
      letI := hN
      IsElementaryAbelian 2 (centralSeed F v m t ⧸ (D F m t).subgroupOf (centralSeed F v m t)) ∧
      Nat.card (centralSeed F v m t ⧸ (D F m t).subgroupOf (centralSeed F v m t)) = 4 :=
    ⟨hN,hE,hcard⟩
  rw [hs] at hh
  have hk : 1 < Nat.card k := by
    let := Fintype.ofFinite k
    rw [Nat.card_eq_fintype_card]
    exact Fintype.one_lt_card
  exact ⟨by omega,hh⟩

end CFSG.Quasithin.ChapterF.Source.DGS85.NoncommutingProfile
