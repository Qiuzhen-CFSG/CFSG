module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.PairingControl.Geometry.Selection.Basic
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.PairingControl.FirstPairing.StepThree.Consequences

/-!
# The backward choices in MS93 (4.3.2)(6)

The conjugates of any incident displacement span the natural group by
irreducibility. Since that group escapes the critical endpoint kernel, an
actual incident edge escapes it as well. Local transitivity moves a moving
neighbor onto that edge. The intersection of all incident displacements is
zero, so every nontrivial subgroup escapes one of them.

Source: Meierfrankenfeld--Stellmacher (1993), (4.3.2)(6), printed p.885.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.PairingControl.Geometry.LocalProducts.StepSix
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M} {geometry : MS93.Geometry R}

theorem exists_moving_at_edge (hb : 2 < geometry.b R)
    (transfer : NormalizationTransfer R) (p : Counterexample geometry)
    (bad : ¬ ⁅V R p.a, Q R p.a⁆ ≤ fixedCore R p.a)
    {a t : Vertex R} (ha : color R a = false) (hat : Adjacent R a t) :
    ∃ d, Adjacent R d t ∧ d ∈ movingNeighbors geometry a := by
  obtain ⟨q, hqa, hbad⟩ := FirstPairing.contrary_at p bad a ha
  obtain ⟨d, hd⟩ := FirstPairing.StepThree.exists_moving_neighbor hb transfer q hbad
  rw [hqa] at hd
  obtain ⟨s, has, hds⟩ := exists_common_neighbor_of_dist_two R a d hd.1
  obtain ⟨g, hg, hgs⟩ := stabilizer_transitive_neighbors R a has hat
  have hga : act R g a = a := hg
  refine ⟨act R g d, ?_, ?_⟩
  · rw [← hgs]
    exact (adjacent_act_iff R g d s).mpr hds
  · have h := (FirstPairing.movingNeighbors_act_iff hb g a d ha).mpr hd
    rwa [hga] at h

theorem edge_conjugates_eq_natural (source : LocalSource L R)
    (modules : ModuleFacts source geometry) (facts : ContraryLocalFacts geometry)
    {a t : Vertex R} (ha : color R a = false) (hat : Adjacent R a t) :
    NormalizerTransfer.conjugatesIn (edgeDisplacement a t) (stabilizer R a) = U R a := by
  obtain ⟨o⟩ := facts.opposite a ha
  let K := NormalizerTransfer.conjugatesIn (edgeDisplacement a t) (stabilizer R a)
  have hKU : K ≤ U R a := by
    apply iSup_le
    intro g
    exact (map_mono (Initial.edge_le_natural source a t ha hat)).trans
      (mem_normalizer_iff_map_conj_eq.mp
        (U_normalized a ((stabilizer R a).inv_mem g.property))).le
  have hUG := (U_le_Z a).trans (Z_le_stabilizer R a)
  have hKG := hKU.trans hUG
  have hn := NormalizerTransfer.conjugatesIn_normalized (edgeDisplacement a t) (stabilizer R a)
  let : (K.subgroupOf (stabilizer R a)).Normal := normal_subgroupOf_of_le_normalizer hn
  have him : (⊤ : Subgroup (stabilizer R a)).map o.projection = ⊤ := by
    rw [← MonoidHom.range_eq_map]
    exact MonoidHom.range_eq_top.mpr o.surjective
  rcases o.naturalU.irreducible him (K.subgroupOf (stabilizer R a))
    (fun _ hx => hKU hx) le_normalizer_of_normal with h | h
  · have hbot : K = ⊥ := by
      have hh := congrArg (Subgroup.map (stabilizer R a).subtype) h
      simpa only [map_subgroupOf_eq_of_le hKG, Subgroup.map_bot] using hh
    have hle : edgeDisplacement a t ≤ K := by
      have hh := le_iSup (fun g : stabilizer R a =>
        NormalizerTransfer.rightConjugate (edgeDisplacement a t) g) 1
      intro x hx
      exact hh ⟨x, hx, by simp⟩
    exact (EdgeTransfer.edge_commutator_ne_bot modules a t ha hat
      (le_bot_iff.mp (hbot ▸ hle))).elim
  · have hh := congrArg (Subgroup.map (stabilizer R a).subtype) h
    simpa only [map_subgroupOf_eq_of_le hKG, map_subgroupOf_eq_of_le hUG] using hh

theorem natural_not_le_endpoint_kernel (source : LocalSource L R)
    (modules : ModuleFacts source geometry) (p : Counterexample geometry) :
    ¬ U R p.a ≤ Q R p.a' := by
  intro h
  apply (source.critical_reverse geometry p.a p.color_a p.a' p.end_color p.critical).2
  rw [← modules.natural.centralizer p.a p.color_a]
  exact le_inf p.end_Z_le_start_stabilizer
    ((commutator_eq_bot_iff_le_centralizer.mp (geometry.centralizes p.a' p.end_color)).trans
      (centralizer_le h))

/-- This constructs both actual backward vertices and the escaping displacement. -/
theorem backwardChoice_nonempty (source : LocalSource L R)
    (hb : 2 < geometry.b R) (modules : ModuleFacts source geometry)
    (transfer : NormalizationTransfer R) (facts : ContraryLocalFacts geometry)
    (p : Counterexample geometry) (bad : ¬ ⁅V R p.a, Q R p.a⁆ ≤ fixedCore R p.a) :
    Nonempty (BackwardChoice p) := by
  classical
  obtain ⟨d, hd⟩ := FirstPairing.StepThree.exists_moving_neighbor hb transfer p bad
  obtain ⟨t, hat, hdt⟩ := exists_common_neighbor_of_dist_two R p.a d hd.1
  have hnot : ¬ NormalizerTransfer.conjugatesIn (edgeDisplacement p.a t)
      (stabilizer R p.a) ≤ Q R p.a' := by
    rw [edge_conjugates_eq_natural source modules facts p.color_a hat]
    exact natural_not_le_endpoint_kernel source modules p
  obtain ⟨g, hg⟩ : ∃ g : stabilizer R p.a,
      ¬ NormalizerTransfer.rightConjugate (edgeDisplacement p.a t) g ≤ Q R p.a' := by
    simpa only [NormalizerTransfer.conjugatesIn, iSup_le_iff, not_forall] using hnot
  have hga : act R (g : FreeAmalgam R) p.a = p.a := g.property
  refine ⟨{
    edge := act R (g : FreeAmalgam R) t
    back := act R (g : FreeAmalgam R) d
    adjacent_start := ?_
    adjacent_back := (adjacent_act_iff R _ d t).mpr hdt
    moving := ?_
    escapes := ?_ }⟩
  · simpa only [hga] using (adjacent_act_iff R (g : FreeAmalgam R) p.a t).mpr hat
  · have h := (FirstPairing.movingNeighbors_act_iff hb (g : FreeAmalgam R)
      p.a d p.color_a).mpr hd
    rwa [hga] at h
  · have he := FirstPairing.edgeDisplacement_act (g : FreeAmalgam R) p.a t
    rw [hga] at he
    rwa [he]

/-- A nonzero subgroup cannot lie in every incident edge displacement. -/
theorem exists_avoiding_edge (source : LocalSource L R)
    (hb : 2 < geometry.b R) (modules : ModuleFacts source geometry)
    (facts : ContraryLocalFacts geometry) {a : Vertex R} (ha : color R a = false)
    (K : Subgroup (FreeAmalgam R)) (hne : K ≠ ⊥) :
    ∃ t, Adjacent R a t ∧ ¬ K ≤ edgeDisplacement a t := by
  classical
  let J : Subgroup (FreeAmalgam R) := ⨅ t, ⨅ (_ : Adjacent R a t), edgeDisplacement a t
  have hJ : ∀ t, Adjacent R a t → J ≤ edgeDisplacement a t :=
    fun t ht => (iInf_le _ t).trans (iInf_le _ ht)
  have hn : stabilizer R a ≤ normalizer (J : Set (FreeAmalgam R)) := by
    apply le_normalizer_iff.mpr
    intro g hg x hx
    apply mem_iInf.mpr
    intro t
    apply mem_iInf.mpr
    intro ht
    have hga : act R g a = a := hg
    have hgai : act R g⁻¹ a = a := (stabilizer R a).inv_mem hg
    have hgt : Adjacent R a (act R g t) := by
      rw [← hga]
      exact (adjacent_act_iff R g a t).mpr ht
    have hx' := mem_map_of_mem (MulAut.conj g).toMonoidHom (hJ _ hgt hx)
    have he := FirstPairing.edgeDisplacement_act g⁻¹ a (act R g t)
    simp only [hgai, ← act_mul, mul_inv_cancel, act_one, inv_inv] at he
    rwa [← he] at hx'
  obtain ⟨g, rfl⟩ := exists_mVertex_of_color R ha
  have hadj : Adjacent R (mVertex R g) (hVertex R g) := by
    simpa only [act_mVertex, act_hVertex, one_mul] using
      (adjacent_act_iff R g (mVertex R 1) (hVertex R 1)).mpr (base_adjacent R)
  have hzero := Selection.edge_normal_subgroup_eq_bot source hb modules facts
    (show color R (mVertex R g) = false from rfl) hadj J (hJ _ hadj) hn
  by_contra! h
  apply hne
  apply le_bot_iff.mp
  rw [← hzero]
  exact le_iInf fun t => le_iInf fun ht => h t ht

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.PairingControl.Geometry.LocalProducts.StepSix
