module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Flags.RankOne.Triple.Natural.GeometryBound.Displacement.Local
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Flags.RankOne.Triple.Natural.GeometryBound.Displacement.RankOne

/-!
# Transport and the reverse small-displacement contradiction

The rank-one fixed-index estimate transports under an actual automorphism of
the free amalgam, moving the quotient denominator together with the layer and
actor. Reverse radius escape supplies an actual conjugate edge layer at the
midpoint escaping Q_alpha.

For such a layer W, the edge index two identifies C_{Z_alpha}(W) with Z_beta.
Intersect the original radius with the transported parabolic to obtain E.
Normalization and the earlier radius commutator bound put [W cap Q_alpha,E]
in W cap Z_alpha, hence in Z_beta and therefore Z_middle. The transported
kernel centralizes W modulo Z_middle. If E joins that kernel with index
three, the rank-one estimate contradicts the excessive fixed index whenever
the reverse radius displacement is at most two.

`ReverseRadiusWitness` retains precisely the geometric selection still
required: an escaping transported edge and its index-three join. This module
proves the contradiction from that witness; it does not construct the join
from the forward inequalities. In particular it is not a completed proof of
the reverse step in (4.6.8).

Source: Meierfrankenfeld--Stellmacher, *Pushing up weak BN-pairs of rank two*
(1993), proof of (4.6.8), claim (1), printed p.905, the sentence beginning
“By a symmetric argument”.
-/

public section
open Subgroup Stellmacher.PushingUp.AmalgamGraph
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Flags.RankOne
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}

private theorem map_preimage_le {G : Type*} [Group G]
    (W T N : Subgroup G) (f : G →* G) (hWN : W ≤ normalizer N) :
    (commutatorPreimage W T N).map f ≤
      commutatorPreimage (W.map f) (T.map f) (N.map f) := by
  apply le_commutatorPreimage (map_mono (commutatorPreimage_le W T N))
  rw [← map_commutator]
  exact map_mono (commutator_commutatorPreimage_le W T N hWN)

private theorem map_preimage_eq {G : Type*} [Group G]
    (W T N : Subgroup G) (e : G ≃* G) (hWN : W ≤ normalizer N) :
    (commutatorPreimage W T N).map e.toMonoidHom =
      commutatorPreimage (W.map e.toMonoidHom) (T.map e.toMonoidHom)
        (N.map e.toMonoidHom) := by
  refine le_antisymm (map_preimage_le W T N e.toMonoidHom hWN) ?_
  have hn : W.map e.toMonoidHom ≤ normalizer (N.map e.toMonoidHom) :=
    (map_mono hWN).trans (le_normalizer_map e.toMonoidHom)
  have hb := map_preimage_le (W.map e.toMonoidHom) (T.map e.toMonoidHom)
    (N.map e.toMonoidHom) e.symm.toMonoidHom hn
  have he : e.symm.toMonoidHom.comp e.toMonoidHom = MonoidHom.id G :=
    MonoidHom.ext e.symm_apply_apply
  rw [map_map, map_map, map_map, he, map_id, map_id, map_id] at hb
  have hm := map_mono (f := e.toMonoidHom) hb
  have he' : e.toMonoidHom.comp e.symm.toMonoidHom = MonoidHom.id G :=
    MonoidHom.ext e.apply_symm_apply
  rwa [map_map, he', map_id] at hm

/-- The index-three fixed-space estimate transports to an arbitrary vertex.
The denominator is transported with the layer and actor. -/
theorem flagFixedPreimage_relIndex_le_four_of_conjugate_index_three
    (source : LocalSource L R) (geometry : Geometry R)
    (hlarge : 2 < geometry.b R) (i : Bool)
    (hkernel : flagKernel source i = Q R (beta R))
    (e : FreeAmalgam R ≃* FreeAmalgam R) (T : Subgroup (FreeAmalgam R))
    (hT : T ≤ (flagParabolic source i).map e.toMonoidHom)
    (hindex : T.relIndex ((flagParabolic source i).map e.toMonoidHom) = 3)
    (hfixed : (commutatorPreimage ((V R (beta R)).map e.toMonoidHom) T
      ((Z R (alpha R)).map e.toMonoidHom)).relIndex
        ((V R (beta R)).map e.toMonoidHom) ≤ 2) :
    (flagFixedPreimage source i).relIndex (V R (beta R)) ≤ 4 := by
  let T₀ := T.map e.symm.toMonoidHom
  have he : e.symm.toMonoidHom.comp e.toMonoidHom = MonoidHom.id (FreeAmalgam R) :=
    MonoidHom.ext e.symm_apply_apply
  have he' : e.toMonoidHom.comp e.symm.toMonoidHom = MonoidHom.id (FreeAmalgam R) :=
    MonoidHom.ext e.apply_symm_apply
  have hT₀ : T₀ ≤ flagParabolic source i := by
    have h := map_mono (f := e.symm.toMonoidHom) hT
    rwa [map_map, he, map_id] at h
  have hTmap : T₀.map e.toMonoidHom = T := by
    dsimp only [T₀]
    rw [map_map, he', map_id]
  have hi₀ : T₀.relIndex (flagParabolic source i) = 3 := by
    rw [← relIndex_map_map_of_injective T₀ (flagParabolic source i)
      (f := e.toMonoidHom) e.injective, hTmap]
    exact hindex
  have hWN : V R (beta R) ≤ normalizer (Z R (alpha R)) :=
    (edgeRadius_le_stabilizer geometry hlarge).trans (Z_normalized R _)
  have hm := map_preimage_eq (V R (beta R)) T₀ (Z R (alpha R)) e hWN
  rw [hTmap] at hm
  have hf₀ : (commutatorPreimage (V R (beta R)) T₀ (Z R (alpha R))).relIndex
      (V R (beta R)) ≤ 2 := by
    rwa [← hm, relIndex_map_map_of_injective _ _ e.injective] at hfixed
  apply flagFixedPreimage_relIndex_le_four_of_local_index_three source geometry hlarge i
    hkernel 1 T₀
  · simpa only [localFlagActor, localConjugate_one] using hT₀
  · simpa only [localFlagActor, localConjugate_one] using hi₀
  · simpa only [firstFlagLayer, localConjugate_one] using hf₀

/-- Concrete geometric data sufficient for the reverse displacement step.
The transporter changes the base vertex to the chosen midpoint. The original
radius intersected with the transported parabolic, joined with its kernel,
has index three in that parabolic. No fixed-index bound or displacement
conclusion is a field. Construction of this witness is a separate obligation. -/
structure ReverseRadiusWitness (source : LocalSource L R) (geometry : Geometry R)
    (i : Bool) (p : FlagCriticalData source geometry i) where
  transporter : FreeAmalgam R
  base_image : act R transporter (alpha R) = p.middle
  escapes : ¬ (V R (beta R)).map (MulAut.conj transporter⁻¹).toMonoidHom ≤ Q R (alpha R)
  join_index : ((V R (alpha R) ⊓
      (flagParabolic source i).map (MulAut.conj transporter⁻¹).toMonoidHom) ⊔
      (flagKernel source i).map (MulAut.conj transporter⁻¹).toMonoidHom).relIndex
    ((flagParabolic source i).map (MulAut.conj transporter⁻¹).toMonoidHom) = 3

omit [Finite M] in
/-- Reverse radius escape already supplies an actual transported edge layer
at the midpoint which escapes Q_alpha. The remaining witness field concerns
only the index-three join in its finite parabolic. -/
theorem FlagCriticalData.exists_reverse_escaping_edge
    {source : LocalSource L R} {geometry : Geometry R} {i : Bool}
    (p : FlagCriticalData source geometry i) (common : CommonFacts R source geometry)
    (hb : geometry.b R = 4) :
    ∃ g : FreeAmalgam R, act R g (alpha R) = p.middle ∧
      ¬ (V R (beta R)).map (MulAut.conj g⁻¹).toMonoidHom ≤ Q R (alpha R) := by
  have hmid : Z R p.middle ≤ Q R (alpha R) := by
    have hh := p.middle_le_firstLayer
    rw [firstFlagLayer, localConjugate_one] at hh
    exact hh.trans (edgeRadius_le_Q_alpha geometry common.large_distance)
  have hex : ∃ b, Adjacent R p.middle b ∧ ¬ V R b ≤ Q R (alpha R) := by
    classical
    by_contra! hn
    apply p.middle_radius_not_le_Q_alpha common hb
    apply iSup_le
    intro t
    apply iSup_le
    intro ht
    by_cases h0 : (cosetGraph R).dist t p.middle = 0
    · have he := (cosetGraph_connected R).dist_eq_zero_iff.mp h0
      simpa only [he] using hmid
    by_cases h1 : (cosetGraph R).dist t p.middle = 1
    · exact (Early.edge_Z_le p.middle t p.middle_color
        (adjacent_symm R ((cosetGraph_adj R _ _).mp
          (SimpleGraph.dist_eq_one_iff_adj.mp h1)))).trans hmid
    have h2 : (cosetGraph R).dist t p.middle = 2 := by omega
    have hed : (cosetGraph R).edist t p.middle = 2 := by
      rw [← ((cosetGraph_connected R) t p.middle).coe_dist_eq_edist, h2]
      rfl
    obtain ⟨b, htb, hmb⟩ := (SimpleGraph.edist_eq_two_iff.mp hed).2.2
    have hZV : Z R t ≤ V R b := le_iSup_of_le t (le_iSup_of_le
      (show (cosetGraph R).dist t b ≤ 2 by
        rw [SimpleGraph.dist_eq_one_iff_adj.mpr htb]
        decide) le_rfl)
    exact hZV.trans (hn b ((cosetGraph_adj R _ _).mp hmb))
  obtain ⟨b, hmb, hbQ⟩ := hex
  obtain ⟨g, hpair⟩ := (adjacent_iff_exists_common R p.middle b).mp hmb
  have hp : p.middle = mVertex R g ∧ b = hVertex R g := by
    rcases hpair with hh | hh
    · exact hh
    · have hc := p.middle_color
      rw [hh.1] at hc
      simp [color, hVertex] at hc
  have hga : act R g (alpha R) = p.middle := by
    rw [hp.1]
    simp only [alpha, act_mVertex, one_mul]
  refine ⟨g, hga, ?_⟩
  rw [← V_act]
  simpa only [hp.2, beta, act_hVertex, one_mul] using hbQ

private theorem alpha_centralizer_of_escape (source : LocalSource L R)
    (geometry : Geometry R) (common : CommonFacts R source geometry)
    (early : EarlyFacts R geometry) (W : Subgroup (FreeAmalgam R))
    (hWQ : W ≤ Q R (beta R)) (hnot : ¬ W ≤ Q R (alpha R)) :
    Z R (alpha R) ⊓ centralizer (W : Set (FreeAmalgam R)) = Z R (beta R) := by
  let C := Z R (alpha R) ⊓ centralizer (W : Set (FreeAmalgam R))
  have hBC : Z R (beta R) ≤ C := by
    rw [Early.edge_Z_eq_fixed common (alpha R) (beta R) rfl (base_adjacent R)]
    exact inf_le_inf_left _ (centralizer_le hWQ)
  let := finite_stabilizer R (alpha R)
  let : Finite (Z R (alpha R)) := Finite.of_injective (inclusion (Z_le_stabilizer R _))
    (inclusion_injective _)
  let : Finite C := Finite.of_injective (inclusion (show C ≤ Z R (alpha R) from inf_le_left))
    (inclusion_injective _)
  have hne : C.relIndex (Z R (alpha R)) ≠ 1 := by
    intro hc
    have hz : Z R (alpha R) ≤ centralizer (W : Set (FreeAmalgam R)) :=
      (relIndex_eq_one.mp hc).trans inf_le_right
    apply hnot
    rw [← common.centralizer (alpha R) (beta R) rfl (base_adjacent R)]
    exact le_inf hWQ (le_centralizer_iff.mp hz)
  have hi := early.edge_Z_index (alpha R) (beta R) rfl (base_adjacent R)
  have hm := relIndex_mul_relIndex (Z R (beta R)) C (Z R (alpha R)) hBC inf_le_left
  rw [hi] at hm
  have hcpos : 0 < C.relIndex (Z R (alpha R)) := Nat.pos_of_ne_zero index_ne_zero_of_finite
  have hbpos : 0 < (Z R (beta R)).relIndex C := Nat.pos_of_ne_zero index_ne_zero_of_finite
  have hc2 : 2 ≤ C.relIndex (Z R (alpha R)) := by omega
  have hc : (Z R (beta R)).relIndex C = 1 := by nlinarith
  exact le_antisymm (relIndex_eq_one.mp hc) hBC

/-- The reverse small-displacement calculation for an actual transported
edge layer. The centralizer at alpha changes the denominator from Z_alpha
to Z_middle through their common edge subgroup. -/
theorem ReverseRadiusWitness.two_lt_middle_radius_index
    {source : LocalSource L R} {geometry : Geometry R} {i : Bool}
    {p : FlagCriticalData source geometry i} (w : ReverseRadiusWitness source geometry i p)
    (common : CommonFacts R source geometry) (early : EarlyFacts R geometry)
    (hkernel : flagKernel source i = Q R (beta R))
    (hexcess : 4 < (flagFixedPreimage source i).relIndex (V R (beta R))) :
    2 < (Q R (alpha R)).relIndex (V R p.middle) := by
  let e := MulAut.conj w.transporter⁻¹
  let W := (V R (beta R)).map e.toMonoidHom
  let P := (flagParabolic source i).map e.toMonoidHom
  let K := (flagKernel source i).map e.toMonoidHom
  let E := V R (alpha R) ⊓ P
  let N := Z R p.middle
  let T := E ⊔ K
  have hN : (Z R (alpha R)).map e.toMonoidHom = N := by
    rw [← Z_act, w.base_image]
  have hWV : W ≤ V R p.middle := by
    have hh := map_mono (f := e.toMonoidHom)
      (edgeRadius_le_radius (alpha R) (beta R) rfl (base_adjacent R))
    rwa [← V_act R w.transporter (alpha R), w.base_image] at hh
  have hVQ : V R p.middle ≤ Q R (beta R) :=
    (V_le_Q geometry common.large_distance _ p.middle_color).trans
      (Q_le_adjacent_h R rfl (adjacent_symm R p.middle_neighbor))
  have hWQ := hWV.trans hVQ
  have hEV : E ≤ V R (alpha R) := inf_le_left
  have hmiddle : V R p.middle ≤ stabilizer R p.middle :=
    geometry.V_local _ p.middle_color (by
      rw [geometry.distance_constant _ p.middle_color]
      exact common.large_distance)
  have hPN : P ≤ normalizer N := by
    rw [← hN]
    exact (map_mono ((flagParabolic_le source i).trans (Z_normalized R _))).trans
      (le_normalizer_map e.toMonoidHom)
  have hPW : P ≤ normalizer W :=
    (map_mono (flagParabolic_normalizes_edgeRadius source geometry common.large_distance
      i hkernel)).trans (le_normalizer_map e.toMonoidHom)
  have hEP : E ≤ P := inf_le_right
  have hKP : K ≤ P := map_mono (flagKernel_le source i)
  have hTP : T ≤ P := sup_le hEP hKP
  have hWK : ⁅W,K⁆ ≤ N := by
    have hh := localFlagKernel_centralizes_bar source geometry common early i hkernel 1
    simp only [firstFlagLayer, localFlagKernel, localConjugate_one] at hh
    have hm := map_mono (f := e.toMonoidHom) hh
    rwa [map_commutator, hN] at hm
  let := edgeRadius_abelian geometry common.large_distance (alpha R) (beta R) rfl (base_adjacent R)
  let : IsMulCommutative W := inferInstanceAs
    (IsMulCommutative ((V R (beta R)).map e.toMonoidHom))
  have hD : ⁅W ⊓ Q R (alpha R), E⁆ ≤ N := by
    have hDW : ⁅W ⊓ Q R (alpha R), E⁆ ≤ W :=
      (commutator_mono inf_le_left le_rfl).trans
        (le_normalizer_iff_commutator_le_left.mp (hEP.trans hPW))
    have hDZ : ⁅W ⊓ Q R (alpha R), E⁆ ≤ Z R (alpha R) := by
      rw [commutator_comm]
      exact (commutator_mono hEV inf_le_right).trans (early.commutator_le_Z _ rfl)
    have hh := le_inf hDZ (hDW.trans (le_centralizer W))
    rw [alpha_centralizer_of_escape source geometry common early W hWQ w.escapes] at hh
    exact hh.trans (Early.edge_Z_le _ _ p.middle_color (adjacent_symm R p.middle_neighbor))
  have hfixed : W ⊓ Q R (alpha R) ≤ commutatorPreimage W T N := by
    have hTD : T ≤ commutatorPreimage T (W ⊓ Q R (alpha R)) N := by
      apply sup_le
      · exact le_commutatorPreimage le_sup_left (by rwa [commutator_comm])
      · apply le_commutatorPreimage le_sup_right
        rw [commutator_comm]
        exact (commutator_mono inf_le_left le_rfl).trans hWK
    apply le_commutatorPreimage inf_le_left
    rw [commutator_comm]
    exact (commutator_mono hTD le_rfl).trans
      (commutator_commutatorPreimage_le T (W ⊓ Q R (alpha R)) N (hTP.trans hPN))
  let := finite_stabilizer R p.middle
  let : Finite (V R p.middle) := Finite.of_injective
    (inclusion hmiddle) (inclusion_injective _)
  let : Finite W := Finite.of_injective (inclusion hWV) (inclusion_injective _)
  have hbound : (commutatorPreimage W T N).relIndex W ≤
      (Q R (alpha R)).relIndex (V R p.middle) := by
    have hh := relIndex_le_of_le_left hfixed
      (show (W ⊓ Q R (alpha R)).relIndex W ≠ 0 from index_ne_zero_of_finite)
    rw [inf_relIndex_left] at hh
    exact hh.trans (relIndex_le_of_le_right hWV index_ne_zero_of_finite)
  by_contra! hsmall
  have hf : (commutatorPreimage ((V R (beta R)).map e.toMonoidHom) T
      ((Z R (alpha R)).map e.toMonoidHom)).relIndex
        ((V R (beta R)).map e.toMonoidHom) ≤ 2 := by
    rw [hN]
    exact hbound.trans hsmall
  exact (not_lt_of_ge (flagFixedPreimage_relIndex_le_four_of_conjugate_index_three
    source geometry common.large_distance i hkernel e T hTP w.join_index hf)) hexcess

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Flags.RankOne
