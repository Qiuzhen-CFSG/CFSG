module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.RegularPaths.OrbitEscape.CommutatorContradiction.LocalImage
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.LocalCommutator.Basic
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.Initial.RadiusGrowth
public import Theory.GroupTheory.CommutatorPreimage

/-!
# The reverse-span obstruction in the R₁ calculation

The reverse orbit span cannot have its Zδ-commutator inside Z_(a+2).
Otherwise all local conjugates of Zδ normalize the neighboring product
Z_a Z_(a+2). Together with the local kernel these conjugates generate the
whole stabilizer, contradicting the proved reverse nonnormality theorem.

Joint normality then transfers this noncontainment to the literal R₁,
once the preceding source bound [V,Zδ] ≤ Z_(a+2) has been proved. The
same bound gives R₁ ≠ 1 and R₁ not contained in Dδ, using its already
proved containment in the disjoint natural summand Uδ. The forward bound
is an explicit remaining premise, not a claimed consequence here.

Source: Meierfrankenfeld--Stellmacher, Pushing up weak BN-pairs of rank two
(1993), (2.2)(v) and (4.4.2), printed pp.856 and 893.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.RegularPaths.OrbitEscape.CommutatorContradiction
open NormalizerTransfer

private theorem conjugates_normalize_of_commutator_le {G : Type*} [Group G]
    (A F W Z K : Subgroup G)
    (hFW : F ≤ normalizer (W : Set G)) (hFZ : F ≤ normalizer (Z : Set G))
    (hZK : Z ≤ K) (hKW : K ≤ W) (hcomm : ⁅W, A⁆ ≤ Z) :
    conjugatesIn A F ≤ normalizer (K : Set G) := by
  apply iSup_le
  intro g
  have hW := mem_normalizer_iff_map_conj_eq.mp (hFW (F.inv_mem g.property))
  have hZ := mem_normalizer_iff_map_conj_eq.mp (hFZ (F.inv_mem g.property))
  change W.map (MulAut.conj (g : G)⁻¹).toMonoidHom = W at hW
  change Z.map (MulAut.conj (g : G)⁻¹).toMonoidHom = Z at hZ
  have hc : ⁅W, rightConjugate A g⁆ ≤ Z := by
    rw [← hW, rightConjugate, ← map_commutator, ← hZ]
    exact map_mono hcomm
  exact le_normalizer_iff_commutator_le_left.mpr
    ((commutator_mono hKW le_rfl).trans (hc.trans hZK))

variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}
  {source : LocalSource L R} {geometry : Geometry R}

/-- A critical actor moves the local span outside its central Z-layer.
All normalizers in the proof are relative to the actual vertex stabilizer. -/
theorem localSpan_commutator_not_le_center (common : CommonFacts R source geometry)
    {a c d : Vertex R} (hc : color R c = false)
    (hcrit : CriticalPair R c d (geometry.exists_critical c hc))
    (hac : (cosetGraph R).dist a c = 2)
    (hpath : (cosetGraph R).dist a d + 2 = (cosetGraph R).dist c d) :
    ¬ ⁅localZSpan R a c, Z R d⁆ ≤ Z R c := by
  intro hcomm
  have hnorm := conjugates_normalize_of_commutator_le (Z R d) (stabilizer R c)
    (localZSpan R a c) (Z R c) (Z R a ⊔ Z R c)
    (localZSpan_normalized R a c) (Z_normalized R c) le_sup_right
    (sup_le (Z_le_localZSpan R a c) (LocalCommutator.center_Z_le_span hc hac)) hcomm
  have hQ : Q R c ≤ normalizer (Z R a ⊔ Z R c : Subgroup (FreeAmalgam R)) :=
    (le_inf ((Q_le_stabilizer_of_dist_two R c a hc (by rwa [SimpleGraph.dist_comm])).trans
      (Z_normalized R a))
      ((show Q R c ≤ stabilizer R c from fun _ hx => hx.1).trans (Z_normalized R c))).trans
      (normalizer_inf_normalizer_le_normalizer_sup _ _)
  have hd := critical_endpoint_color R c hc _ hcrit
  have hgen := Escape.Initial.local_conjugate_generation source c hc (Z R d)
    (source.critical_Z_le_stabilizer geometry c hc d hcrit).2
    (common.critical_reverse c hc d hd hcrit).2
  have hpos : 0 < criticalDistance R c (geometry.exists_critical c hc) := by
    rw [geometry.distance_constant c hc]
    exact lt_trans (by decide : 0 < 2) common.large_distance
  have hnot := critical_nonnormal_reverse R geometry common.centralizer common.escape
    c hc hpos hcrit a (by rwa [SimpleGraph.dist_comm]) hpath
  rw [common.X_eq_Z c hc] at hnot
  apply hnot.2
  apply normal_subgroupOf_of_le_normalizer
  rw [← hgen]
  exact sup_le hnorm hQ

namespace Configuration
variable {a a' : Vertex R} {p : CriticalPath R geometry a a'}
  (s : Configuration p) (hb : 4 < geometry.b R)

include hb

/-- The literal [V₁,Zδ] ≰ Z_(a+2) on the retained backward configuration. -/
theorem reverseSpan_commutator_not_le_second_Z (common : CommonFacts R source geometry) :
    ¬ ⁅localZSpan R a (p.walk.getVert 2), Z R s.delta⁆ ≤ Z R (p.walk.getVert 2) := by
  have hl := p.length_eq_b
  have hc : color R (p.walk.getVert 2) = false := (p.vertex_color (by omega)).mpr (by decide)
  apply localSpan_commutator_not_le_center common hc
    (common.critical_reverse s.delta s.delta_color _ hc (s.backward_critical hb))
    (p.dist_start (by omega))
  rw [SimpleGraph.dist_comm (u := a), s.distance_start hb,
    SimpleGraph.dist_comm (u := p.walk.getVert 2), s.distance_second hb]
  omega


/-- Joint normality transfers the reverse-span obstruction to R₁.
The preceding printed forward-commutator bound remains explicit. -/
theorem firstCommutator_not_le_second_Z_of_forward_bound
    (common : CommonFacts R source geometry)
    (hnorm : stabilizer R a ≤ normalizer (jointSpan p))
    (hforwardComm : ⁅localZSpan R (p.walk.getVert 2) a, Z R s.delta⁆ ≤
      Z R (p.walk.getVert 2)) :
    ¬ s.firstCommutator ≤ Z R (p.walk.getVert 2) := by
  intro hfirst
  have hd : (cosetGraph R).dist a (p.walk.getVert 2) = 2 :=
    p.dist_start (by have hl := p.length_eq_b; omega)
  have hc : color R (p.walk.getVert 2) = false :=
    (p.vertex_color (by have hl := p.length_eq_b; omega)).mpr (by decide)
  have hV : localZSpan R (p.walk.getVert 2) a ≤ stabilizer R (p.walk.getVert 2) :=
    (localZSpan_le_Q R p.start_color (by rw [SimpleGraph.dist_comm, hd])
      (by omega : 2 < geometry.b R)).trans
      (Q_le_stabilizer_of_dist_two R a _ p.start_color hd)
  have hW : localZSpan R a (p.walk.getVert 2) ≤ stabilizer R (p.walk.getVert 2) :=
    (localZSpan_le_Q R hc hd.le (by omega : 2 < geometry.b R)).trans (fun _ hx => hx.1)
  have hJ : jointSpan p ≤ stabilizer R (p.walk.getVert 2) := sup_le hV hW
  have heq : (jointSpan p).map (MulAut.conj s.g⁻¹).toMonoidHom = jointSpan p :=
    mem_normalizer_iff_map_conj_eq.mp (hnorm ((stabilizer R a).inv_mem s.mem_stabilizer))
  have hVeq : (localZSpan R (p.walk.getVert 2) a).map
      (MulAut.conj s.g⁻¹).toMonoidHom = localZSpan R (p.walk.getVert 2) a :=
    mem_normalizer_iff_map_conj_eq.mp
      (localZSpan_normalized R _ a ((stabilizer R a).inv_mem s.mem_stabilizer))
  have hsplit : localZSpan R (p.walk.getVert 2) a ⊔
      (localZSpan R a (p.walk.getVert 2)).map (MulAut.conj s.g⁻¹).toMonoidHom =
        jointSpan p := by
    simpa only [jointSpan, Subgroup.map_sup, hVeq] using heq
  have hconj : (localZSpan R a (p.walk.getVert 2)).map (MulAut.conj s.g⁻¹).toMonoidHom ≤
      stabilizer R (p.walk.getVert 2) := (hsplit ▸ le_sup_right).trans hJ
  have hpre : jointSpan p ≤ commutatorPreimage (stabilizer R (p.walk.getVert 2))
      (Z R s.delta) (Z R (p.walk.getVert 2)) := by
    rw [← hsplit]
    exact sup_le (le_commutatorPreimage hV hforwardComm)
      (le_commutatorPreimage hconj hfirst)
  apply s.reverseSpan_commutator_not_le_second_Z hb common
  exact (commutator_mono (le_sup_right.trans hpre) le_rfl).trans
    (commutator_commutatorPreimage_le _ _ _ (Z_normalized R _))


/-- In particular R₁ is nontrivial once the preceding forward bound is known. -/
theorem firstCommutator_ne_bot_of_forward_bound
    (common : CommonFacts R source geometry)
    (hnorm : stabilizer R a ≤ normalizer (jointSpan p))
    (hforwardComm : ⁅localZSpan R (p.walk.getVert 2) a, Z R s.delta⁆ ≤
      Z R (p.walk.getVert 2)) : s.firstCommutator ≠ ⊥ := by
  intro h
  exact s.firstCommutator_not_le_second_Z_of_forward_bound hb common hnorm hforwardComm
    (h ▸ bot_le)

/-- Nontriviality in Uδ excludes containment in the source fixed core Dδ. -/
theorem firstCommutator_not_le_delta_fixed_of_forward_bound
    (common : CommonFacts R source geometry)
    (hnorm : stabilizer R a ≤ normalizer (jointSpan p))
    (hforwardComm : ⁅localZSpan R (p.walk.getVert 2) a, Z R s.delta⁆ ≤
      Z R (p.walk.getVert 2)) : ¬ s.firstCommutator ≤ fixedCore R s.delta := by
  intro h
  apply s.firstCommutator_ne_bot_of_forward_bound hb common hnorm hforwardComm
  apply le_bot_iff.mp
  rw [← Escape.EdgeTransfer.U_fixed_eq_bot (moduleFacts common) s.delta s.delta_color]
  exact le_inf (s.firstCommutator_le_delta_natural hb source) (h.trans inf_le_right)

end Configuration
end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.RegularPaths.OrbitEscape.CommutatorContradiction
