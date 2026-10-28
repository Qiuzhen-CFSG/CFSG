module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Flags.RankOne.Consequences.Quotient
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Flags.RankOne.Consequences.Assembly

/-!
# Deductions from the first MS93 displacement calculation

Noncentrality of the radius-derived subgroup supplies a noncentral generator
beyond the distinguished edge. Extending that choice to a critical path is
kept explicit in `NoncentralCriticalPath`; both midpoint distances and the
actual critical endpoint are retained.

For such a path, disjointness of [Z_c,V_alpha] from Z(G_alpha) makes Bzero
centralize Z_c, hence puts it in Q_c. The index-two edge layer then bounds
[Bzero,Z_endpoint] by Z_alpha. The simple marked quotient and the genuine
two-residual imply Bzero = B_alpha. Separately, displacement index four
exhausts Q_beta/Q_c and gives V_alpha joined with Q_c equal to Q_beta.

These are conditional deductions, not a construction of the critical path
or of the displacement cardinalities from FlagControl. Their final assembly
remains in Consequences.Displacement. No core containment, radius-derived
equality, or generation by the commutator core is assumed.

Source: Meierfrankenfeld--Stellmacher, *Pushing up weak BN-pairs of rank two*
(1993), first two paragraphs of (4.6.9), printed p.908; the reference there
to noncentrality is the second (4.6.6), on pp.903--904.
-/

@[expose] public section
open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Flags.RankOne
variable {M : Type*} [Group M] {L R : Subgroup M}

/-- Noncentrality of the derived radius group selects a noncentral
edge generator. This does not yet extend it to a critical path. -/
theorem exists_noncentral_edge_generator [Finite M] (geometry : Geometry R)
    (hlarge : 2 < geometry.b R) (early : EarlyFacts R geometry) :
    ∃ c, nu R geometry (alpha R) c ∧ Adjacent R (beta R) c ∧
      ¬ ⁅Z R c, V R (alpha R)⁆ ≤
        (center (stabilizer R (alpha R))).map (stabilizer R (alpha R)).subtype := by
  classical
  by_contra! hn
  have hV := geometry.V_local (alpha R) rfl hlarge
  have hB : B R (alpha R) (geometry.Z_normal (alpha R)) ≤ Bzero geometry (alpha R) := by
    rw [early.B_eq_center _ rfl]
    exact radius_center_le_Bzero geometry _ hV
  have hedge : edgeStar R geometry (alpha R) (beta R) ≤ Bzero geometry (alpha R) := by
    apply iSup_le
    intro c
    apply iSup_le
    rintro ⟨hc, hbc⟩
    have hZc : Z R c ≤ V R (alpha R) :=
      le_iSup_of_le c (le_iSup_of_le hc.1.le le_rfl)
    apply (le_Bzero_iff geometry (alpha R) hV _).mpr
    exact ⟨hZc, le_inf
      ((commutator_mono hZc (V_le_Q geometry hlarge _ rfl)).trans
        (early.commutator_le_Z _ rfl)) (hn c hc hbc)⟩
  have hstar : VStar R geometry (alpha R) (beta R) ≤ Bzero geometry (alpha R) :=
    iSup_conjugates_le_of_le_normalizer _ _ _ hedge
      (Bzero_normalized geometry (alpha R) hV)
  have hfull : V R (alpha R) ≤ Bzero geometry (alpha R) := by
    rw [radius_eq_B_sup_star geometry early hlarge (alpha R) (beta R) rfl (base_adjacent R)]
    exact sup_le hB hstar
  exact early.derived_noncentral _ rfl
    (((le_Bzero_iff geometry (alpha R) hV _).mp hfull).2.trans inf_le_right)

/-- A genuine critical path through the distinguished edge, with the
noncentral displacement used at the start of (4.6.9). -/
structure NoncentralCriticalPath (R : Subgroup M) (geometry : Geometry R) where
  endpoint : Vertex R
  middle : Vertex R
  critical : CriticalPair R (alpha R) endpoint (geometry.exists_critical (alpha R) rfl)
  first_distance : (cosetGraph R).dist (alpha R) middle = 2
  second_distance : (cosetGraph R).dist middle endpoint = 2
  edge : Adjacent R (beta R) middle
  noncentral : ¬ ⁅Z R middle, V R (alpha R)⁆ ≤
    (center (stabilizer R (alpha R))).map (stabilizer R (alpha R)).subtype

private theorem midpoint_color (geometry : Geometry R)
    (p : NoncentralCriticalPath R geometry) : color R p.middle = false := by
  have h := adjacent_color_ne R p.edge
  have hb : color R (beta R) = true := rfl
  cases he : color R p.middle <;> simp_all

private theorem residual_le_normal_of_external [Finite M] (source : LocalSource L R)
    (N J : Subgroup (FreeAmalgam R)) (hN : N ≤ stabilizer R (alpha R))
    (hNnormal : stabilizer R (alpha R) ≤ normalizer (N : Set (FreeAmalgam R)))
    (hJN : J ≤ N) (hJnot : ¬ J ≤ Q R (alpha R)) : Ltilde R (alpha R) ≤ N := by
  let A := N.comap (embedM R)
  have hmap : A.map (embedM R) = N := by
    rw [map_comap_eq]
    apply inf_eq_right.mpr
    exact hN.trans (by rw [alpha, stabilizer_m_base]; exact le_rfl)
  let : A.Normal := by
    constructor
    intro n hn m
    have hm : embedM R m ∈ stabilizer R (alpha R) := by
      rw [alpha, stabilizer_m_base]
      exact ⟨m, rfl⟩
    have hh := le_normalizer_iff.mp hNnormal _ hm _ hn
    change embedM R (m * n * m⁻¹) ∈ N
    simpa only [map_mul, map_inv] using hh
  let : IsSimpleGroup SL := Atlas.Comparisons.Exceptional.sl3Two_simple
  have hA : ¬ A ≤ pCore 2 M := by
    intro ha
    apply hJnot
    calc
      J ≤ N := hJN
      _ = A.map (embedM R) := hmap.symm
      _ ≤ (pCore 2 M).map (embedM R) := map_mono ha
      _ = Q R (alpha R) := (Q_alpha R source.two_group source.core_le).symm
  have hn : (A.map source.projection).Normal :=
    Normal.map inferInstance _ source.projection_surjective
  have htop : A.map source.projection = ⊤ := by
    rcases hn.eq_bot_or_eq_top with hh | hh
    · exact (hA (by simpa only [source.projection_kernel] using
        (Subgroup.map_eq_bot_iff _).mp hh)).elim
    · exact hh
  rw [Ltilde_alpha, source.residual, ← hmap]
  exact map_mono (source.residual_le_of_image_top A htop)

/-- A non-kernel actor centralizing B₀ modulo Z forces B₀ into B. -/
theorem Bzero_le_B_of_external_commutator [Finite M] (source : LocalSource L R)
    (geometry : Geometry R) (hlarge : 2 < geometry.b R)
    (J : Subgroup (FreeAmalgam R)) (hJ : J ≤ stabilizer R (alpha R))
    (hnot : ¬ J ≤ Q R (alpha R))
    (hcomm : ⁅Bzero geometry (alpha R), J⁆ ≤ Z R (alpha R)) :
    Bzero geometry (alpha R) ≤ B R (alpha R) (geometry.Z_normal (alpha R)) := by
  have hV := geometry.V_local (alpha R) rfl hlarge
  have hB := Bzero_normalized geometry (alpha R) hV
  let N := commutatorPreimage (stabilizer R (alpha R))
    (Bzero geometry (alpha R)) (Z R (alpha R))
  have hNN : stabilizer R (alpha R) ≤ normalizer (N : Set (FreeAmalgam R)) :=
    commutatorPreimage_normalized _ _ _ _ (Z_normalized R _)
      (stabilizer R (alpha R)).le_normalizer hB (Z_normalized R _)
  have hLN : Ltilde R (alpha R) ≤ N :=
    residual_le_normal_of_external source N J (commutatorPreimage_le _ _ _) hNN
      (le_commutatorPreimage hJ (by rwa [commutator_comm])) hnot
  have hLB : ⁅Ltilde R (alpha R), Bzero geometry (alpha R)⁆ ≤ Z R (alpha R) :=
    (commutator_mono hLN le_rfl).trans
      (commutator_commutatorPreimage_le _ _ _ (Z_normalized R _))
  intro x hx
  apply (mem_B_iff R (alpha R) (geometry.Z_normal (alpha R)) hV x).mpr
  exact ⟨Bzero_le_radius geometry _ hx,
    fun l hl => hLB (commutator_mem_commutator hl hx)⟩

/-- The central-disjointness calculation in the source suffices to identify B₀. -/
theorem Bzero_eq_of_disjoint_displacement [Finite M] (source : LocalSource L R)
    (geometry : Geometry R) (common : CommonFacts R source geometry)
    (early : EarlyFacts R geometry) (p : NoncentralCriticalPath R geometry)
    (hdisj : Disjoint ⁅Z R p.middle, V R (alpha R)⁆
      ((center (stabilizer R (alpha R))).map (stabilizer R (alpha R)).subtype)) :
    Bzero geometry (alpha R) = B R (alpha R) (geometry.Z_normal (alpha R)) := by
  have hV := geometry.V_local (alpha R) rfl common.large_distance
  have hc := midpoint_color geometry p
  have hZc : Z R p.middle ≤ V R (alpha R) :=
    le_iSup_of_le p.middle (le_iSup_of_le (by rw [SimpleGraph.dist_comm, p.first_distance]) le_rfl)
  have hBcomm : ⁅Bzero geometry (alpha R), Z R p.middle⁆ = ⊥ := by
    apply le_bot_iff.mp
    apply (disjoint_iff.mp hdisj).le.trans' (le_inf ?_ ?_)
    · rw [commutator_comm]
      exact commutator_mono le_rfl (Bzero_le_radius geometry _)
    · exact ((commutator_mono le_rfl hZc).trans
        ((le_Bzero_iff geometry (alpha R) hV _).mp le_rfl).2).trans inf_le_right
  have hBQ : Bzero geometry (alpha R) ≤ Q R p.middle := by
    rw [← common.centralizer p.middle (beta R) hc (adjacent_symm R p.edge)]
    exact le_inf ((Bzero_le_radius geometry _).trans
      ((V_le_Q geometry common.large_distance _ rfl).trans
        (Q_le_adjacent_h R rfl (base_adjacent R))))
      (commutator_eq_bot_iff_le_centralizer.mp hBcomm)
  have hZbB : Z R (beta R) ≤ Bzero geometry (alpha R) :=
    (edge_Z_le (alpha R) (beta R) rfl (base_adjacent R)).trans
      ((Z_le_B geometry (alpha R) hV).trans (by
        rw [early.B_eq_center _ rfl]
        exact radius_center_le_Bzero geometry _ hV))
  have hZbZc : Z R (beta R) ≤ Z R p.middle :=
    edge_Z_le p.middle (beta R) hc (adjacent_symm R p.edge)
  have hinter : Bzero geometry (alpha R) ⊓ Z R p.middle ≤ Z R (beta R) := by
    have hproper : ¬ Z R p.middle ≤ Bzero geometry (alpha R) := by
      intro h
      exact p.noncentral (((le_Bzero_iff geometry (alpha R) hV _).mp h).2.trans inf_le_right)
    have hi := relIndex_mul_relIndex (Z R (beta R))
      (Bzero geometry (alpha R) ⊓ Z R p.middle) (Z R p.middle)
      (le_inf hZbB hZbZc) inf_le_right
    rw [early.edge_Z_index p.middle (beta R) hc (adjacent_symm R p.edge)] at hi
    have hd : (Z R (beta R)).relIndex (Bzero geometry (alpha R) ⊓ Z R p.middle) ∣ 2 :=
      ⟨_, hi.symm⟩
    rcases Nat.prime_two.eq_one_or_self_of_dvd _ hd with he | he
    · exact relIndex_eq_one.mp he
    · rw [he] at hi
      have hone : (Bzero geometry (alpha R) ⊓ Z R p.middle).relIndex (Z R p.middle) = 1 := by omega
      exact (hproper ((relIndex_eq_one.mp hone).trans inf_le_left)).elim
  have ha' : color R p.endpoint = false :=
    critical_endpoint_color R (alpha R) rfl _ p.critical
  have hJ : Z R p.endpoint ≤ stabilizer R (alpha R) := by
    apply geometry.Z_le_stabilizer_of_dist_le_b p.endpoint ha'
    rw [SimpleGraph.dist_comm, p.critical.1]
    exact le_rfl
  have hJa : Z R p.endpoint ≤ V R p.middle :=
    le_iSup_of_le p.endpoint (le_iSup_of_le (by rw [SimpleGraph.dist_comm, p.second_distance]) le_rfl)
  have hcomm : ⁅Bzero geometry (alpha R), Z R p.endpoint⁆ ≤ Z R (alpha R) := by
    apply le_trans (le_inf ?_ ?_) (hinter.trans (edge_Z_le _ _ rfl (base_adjacent R)))
    · exact le_normalizer_iff_commutator_le_left.mp
        (hJ.trans (Bzero_normalized geometry (alpha R) hV))
    · rw [commutator_comm]
      exact (commutator_mono hJa hBQ).trans (early.commutator_le_Z p.middle hc)
  apply le_antisymm
  · exact Bzero_le_B_of_external_commutator source geometry common.large_distance _ hJ
      (common.critical_reverse _ rfl _ ha' p.critical).2 hcomm
  · rw [early.B_eq_center _ rfl]
    exact radius_center_le_Bzero geometry _ hV

/-- The displacement index exhausts the edge quotient, giving the printed product. -/
theorem radius_sup_midpoint_kernel [Finite M] (geometry : Geometry R)
    (hlarge : 2 < geometry.b R) (early : EarlyFacts R geometry)
    (c : Vertex R) (hc : color R c = false) (hbc : Adjacent R (beta R) c)
    (hindex : (Q R c).relIndex (V R (alpha R)) = 4) :
    V R (alpha R) ⊔ Q R c = Q R (beta R) := by
  have hVS : V R (alpha R) ≤ Q R (beta R) :=
    (V_le_Q geometry hlarge _ rfl).trans (Q_le_adjacent_h R rfl (base_adjacent R))
  have hKS : Q R c ≤ Q R (beta R) :=
    Q_le_adjacent_h R rfl (adjacent_symm R hbc)
  let A := (V R (alpha R)).subgroupOf (Q R (beta R))
  let K := (Q R c).subgroupOf (Q R (beta R))
  let : K.Normal := normal_subgroupOf_of_le_normalizer
    ((show Q R (beta R) ≤ stabilizer R c from fun _ hx => hx.2 c hbc).trans
      (Q_normalized R c))
  have hK : K.index = 4 := early.edge_Q_index c (beta R) hc (adjacent_symm R hbc)
  have hKA : K.relIndex A = 4 := by
    rw [relIndex_subgroupOf hVS]
    exact hindex
  have hmul := relIndex_mul_index (show K ≤ A ⊔ K from le_sup_right)
  rw [relIndex_sup_right, hKA, hK] at hmul
  have he : A ⊔ K = ⊤ := index_eq_one.mp (by omega)
  have hh := congrArg (Subgroup.map (Q R (beta R)).subtype) he
  dsimp only [A, K] at hh
  simpa only [Subgroup.map_sup, map_subgroupOf_eq_of_le hVS,
    map_subgroupOf_eq_of_le hKS, ← MonoidHom.range_eq_map, range_subtype] using hh

/-- Assembly from the two local displacement calculations. Their production
from the marked action and the source choice of path remains separate. -/
theorem localDisplacement_and_Bzero_of_calculation [Finite M] (source : LocalSource L R)
    (geometry : Geometry R) (common : CommonFacts R source geometry)
    (early : EarlyFacts R geometry) (p : NoncentralCriticalPath R geometry)
    (hindex : (Q R p.middle).relIndex (V R (alpha R)) = 4)
    (hdisj : Disjoint ⁅Z R p.middle, V R (alpha R)⁆
      ((center (stabilizer R (alpha R))).map (stabilizer R (alpha R)).subtype)) :
    LocalDisplacement R geometry ∧
      Bzero geometry (alpha R) = B R (alpha R) (geometry.Z_normal (alpha R)) := by
  refine ⟨⟨p.endpoint, p.middle, p.critical, p.first_distance, p.second_distance, ?_⟩,
    Bzero_eq_of_disjoint_displacement source geometry common early p hdisj⟩
  rw [radius_sup_midpoint_kernel geometry common.large_distance early p.middle
    (midpoint_color geometry p) p.edge hindex]
  exact Q_le_adjacent_h R rfl (base_adjacent R)

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Flags.RankOne
