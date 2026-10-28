module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Flags.RankOne.Marked
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Natural
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.SectionThree.CriticalModules.LocalStructure
public import Theory.GroupTheory.CommutatorPreimage

/-!
# Assembly of the local consequences of MS93 (4.6.9)

A critical-path covering controls the action of the far Z-layer on Q_alpha
modulo V_alpha. The centralizer of that action is normal in G_alpha and
has nontrivial image in its marked simple quotient. It therefore contains
the two-residual, giving the required core containment.

The printed comparison of edge generators bounds the edge-star commutator
by U_alpha. The existing starred-span generation then bounds V_alpha-prime
by U_alpha. Noncentrality makes that subgroup nontrivial, and the actual
marked natural action proves equality.

LocalDisplacement and the edge comparison are explicit intermediate inputs
to the assembly theorem, not additional source hypotheses. The Consequences
entry point constructs both from FlagControl and completes this deduction.
Source: Meierfrankenfeld--Stellmacher (1993), (4.6.9), printed p.908.
-/

@[expose] public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
open scoped commutatorElement
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Flags.RankOne
variable {M : Type*} [Group M] {L R : Subgroup M}

/-- The supplied natural marking makes any nontrivial invariant subgroup all of U. -/
theorem natural_subgroup_eq (source : LocalSource L R) (natural : NaturalU R source.projection)
    (D : Subgroup (FreeAmalgam R)) (hDU : D ≤ U R (alpha R)) (hne : D ≠ ⊥)
    (hD : stabilizer R (alpha R) ≤ normalizer (D : Set (FreeAmalgam R))) :
    D = U R (alpha R) := by
  apply le_antisymm hDU
  have hex : ∃ x ∈ D, x ≠ 1 := by
    by_contra! h
    exact hne (le_bot_iff.mp (fun x hx => h x hx))
  obtain ⟨x, hx, hx1⟩ := hex
  let u : U R (alpha R) := ⟨x, hDU hx⟩
  have hu : (natural.equiv u).toAdd ≠ 0 := by
    intro hh
    apply hx1
    have hh' : natural.equiv u = 1 := hh
    exact congrArg Subtype.val (natural.equiv.map_eq_one_iff.mp hh')
  intro y hy
  by_cases hy1 : y = 1
  · simpa only [hy1] using D.one_mem
  let v : U R (alpha R) := ⟨y, hy⟩
  have hv : (natural.equiv v).toAdd ≠ 0 := by
    intro hh
    apply hy1
    have hh' : natural.equiv v = 1 := hh
    exact congrArg Subtype.val (natural.equiv.map_eq_one_iff.mp hh')
  obtain ⟨g, hg⟩ := Linear.natural_orbit hu hv
  obtain ⟨m, hm⟩ := source.projection_surjective (natural.marking.symm g)
  have hmG : embedM R m ∈ stabilizer R (alpha R) := by
    rw [alpha, stabilizer_m_base]
    exact ⟨m, rfl⟩
  have hxD : embedM R m * x * (embedM R m)⁻¹ ∈ D :=
    le_normalizer_iff.mp hD _ hmG _ hx
  let w : U R (alpha R) := ⟨_, hDU hxD⟩
  have hw : w = v := by
    apply natural.equiv.injective
    have hh := natural.action m u w rfl
    rw [hm, natural.marking.apply_symm_apply, hg] at hh
    exact hh
  have hw' : embedM R m * x * (embedM R m)⁻¹ = y := congrArg Subtype.val hw
  rwa [hw'] at hxD

/-- Noncentrality and the marked natural action supply the reverse derived inclusion. -/
theorem radius_derived_eq_of_le (source : LocalSource L R) (geometry : Geometry R)
    (common : CommonFacts R source geometry) (early : EarlyFacts R geometry)
    (h : ⁅V R (alpha R), V R (alpha R)⁆ ≤ U R (alpha R)) :
    ⁅V R (alpha R), V R (alpha R)⁆ = U R (alpha R) := by
  apply natural_subgroup_eq source common.natural _ h
  · intro hz
    apply early.derived_noncentral (alpha R) rfl
    rw [hz]
    exact bot_le
  · intro g hg
    rw [mem_normalizer_iff_map_conj_eq, map_commutator]
    have hh := mem_normalizer_iff_map_conj_eq.mp
      (DistanceEight.V_normalized R (alpha R) hg)
    rw [hh]

/-- The central fixed summand makes all local displacements of Z lie in U. -/
theorem Z_stabilizer_commutator_le_U [Finite M] (source : LocalSource L R)
    (geometry : Geometry R) (common : CommonFacts R source geometry) :
    ⁅Z R (alpha R), stabilizer R (alpha R)⁆ ≤ U R (alpha R) := by
  let naturalData : BinaryNaturalStructure source :=
    ⟨common.X_eq_Z, common.natural, common.decomposition, common.disjoint⟩
  have hsplit := naturalData.decomposition_at (alpha R) rfl
  have hh := commutator_eq_of_centralizing_sup
    ((sup_comm _ _).trans hsplit.symm) inf_le_right
    ((DistanceEight.U_le_Z R _).trans ((Z_le_stabilizer R _).trans
      (stabilizer R (alpha R)).le_normalizer))
  rw [commutator_comm, ← hh]
  exact le_normalizer_iff_commutator_le_right.mp (U_normalized (alpha R))

/-- The printed edge-generator comparison bounds the complete edge star. -/
theorem edge_commutator_le_of_comparison [Finite M] (source : LocalSource L R)
    (geometry : Geometry R) (common : CommonFacts R source geometry)
    (hcompare : ∀ t, nu R geometry (alpha R) t → Adjacent R (beta R) t →
      ⁅Z R t, Q R (beta R)⁆ = ⁅Z R (alpha R), Q R (beta R)⁆) :
    ⁅edgeStar R geometry (alpha R) (beta R), Q R (alpha R)⁆ ≤ U R (alpha R) := by
  have hQ : Q R (alpha R) ≤ Q R (beta R) :=
    Q_le_adjacent_h R rfl (base_adjacent R)
  have hlocal : Q R (beta R) ≤ stabilizer R (alpha R) :=
    fun _ hx => hx.2 _ (adjacent_symm R (base_adjacent R))
  have hpre : edgeStar R geometry (alpha R) (beta R) ≤
      commutatorPreimage (stabilizer R (alpha R)) (Q R (alpha R)) (U R (alpha R)) := by
    apply iSup_le
    intro t
    apply iSup_le
    rintro ⟨ht, hbt⟩
    have htV : Z R t ≤ V R (alpha R) :=
      le_iSup_of_le t (le_iSup_of_le ht.1.le le_rfl)
    apply le_commutatorPreimage
    · exact htV.trans ((V_le_Q geometry common.large_distance (alpha R) rfl).trans
        (fun _ hx => hx.1))
    · calc
        ⁅Z R t, Q R (alpha R)⁆ ≤ ⁅Z R t, Q R (beta R)⁆ := commutator_mono le_rfl hQ
        _ = ⁅Z R (alpha R), Q R (beta R)⁆ := hcompare t ht hbt
        _ ≤ ⁅Z R (alpha R), stabilizer R (alpha R)⁆ := commutator_mono le_rfl hlocal
        _ ≤ U R (alpha R) := Z_stabilizer_commutator_le_U source geometry common
  exact (commutator_mono hpre le_rfl).trans
    (commutator_commutatorPreimage_le _ _ _ (U_normalized (alpha R)))

/-- The edge comparison also determines the whole derived radius group. -/
theorem radius_derived_eq_of_comparison [Finite M] (source : LocalSource L R)
    (geometry : Geometry R) (common : CommonFacts R source geometry)
    (early : EarlyFacts R geometry)
    (hcompare : ∀ t, nu R geometry (alpha R) t → Adjacent R (beta R) t →
      ⁅Z R t, Q R (beta R)⁆ = ⁅Z R (alpha R), Q R (beta R)⁆) :
    ⁅V R (alpha R), V R (alpha R)⁆ = U R (alpha R) := by
  apply radius_derived_eq_of_le source geometry common early
  exact (derived_le_star_commutator geometry early common.large_distance
    (alpha R) (beta R) rfl (base_adjacent R)).trans
    (star_commutator_le_of_edge geometry common.large_distance (alpha R) (beta R) rfl
      (edge_commutator_le_of_comparison source geometry common hcompare))

/-- A normal centralizer in the marked simple quotient absorbs the local two-residual. -/
theorem core_le_radius_of_external_commutator [Finite M] (source : LocalSource L R)
    (J : Subgroup (FreeAmalgam R)) (hJ : J ≤ stabilizer R (alpha R))
    (hnot : ¬ J ≤ Q R (alpha R)) (hcomm : ⁅Q R (alpha R), J⁆ ≤ V R (alpha R)) :
    core R (alpha R) ≤ V R (alpha R) := by
  let S := stabilizer R (alpha R)
  let A := commutatorPreimage S (Q R (alpha R)) (V R (alpha R))
  let N := A.comap (embedM R)
  have hS : S ≤ normalizer (V R (alpha R) : Set (FreeAmalgam R)) :=
    DistanceEight.V_normalized R (alpha R)
  have hA : S ≤ normalizer (A : Set (FreeAmalgam R)) :=
    commutatorPreimage_normalized _ _ _ _ hS S.le_normalizer (Q_normalized R _) hS
  have hJA : J ≤ A := le_commutatorPreimage hJ (by rwa [commutator_comm])
  have hmap : N.map (embedM R) = A := by
    rw [map_comap_eq]
    apply inf_eq_right.mpr
    exact (commutatorPreimage_le S _ _).trans (by
      change stabilizer R (alpha R) ≤ (embedM R).range
      rw [alpha, stabilizer_m_base]
      exact le_rfl)
  let : N.Normal := by
    constructor
    intro n hn m
    have hm : embedM R m ∈ S := by
      rw [show S = stabilizer R (alpha R) from rfl, alpha, stabilizer_m_base]
      exact ⟨m, rfl⟩
    have hh := le_normalizer_iff.mp hA _ hm _ hn
    change embedM R (m * n * m⁻¹) ∈ A
    simpa only [map_mul, map_inv] using hh
  let : IsSimpleGroup SL := Atlas.Comparisons.Exceptional.sl3Two_simple
  have hN : ¬ N ≤ pCore 2 M := by
    intro hn
    apply hnot
    calc
      J ≤ A := hJA
      _ = N.map (embedM R) := hmap.symm
      _ ≤ (pCore 2 M).map (embedM R) := map_mono hn
      _ = Q R (alpha R) := (Q_alpha R source.two_group source.core_le).symm
  have hn : (N.map source.projection).Normal := Normal.map inferInstance _ source.projection_surjective
  have htop : N.map source.projection = ⊤ := by
    rcases hn.eq_bot_or_eq_top with hh | hh
    · exact (hN (by simpa only [source.projection_kernel] using
        (Subgroup.map_eq_bot_iff _).mp hh)).elim
    · exact hh
  have hL : Ltilde R (alpha R) ≤ A := by
    rw [Ltilde_alpha, source.residual, ← hmap]
    exact map_mono (source.residual_le_of_image_top N htop)
  rw [core, commutator_comm]
  exact (commutator_mono hL le_rfl).trans
    (commutator_commutatorPreimage_le _ _ _ hS)

/-- The local covering extracted from the first paragraph of (4.6.9).
The endpoint and its midpoint retain their genuine critical-path distances. -/
def LocalDisplacement (R : Subgroup M) (geometry : Geometry R) : Prop :=
  ∃ a' c : Vertex R,
    CriticalPair R (alpha R) a' (geometry.exists_critical (alpha R) rfl) ∧
    (cosetGraph R).dist (alpha R) c = 2 ∧
    (cosetGraph R).dist c a' = 2 ∧
    Q R (alpha R) ≤ V R (alpha R) ⊔ Q R c

/-- The source covering controls Q on the critical endpoint, hence controls the core. -/
theorem core_le_radius_of_displacement [Finite M] (source : LocalSource L R)
    (geometry : Geometry R) (common : CommonFacts R source geometry)
    (early : EarlyFacts R geometry)
    (displacement : LocalDisplacement R geometry) :
    core R (alpha R) ≤ V R (alpha R) := by
  obtain ⟨a', c, hcrit, hac, hca', hcover⟩ := displacement
  have ha' : color R a' = false := critical_endpoint_color R (alpha R) rfl _ hcrit
  have hc : color R c = false := by
    obtain ⟨p, hp⟩ := (cosetGraph_connected R).exists_walk_length_eq_dist (alpha R) c
    exact ((walk_even_iff_color_eq R p).mp (by rw [hp, hac]; decide)).symm
  have hJ : Z R a' ≤ stabilizer R (alpha R) := by
    apply geometry.Z_le_stabilizer_of_dist_le_b a' ha'
    rw [SimpleGraph.dist_comm, hcrit.1]
    exact le_rfl
  apply core_le_radius_of_external_commutator source (Z R a') hJ
    (common.critical_reverse (alpha R) rfl a' ha' hcrit).2
  have hZc : Z R c ≤ V R (alpha R) :=
    le_iSup_of_le c (le_iSup_of_le (by rw [SimpleGraph.dist_comm, hac]) le_rfl)
  have hZa' : Z R a' ≤ V R c :=
    le_iSup_of_le a' (le_iSup_of_le (by rw [SimpleGraph.dist_comm, hca']) le_rfl)
  have hQc : Q R c ≤ stabilizer R (alpha R) :=
    Q_le_stabilizer_of_dist_le_two c (alpha R) hc rfl
      (by rw [SimpleGraph.dist_comm, hac])
  have hfirst : ⁅V R (alpha R), Z R a'⁆ ≤ V R (alpha R) :=
    le_normalizer_iff_commutator_le_left.mp
      (hJ.trans (DistanceEight.V_normalized R (alpha R)))
  have hsecond : ⁅Q R c, Z R a'⁆ ≤ V R (alpha R) := by
    rw [commutator_comm]
    exact ((commutator_mono hZa' le_rfl).trans (early.commutator_le_Z c hc)).trans hZc
  have hpre : V R (alpha R) ⊔ Q R c ≤
      commutatorPreimage (stabilizer R (alpha R)) (Z R a') (V R (alpha R)) :=
    sup_le (le_commutatorPreimage (geometry.V_local (alpha R) rfl common.large_distance) hfirst)
      (le_commutatorPreimage hQc hsecond)
  exact (commutator_mono (hcover.trans hpre) le_rfl).trans
    (commutator_commutatorPreimage_le _ _ _ (DistanceEight.V_normalized R (alpha R)))

/-- Assembly from the actual local displacement and edge-generator comparison.
The Consequences entry point supplies both from FlagControl. -/
theorem baseConclusions_of_displacement_comparison [Finite M] (source : LocalSource L R)
    (geometry : Geometry R) (common : CommonFacts R source geometry)
    (early : EarlyFacts R geometry)
    (displacement : LocalDisplacement R geometry)
    (hcompare : ∀ t, nu R geometry (alpha R) t → Adjacent R (beta R) t →
      ⁅Z R t, Q R (beta R)⁆ = ⁅Z R (alpha R), Q R (beta R)⁆) :
    BaseConclusions R geometry where
  radius_derived := radius_derived_eq_of_comparison source geometry common early hcompare
  core_le_radius := core_le_radius_of_displacement source geometry common early displacement
  edge_commutator_le := edge_commutator_le_of_comparison source geometry common hcompare
end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Flags.RankOne
