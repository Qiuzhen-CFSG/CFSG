module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Flags.RankOne.Triple.Natural.GeometryBound.Incidence
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Flags.RankOne.Triple.Preparatory.Incident.Coverage
public import Theory.GroupTheory.Commutator.NormalizedIndexTwo

/-!
# Displacement and fixed subgroups in the p.905 symmetry argument

The strict layer displacement fills the order-four quotient of the edge
kernel by the midpoint kernel. The latter centralizes the midpoint Z-layer,
so the commutator against the actual conjugate layer equals the full edge
commutator. The index-two edge fixed subgroup also bounds the displacement
of every edge-layer generator. Conjugating this bound puts the full midpoint
commutator in the literal fixed subgroup at each selected local flag.

`FlagP905PencilFacts` specifies the remaining finite local-geometry input:
incident core intersections have order at most two modulo Q_alpha, and two
distinct pencils have flags whose common fixed intersection with Z_beta is
central. This module does not construct those facts or assert the source
symmetry conclusion without them.

Source: Meierfrankenfeld--Stellmacher, *Pushing up weak BN-pairs of rank two*
(1993), final paragraph of (4.6.8), claim (1), printed p.905.
-/

@[expose] public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Flags.RankOne
variable {M : Type*} [Group M] {L R : Subgroup M}

/-- The edge index-two quotient has trivial action under its edge kernel. -/
theorem edge_commutator_le_edgeZ_of_early {geometry : Geometry R} (early : EarlyFacts R geometry)
    (a b : Vertex R) (ha : color R a = false) (hab : Adjacent R a b) :
    ⁅Z R a, Q R b⁆ ≤ Z R b :=
  commutator_le_of_normalized_index_two _ _ _ (edge_Z_le a b ha hab)
    (early.edge_Z_index a b ha hab)
    ((show Q R b ≤ stabilizer R a from fun _ hx => hx.2 a (adjacent_symm R hab)).trans
      (Z_normalized R a))
    ((show Q R b ≤ stabilizer R b from fun _ hx => hx.1).trans (Z_normalized R b))

/-- The entire edge layer has displacement in the edge omega-center. -/
theorem edgeRadius_commutator_le_edgeZ (geometry : Geometry R)
    (hlarge : 2 < geometry.b R) (early : EarlyFacts R geometry) :
    ⁅V R (beta R), Q R (beta R)⁆ ≤ Z R (beta R) := by
  have hVQ : V R (beta R) ≤ stabilizer R (beta R) := by
    exact (edgeRadius_le_Q_alpha geometry hlarge).trans
      (fun _ hx => hx.2 (beta R) (base_adjacent R))
  have hpre : V R (beta R) ≤
      commutatorPreimage (V R (beta R)) (Q R (beta R)) (Z R (beta R)) := by
    rw [V_eq_neighborSpan (alpha R) (beta R) rfl (base_adjacent R)]
    apply iSup_le
    intro t
    apply iSup_le
    intro ht
    apply le_commutatorPreimage
      (show Z R t ≤ neighborSpan (beta R) from le_iSup_of_le t (le_iSup_of_le ht le_rfl))
    have hcol : color R t = false := by
      have hne := adjacent_color_ne R ht
      have hbeta : color R (beta R) = true := rfl
      cases h : color R t <;> simp_all
    exact edge_commutator_le_edgeZ_of_early early t (beta R) hcol (adjacent_symm R ht)
  exact (commutator_mono hpre le_rfl).trans
    (commutator_commutatorPreimage_le _ _ _ (hVQ.trans (Z_normalized R _)))

/-- Conjugating the edge center gives elements of the literal local fixed Z-layer. -/
theorem localConjugate_edgeZ_le_localFlagZ (source : LocalSource L R)
    (i : Bool) (hkernel : flagKernel source i = Q R (beta R)) (g : M) :
    localConjugate (Z R (beta R)) g ≤ localFlagZ source i g := by
  have hg : embedM R g ∈ stabilizer R (alpha R) := by
    rw [alpha, stabilizer_m_base]
    exact ⟨g, rfl⟩
  apply le_inf
  · exact (map_mono (edge_Z_le (alpha R) (beta R) rfl (base_adjacent R))).trans_eq
      (mem_normalizer_iff_map_conj_eq.mp (Z_normalized R (alpha R) hg))
  · unfold localFlagKernel
    rw [hkernel]
    have hc : Z R (beta R) ≤ centralizer (Q R (beta R) : Set (FreeAmalgam R)) := by
      rw [Z, if_neg (show color R (beta R) ≠ false by change true ≠ false; decide)]
      intro x hx
      exact (mem_omegaCenter_iff.mp hx).2.2
    exact (map_mono hc).trans (map_centralizer_le_centralizer_image _ _)


/-- Each actual conjugate layer displaces its own core into its local fixed layer. -/
theorem firstFlagLayer_commutator_le_localFlagZ (source : LocalSource L R)
    (geometry : Geometry R) (common : CommonFacts R source geometry)
    (early : EarlyFacts R geometry) (i : Bool)
    (hkernel : flagKernel source i = Q R (beta R)) (g : M) :
    ⁅firstFlagLayer (R := R) g, localFlagKernel source i g⁆ ≤ localFlagZ source i g := by
  change ⁅(V R (beta R)).map _, (flagKernel source i).map _⁆ ≤ _
  rw [hkernel, ← map_commutator]
  exact (map_mono (edgeRadius_commutator_le_edgeZ geometry common.large_distance early)).trans
    (localConjugate_edgeZ_le_localFlagZ source i hkernel g)

variable [Finite M]

/-- Every local parabolic core contains the original vertex two-core,
including after a change of coset representative. -/
theorem Q_alpha_le_localFlagKernel (source : LocalSource L R) (i : Bool) (g : M) :
    Q R (alpha R) ≤ localFlagKernel source i g := by
  have hbase : Q R (alpha R) ≤ flagKernel source i := by
    rw [Q_alpha R source.two_group source.core_le]
    apply map_mono
    change pCore 2 M ≤ (parabolic source.projection source.flag i).pCoreIn 2
    rw [Incident.parabolic_core_eq_comap source i, ← source.projection_kernel]
    intro x hx
    change source.projection x ∈ (modelParabolic source.flag i).pCoreIn 2
    rw [show source.projection x = 1 from hx]
    exact one_mem _
  have hg : embedM R g ∈ stabilizer R (alpha R) := by
    rw [alpha, stabilizer_m_base]
    exact ⟨g, rfl⟩
  have he : localConjugate (Q R (alpha R)) g = Q R (alpha R) :=
    mem_normalizer_iff_map_conj_eq.mp (Q_normalized R (alpha R) hg)
  exact he.symm.le.trans (map_mono hbase)

/-- Strict displacement by a subgroup of the edge kernel exhausts its order-four
quotient at the midpoint. -/
theorem FlagCriticalData.sup_middle_kernel_of_displacement
    {source : LocalSource L R} {geometry : Geometry R} {i : Bool}
    (p : FlagCriticalData source geometry i) (early : EarlyFacts R geometry)
    (H : Subgroup (FreeAmalgam R)) (hH : H ≤ Q R (beta R))
    (hindex : 2 < (Q R p.middle).relIndex H) : H ⊔ Q R p.middle = Q R (beta R) := by
  have hK : Q R p.middle ≤ Q R (beta R) :=
    Q_le_adjacent_h R rfl (adjacent_symm R p.middle_neighbor)
  let A := H.subgroupOf (Q R (beta R))
  let K := (Q R p.middle).subgroupOf (Q R (beta R))
  let : K.Normal := normal_subgroupOf_of_le_normalizer
    ((show Q R (beta R) ≤ stabilizer R p.middle from fun _ hx => hx.2 _ p.middle_neighbor).trans
      (Q_normalized R p.middle))
  have hKi : K.index = 4 :=
    early.edge_Q_index p.middle (beta R) p.middle_color (adjacent_symm R p.middle_neighbor)
  have hi : K.relIndex A = 4 := by
    have hd : K.relIndex A ∣ 4 := hKi ▸ K.relIndex_dvd_index_of_normal A
    have hn : K.relIndex A ∈ Nat.divisors 4 := Nat.mem_divisors.mpr ⟨hd, by decide⟩
    have hgt : 2 < K.relIndex A := by rwa [relIndex_subgroupOf hH]
    have hdiv : Nat.divisors 4 = {1, 2, 4} := by decide
    rw [hdiv] at hn
    simp only [Finset.mem_insert, Finset.mem_singleton] at hn
    omega
  have hm := relIndex_mul_index (show K ≤ A ⊔ K from le_sup_right)
  rw [relIndex_sup_right, hi, hKi] at hm
  have he : A ⊔ K = ⊤ := index_eq_one.mp (by omega)
  have hh := congrArg (Subgroup.map (Q R (beta R)).subtype) he
  dsimp only [A, K] at hh
  simpa only [Subgroup.map_sup, map_subgroupOf_eq_of_le hH,
    map_subgroupOf_eq_of_le hK, ← MonoidHom.range_eq_map, range_subtype] using hh

/-- A strict layer displacement identifies its commutator with the full edge
commutator, using the actual conjugate layer and the midpoint action kernel. -/
theorem FlagCriticalData.commutator_firstFlagLayer_eq_edge
    {source : LocalSource L R} {geometry : Geometry R} {i : Bool}
    (p : FlagCriticalData source geometry i) (early : EarlyFacts R geometry)
    (hlarge : 2 < geometry.b R) (g : M)
    (hindex : 2 < (Q R p.middle).relIndex (firstFlagLayer (R := R) g)) :
    ⁅Z R p.middle, firstFlagLayer (R := R) g⁆ = ⁅Z R p.middle, Q R (beta R)⁆ := by
  have hH : firstFlagLayer (R := R) g ≤ Q R (beta R) :=
    (firstFlagLayer_le_radius g).trans ((V_le_Q geometry hlarge _ rfl).trans
      (Q_le_adjacent_h R rfl (base_adjacent R)))
  exact commutator_eq_of_centralizing_sup
    ((sup_comm _ _).trans (p.sup_middle_kernel_of_displacement early _ hH hindex))
    (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp
      (geometry.centralizes p.middle p.middle_color)))
    (hH.trans ((show Q R (beta R) ≤ stabilizer R p.middle from
      fun _ hx => hx.2 _ p.middle_neighbor).trans (Z_normalized R p.middle)))

/-- The full midpoint edge commutator is fixed by any first-color core whose
conjugate layer has strict displacement. -/
theorem FlagCriticalData.edge_commutator_le_localFlagZ
    {source : LocalSource L R} {geometry : Geometry R} {i : Bool}
    (p : FlagCriticalData source geometry i) (common : CommonFacts R source geometry)
    (early : EarlyFacts R geometry) (hkernel : flagKernel source i = Q R (beta R))
    (g : M) (hindex : 2 < (Q R p.middle).relIndex (firstFlagLayer (R := R) g)) :
    ⁅Z R p.middle, Q R (beta R)⁆ ≤ localFlagZ source i g := by
  rw [← p.commutator_firstFlagLayer_eq_edge early common.large_distance g hindex,
    commutator_comm]
  have hm : Z R p.middle ≤ Q R (alpha R) := by
    have h := p.middle_le_firstLayer
    rw [firstFlagLayer, localConjugate_one] at h
    exact h.trans (edgeRadius_le_Q_alpha geometry common.large_distance)
  exact (commutator_mono le_rfl (hm.trans (Q_alpha_le_localFlagKernel source i g))).trans
    (firstFlagLayer_commutator_le_localFlagZ source geometry common early i hkernel g)

/-- The finite local-geometry input still required by the p.905 symmetry
argument. The first clause is the order-two intersection of incident cores
modulo Q_alpha. The second separates two distinct pencils by their actual
first-color fixed subgroups. No constructor is asserted here. -/
structure FlagP905PencilFacts (source : LocalSource L R) (i : Bool) : Prop where
  intersection_index : ∀ d : M, flagIncident source i 1 d →
    (Q R (alpha R)).relIndex
      (flagKernel source i ⊓ localFlagKernel source (!i) d) ≤ 2
  separate : ∀ d d' : M, flagIncident source i 1 d → flagIncident source i 1 d' →
    flagKernel source i ⊓ localFlagKernel source (!i) d ≠
      flagKernel source i ⊓ localFlagKernel source (!i) d' →
    ∃ g g' : M, flagIncident source i g d ∧ flagIncident source i g' d' ∧
      localFlagZ source i g ≠ localFlagZ source i 1 ∧
      localFlagZ source i g' ≠ localFlagZ source i 1 ∧
      localFlagZ source i g' ⊓ localFlagZ source i g ⊓ Z R (beta R) ≤
        (center (stabilizer R (alpha R))).map (stabilizer R (alpha R)).subtype

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Flags.RankOne
