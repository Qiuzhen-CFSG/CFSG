module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Flags.RankOne.Triple.Natural.GeometryBound.Incidence
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Early.EdgeAction
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.SectionThree.CriticalModules.LocalStructure
public import Theory.GroupTheory.ElementaryEightPairing
public import Theory.GroupTheory.Commutator.NormalizedIndexTwo

/-!
# Local calculations for the two displacement cases on p.905

The earlier edge index two makes the whole edge kernel act trivially on
the barred edge layer. Conjugation gives this for every first-color layer,
so adjoining its own kernel to an actor does not change its fixed preimage.
The supplied natural three-space and central decomposition reduce the
critical commutator to the pairing of two elementary groups of order eight;
its order is two, excluding the order-four case in this binary specialization.

If a first layer escapes the midpoint kernel, its centralizer in the midpoint
Z-layer is exactly Z_beta. Thus, when the endpoint normalizes that first
layer, the intersection with the midpoint kernel centralizes the endpoint
modulo Z_alpha. This bounds the endpoint--kernel fixed index by the actual
displacement index. The required endpoint placement and the contained-layer
case are not assumed or proved here. In the reverse direction, critical
escape reduces the midpoint radius image to the alternatives two and four;
excluding two remains part of the source displacement argument.

Source: Meierfrankenfeld--Stellmacher, *Pushing up weak BN-pairs of rank two*
(1993), proof of (4.6.8), claim (1), printed p.905, using (4.6.3)--(4.6.7).
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Flags.RankOne
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}

/-- Every first-color layer remains inside the distinguished edge kernel. -/
theorem firstFlagLayer_le_edgeKernel (geometry : Geometry R)
    (hlarge : 2 < geometry.b R) (g : M) :
    firstFlagLayer (R := R) g ≤ Q R (beta R) :=
  (firstFlagLayer_le_radius g).trans ((V_le_Q geometry hlarge _ rfl).trans
    (Q_le_adjacent_h R (show color R (beta R) = true from rfl) (base_adjacent R)))

/-- The index-two fixed layer at each neighbor bounds the commutator
of the entire edge layer with its kernel. -/
theorem edgeRadius_kernel_commutator_le (source : LocalSource L R) (geometry : Geometry R)
    (common : CommonFacts R source geometry) (early : EarlyFacts R geometry) :
    ⁅V R (beta R), Q R (beta R)⁆ ≤ Z R (beta R) := by
  have hWN : firstFlagLayer (R := R) 1 ≤ normalizer (Z R (beta R)) :=
    (firstFlagLayer_le_edgeKernel geometry common.large_distance 1).trans
      ((show Q R (beta R) ≤ stabilizer R (beta R) from fun _ hx => hx.1).trans
        (Z_normalized R _))
  simp only [firstFlagLayer, localConjugate_one] at hWN
  have hV : V R (beta R) ≤ commutatorPreimage (V R (beta R))
      (Q R (beta R)) (Z R (beta R)) := by
    rw [V_eq_neighborSpan (alpha R) (beta R) rfl (base_adjacent R)]
    apply iSup_le
    intro c
    apply iSup_le
    intro hc
    have hcol : color R c = false := by
      have hh := adjacent_color_ne R hc
      have hb : color R (beta R) = true := rfl
      cases h : color R c <;> simp_all
    have hcb := adjacent_symm R hc
    have hcV : Z R c ≤ neighborSpan (R := R) (beta R) := by
      apply le_iSup_of_le c
      exact le_iSup_of_le hc le_rfl
    apply le_commutatorPreimage hcV
    apply commutator_le_of_normalized_index_two (Z R c) (Z R (beta R)) (Q R (beta R))
      (Early.edge_Z_le c _ hcol hcb) (early.edge_Z_index c _ hcol hcb)
    · exact (show Q R (beta R) ≤ stabilizer R c from fun _ hx => hx.2 c hc).trans
        (Z_normalized R c)
    · exact (show Q R (beta R) ≤ stabilizer R (beta R) from fun _ hx => hx.1).trans
        (Z_normalized R _)
  exact (commutator_mono hV le_rfl).trans
    (commutator_commutatorPreimage_le _ _ _ hWN)

/-- The actual local kernel acts trivially on its barred first-color layer. -/
theorem localFlagKernel_centralizes_bar (source : LocalSource L R) (geometry : Geometry R)
    (common : CommonFacts R source geometry) (early : EarlyFacts R geometry)
    (i : Bool) (hkernel : flagKernel source i = Q R (beta R)) (g : M) :
    ⁅firstFlagLayer (R := R) g, localFlagKernel source i g⁆ ≤ Z R (alpha R) := by
  have h := map_mono (f := (MulAut.conj (embedM R g)).toMonoidHom)
    ((edgeRadius_kernel_commutator_le source geometry common early).trans
      (Early.edge_Z_le (alpha R) (beta R) rfl (base_adjacent R)))
  rw [map_commutator] at h
  have hg : embedM R g ∈ stabilizer R (alpha R) := by
    rw [alpha, stabilizer_m_base]
    exact ⟨g, rfl⟩
  have hz : (Z R (alpha R)).map (MulAut.conj (embedM R g)).toMonoidHom =
      Z R (alpha R) := mem_normalizer_iff_map_conj_eq.mp (Z_normalized R (alpha R) hg)
  rw [hz] at h
  simpa only [firstFlagLayer, localFlagKernel, localConjugate, hkernel] using h

/-- Adding the actual parabolic kernel does not change fixed preimages on
the barred first layer. The other actor need only normalize the denominator. -/
theorem localFlagFixedPreimage_join_kernel (source : LocalSource L R) (geometry : Geometry R)
    (common : CommonFacts R source geometry) (early : EarlyFacts R geometry)
    (i : Bool) (hkernel : flagKernel source i = Q R (beta R)) (g : M)
    (A : Subgroup (FreeAmalgam R)) (hAN : A ≤ normalizer (Z R (alpha R))) :
    commutatorPreimage (firstFlagLayer (R := R) g)
      (A ⊔ localFlagKernel source i g) (Z R (alpha R)) =
        commutatorPreimage (firstFlagLayer (R := R) g) A (Z R (alpha R)) := by
  let W := firstFlagLayer (R := R) g
  let N := Z R (alpha R)
  let T := A ⊔ localFlagKernel source i g
  have hWN : W ≤ normalizer N := (firstFlagLayer_le_radius g).trans
    ((geometry.V_local _ rfl common.large_distance).trans (Z_normalized R _))
  have hTN : T ≤ normalizer N := sup_le hAN
    ((localFlagKernel_le_stabilizer source i g).trans (Z_normalized R _))
  apply le_antisymm
  · exact le_commutatorPreimage (commutatorPreimage_le W T N)
      ((commutator_mono le_rfl le_sup_left).trans
        (commutator_commutatorPreimage_le W T N hWN))
  · let D := commutatorPreimage W A N
    have hTD : T ≤ commutatorPreimage T D N := by
      apply sup_le
      · apply le_commutatorPreimage le_sup_left
        rw [commutator_comm]
        exact commutator_commutatorPreimage_le W A N hWN
      · apply le_commutatorPreimage le_sup_right
        rw [commutator_comm]
        exact (commutator_mono (commutatorPreimage_le W A N) le_rfl).trans
          (localFlagKernel_centralizes_bar source geometry common early i hkernel g)
    apply le_commutatorPreimage (commutatorPreimage_le W A N)
    rw [commutator_comm]
    exact (commutator_mono hTD le_rfl).trans
      (commutator_commutatorPreimage_le T D N hTN)

namespace FlagCriticalData
variable {source : LocalSource L R} {geometry : Geometry R} {i : Bool}

/-- In the binary natural three-space specialization the critical commutator
has order two. In particular the source order-four alternative cannot occur. -/
theorem critical_commutator_card_two (p : FlagCriticalData source geometry i)
    (common : CommonFacts R source geometry) :
    Nat.card (⁅Z R (alpha R), Z R p.endpoint⁆ : Subgroup (FreeAmalgam R)) = 2 := by
  let s : BinaryNaturalStructure source :=
    ⟨common.X_eq_Z, common.natural, common.decomposition, common.disjoint⟩
  rw [s.critical_commutator_eq geometry (alpha R) rfl p.endpoint p.critical]
  let : Finite (U R (alpha R)) := Nat.finite_of_card_ne_zero (by
    rw [common.natural.card_at _ rfl]; decide)
  let : Finite (U R p.endpoint) := Nat.finite_of_card_ne_zero (by
    rw [common.natural.card_at _ p.endpoint_color]; decide)
  let := geometry.U_elementary (lt_trans (by decide) common.large_distance) (alpha R) rfl
  let := geometry.U_elementary (lt_trans (by decide) common.large_distance) p.endpoint p.endpoint_color
  obtain ⟨hn, hn'⟩ := source.critical_U_mutually_normalize geometry (alpha R) rfl p.endpoint p.critical
  exact card_commutator_eq_two_of_elementary_eight _ _
    (common.natural.card_at _ rfl) (common.natural.card_at _ p.endpoint_color) hn hn'
    (s.critical_U_noncommutation geometry (alpha R) rfl p.endpoint p.critical)

/-- Escaping the midpoint kernel makes the centralizer in Z_middle exactly
the edge fixed layer. This uses the earlier index two, not naturality of U_delta. -/
theorem middle_centralizer_firstFlagLayer (p : FlagCriticalData source geometry i)
    (common : CommonFacts R source geometry) (early : EarlyFacts R geometry)
    (g : M) (hnot : ¬ firstFlagLayer (R := R) g ≤ Q R p.middle) :
    Z R p.middle ⊓ centralizer (firstFlagLayer (R := R) g : Set (FreeAmalgam R)) =
      Z R (beta R) := by
  let W := firstFlagLayer (R := R) g
  let C := Z R p.middle ⊓ centralizer (W : Set (FreeAmalgam R))
  have hWQ : W ≤ Q R (beta R) := firstFlagLayer_le_edgeKernel geometry common.large_distance g
  have hBC : Z R (beta R) ≤ C := by
    rw [Early.edge_Z_eq_fixed common p.middle _ p.middle_color
      (adjacent_symm R p.middle_neighbor)]
    exact inf_le_inf_left _ (centralizer_le hWQ)
  let := finite_stabilizer R p.middle
  let : Finite (Z R p.middle) := Finite.of_injective (inclusion (Z_le_stabilizer R _))
    (inclusion_injective _)
  let : Finite C := Finite.of_injective (inclusion (show C ≤ Z R p.middle from inf_le_left))
    (inclusion_injective _)
  have hne : C.relIndex (Z R p.middle) ≠ 1 := by
    intro hc
    have hz : Z R p.middle ≤ centralizer (W : Set (FreeAmalgam R)) :=
      (relIndex_eq_one.mp hc).trans inf_le_right
    apply hnot
    rw [← common.centralizer p.middle (beta R) p.middle_color
      (adjacent_symm R p.middle_neighbor)]
    exact le_inf hWQ (le_centralizer_iff.mp hz)
  have hi : (Z R (beta R)).relIndex (Z R p.middle) = 2 :=
    early.edge_Z_index _ _ p.middle_color (adjacent_symm R p.middle_neighbor)
  have hm := relIndex_mul_relIndex (Z R (beta R)) C (Z R p.middle) hBC inf_le_left
  rw [hi] at hm
  have hcpos : 0 < C.relIndex (Z R p.middle) := Nat.pos_of_ne_zero index_ne_zero_of_finite
  have hbpos : 0 < (Z R (beta R)).relIndex C := Nat.pos_of_ne_zero index_ne_zero_of_finite
  have hc2 : 2 ≤ C.relIndex (Z R p.middle) := by omega
  have hc : (Z R (beta R)).relIndex C = 1 := by nlinarith
  exact le_antisymm (relIndex_eq_one.mp hc) hBC

/-- The small-displacement intersection commutator is already in Z_alpha
once the endpoint normalizes the first layer and that layer escapes Q_middle. -/
theorem firstLayer_intersection_endpoint_commutator_le_Z
    (p : FlagCriticalData source geometry i) (common : CommonFacts R source geometry)
    (early : EarlyFacts R geometry) (g : M)
    (hnot : ¬ firstFlagLayer (R := R) g ≤ Q R p.middle)
    (hn : Z R p.endpoint ≤ normalizer (firstFlagLayer (R := R) g)) :
    ⁅firstFlagLayer (R := R) g ⊓ Q R p.middle, Z R p.endpoint⁆ ≤ Z R (alpha R) := by
  have hEU : Z R p.endpoint ≤ V R p.middle :=
    le_iSup_of_le p.endpoint (le_iSup_of_le (show (cosetGraph R).dist p.endpoint p.middle ≤ 2 by
      rw [SimpleGraph.dist_comm]; exact p.second_distance.le) le_rfl)
  have hcW : ⁅firstFlagLayer (R := R) g ⊓ Q R p.middle, Z R p.endpoint⁆ ≤
      firstFlagLayer (R := R) g :=
    (commutator_mono inf_le_left le_rfl).trans (le_normalizer_iff_commutator_le_left.mp hn)
  have hcZ : ⁅firstFlagLayer (R := R) g ⊓ Q R p.middle, Z R p.endpoint⁆ ≤ Z R p.middle := by
    rw [commutator_comm]
    exact (commutator_mono hEU inf_le_right).trans (early.commutator_le_Z _ p.middle_color)
  let := edgeRadius_abelian geometry common.large_distance (alpha R) (beta R) rfl (base_adjacent R)
  let : IsMulCommutative (firstFlagLayer (R := R) g) :=
    inferInstanceAs (IsMulCommutative ((V R (beta R)).map
      (MulAut.conj (embedM R g)).toMonoidHom))
  have hc := le_inf hcZ (hcW.trans (le_centralizer (firstFlagLayer (R := R) g)))
  rw [p.middle_centralizer_firstFlagLayer common early g hnot] at hc
  exact hc.trans (Early.edge_Z_le (alpha R) (beta R) rfl (base_adjacent R))


/-- The centralizer estimate for the source endpoint--kernel join is no larger
than the displacement index once the first layer escapes the midpoint kernel. -/
theorem firstLayer_fixedIndex_le_displacement
    (p : FlagCriticalData source geometry i) (common : CommonFacts R source geometry)
    (early : EarlyFacts R geometry)
    (hkernel : flagKernel source i = Q R (beta R)) (g : M)
    (hnot : ¬ firstFlagLayer (R := R) g ≤ Q R p.middle)
    (hn : Z R p.endpoint ≤ normalizer (firstFlagLayer (R := R) g)) :
    (commutatorPreimage (firstFlagLayer (R := R) g)
      (Z R p.endpoint ⊔ localFlagKernel source i g) (Z R (alpha R))).relIndex
        (firstFlagLayer (R := R) g) ≤
          (Q R p.middle).relIndex (firstFlagLayer (R := R) g) := by
  let W := firstFlagLayer (R := R) g
  let T := Z R p.endpoint ⊔ localFlagKernel source i g
  let D := W ⊓ Q R p.middle
  have hA : ⁅D,Z R p.endpoint⁆ ≤ Z R (alpha R) :=
    p.firstLayer_intersection_endpoint_commutator_le_Z common early g hnot hn
  have hK : ⁅D,localFlagKernel source i g⁆ ≤ Z R (alpha R) :=
    (commutator_mono inf_le_left le_rfl).trans
      (localFlagKernel_centralizes_bar source geometry common early i hkernel g)
  have hEP : Z R p.endpoint ≤ stabilizer R (alpha R) :=
    (source.critical_Z_le_stabilizer geometry (alpha R) rfl p.endpoint p.critical).2
  have hTP : T ≤ stabilizer R (alpha R) :=
    sup_le hEP (localFlagKernel_le_stabilizer source i g)
  have hTN : T ≤ normalizer (Z R (alpha R)) := hTP.trans (Z_normalized R _)
  have hTD : T ≤ commutatorPreimage T D (Z R (alpha R)) := by
    apply sup_le
    · exact le_commutatorPreimage le_sup_left (by rwa [commutator_comm])
    · exact le_commutatorPreimage le_sup_right (by rwa [commutator_comm])
  have hD : D ≤ commutatorPreimage W T (Z R (alpha R)) := by
    apply le_commutatorPreimage inf_le_left
    rw [commutator_comm]
    exact (commutator_mono hTD le_rfl).trans
      (commutator_commutatorPreimage_le _ _ _ hTN)
  let := finite_stabilizer R (alpha R)
  let : Finite W := Finite.of_injective (inclusion ((firstFlagLayer_le_radius g).trans
    (geometry.V_local _ rfl common.large_distance))) (inclusion_injective _)
  have h := relIndex_le_of_le_left hD (show D.relIndex W ≠ 0 from index_ne_zero_of_finite)
  simpa only [D, inf_relIndex_left] using h

omit [Finite M] in
/-- The bad midpoint already forces the reverse radius to leave Q_alpha.
The strict index greater than two is the remaining reverse displacement step. -/
theorem middle_radius_not_le_Q_alpha (p : FlagCriticalData source geometry i)
    (common : CommonFacts R source geometry) (hb : geometry.b R = 4) :
    ¬ V R p.middle ≤ Q R (alpha R) := by
  have hK : flagResidual source i ≤ normalizer (V R (alpha R)) :=
    ((flagResidual_le source i).trans (flagParabolic_le source i)).trans
      (DistanceEight.V_normalized R _)
  have hescape : ¬ V R (alpha R) ≤ Q R p.middle := by
    intro h
    apply p.middle_triple
    have hz : ⁅Z R p.middle, V R (alpha R)⁆ = ⊥ :=
      bot_unique ((commutator_mono le_rfl h).trans (geometry.centralizes _ p.middle_color).le)
    have ht : ⁅⁅Z R p.middle, flagResidual source i⁆, V R (alpha R)⁆ = ⊥ := by
      apply commutator_eq_bot_iff_le_centralizer.mpr
      exact (commutator_mono (commutator_eq_bot_iff_le_centralizer.mp hz) le_rfl).trans
        (le_normalizer_iff_commutator_le_left.mp
          (hK.trans (normalizer_le_normalizer_centralizer _)))
    rw [ht]
    exact bot_le
  have hforward : (cosetGraph R).dist (alpha R) p.middle + 2 = geometry.b R := by
    rw [p.first_distance, hb]
  obtain ⟨d, hdcol, hda, hdcrit⟩ :=
    DistanceEight.PathCentrality.exists_critical_shift R rfl hforward hescape
  have hreverse := common.critical_reverse d hdcol p.middle p.middle_color hdcrit
  apply common.escape p.middle p.middle_color d hreverse (alpha R)
  · rw [SimpleGraph.dist_comm]
    exact hda
  · rw [SimpleGraph.dist_comm (u := p.middle), p.first_distance, hreverse.1,
      geometry.distance_constant _ p.middle_color]
    exact hb.symm

/-- Before the strict reverse estimate, the exact remaining alternatives
for the radius image are two and four. -/
theorem middle_radius_index_two_or_four (p : FlagCriticalData source geometry i)
    (common : CommonFacts R source geometry) (hb : geometry.b R = 4)
    (early : EarlyFacts R geometry) :
    (Q R (alpha R)).relIndex (V R p.middle) = 2 ∨
      (Q R (alpha R)).relIndex (V R p.middle) = 4 := by
  have hVQ : V R p.middle ≤ Q R (beta R) :=
    (V_le_Q geometry common.large_distance _ p.middle_color).trans
      (Q_le_adjacent_h R (show color R (beta R) = true from rfl)
        (adjacent_symm R p.middle_neighbor))
  let : ((Q R (alpha R)).subgroupOf (Q R (beta R))).Normal :=
    normal_subgroupOf_of_le_normalizer
      ((show Q R (beta R) ≤ stabilizer R (alpha R) from
        fun _ hx => hx.2 _ (adjacent_symm R (base_adjacent R))).trans (Q_normalized R _))
  have hd := relIndex_dvd_index_of_normal
    ((Q R (alpha R)).subgroupOf (Q R (beta R)))
    ((V R p.middle).subgroupOf (Q R (beta R)))
  rw [relIndex_subgroupOf hVQ] at hd
  change (Q R (alpha R)).relIndex (V R p.middle) ∣
    (Q R (alpha R)).relIndex (Q R (beta R)) at hd
  rw [early.edge_Q_index (alpha R) (beta R) rfl (base_adjacent R)] at hd
  have hne : (Q R (alpha R)).relIndex (V R p.middle) ≠ 1 :=
    fun he => p.middle_radius_not_le_Q_alpha common hb (relIndex_eq_one.mp he)
  have hf := Nat.mem_divisors.mpr ⟨hd, (by decide : 4 ≠ 0)⟩
  rw [show Nat.divisors 4 = ({1,2,4} : Finset ℕ) by decide] at hf
  simp only [Finset.mem_insert, Finset.mem_singleton] at hf
  omega

end FlagCriticalData
end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Flags.RankOne
