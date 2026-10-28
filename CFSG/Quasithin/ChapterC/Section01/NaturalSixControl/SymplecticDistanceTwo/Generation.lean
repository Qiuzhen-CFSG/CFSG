module
public import CFSG.Quasithin.ChapterC.Section01.NaturalSixControl.SymplecticSetup.Source
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.SectionThree.DistanceTwo.NaturalCore.LocalGeometry
public import Theory.GroupTheory.PResidual.SubnormalCoreAction
public import Theory.GroupTheory.PResidual.PerfectCover
public import Theory.GroupTheory.PResidual.PrimeSection
public import Theory.GroupTheory.InvolutionGeneratedCommutator.Generation
public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple

/-!
# Normal and involution generation for native symplectic distance two

The marked image is A₆ or S₆. Every normal subgroup escaping the two-core
therefore contains A₆ in its image, by simplicity in the first case and
the normal-subgroup theorem for symmetric groups in the second. The
component is two-perfect, so its containment lifts through the two-core.

At critical distance two, reversal makes the endpoint layer escape the
first vertex kernel. Its normal closure consequently contains the residual.
The commutator of that layer with the core has exponent two, and residual
commutator idempotence then gives involution generation of the whole core.
The edge-centralizer condition is the exact earlier recognition input; no
SL₃ quotient or module classifier is used.

Source: Meierfrankenfeld--Stellmacher (1993), (2.2)(iii), (3.6), and the
symplectic analysis in Section 7; printed pp.856,870,932--933.
-/

@[expose] public section
open Subgroup Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
namespace CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup.Source
variable {M : Type*} [Group M] [Finite M] {L R W : Subgroup M} [L.Normal] [W.Normal]
  (s : Source L R W)
include s

/-- Covering the even image forces a normal subgroup to contain the component. -/
theorem residual_le_of_image_contains_alternating (N : Subgroup M) [N.Normal]
    (hN : alternatingGroup (Fin 6) ≤ N.map s.projection) : L ≤ N := by
  apply le_normal_of_isPPerfect_of_le_sup_pGroup L N (pCore 2 M)
    s.component_twoPerfect pCore_isPGroup
  rw [← s.projection_kernel, ← comap_map_eq]
  exact (map_le_iff_le_comap).mp (s.component_image ▸ hN)

omit [Finite M] in
/-- Every normal subgroup escaping the kernel contains the even image. -/
theorem image_contains_alternating_of_not_le_core (N : Subgroup M) [N.Normal]
    (hN : ¬ N ≤ pCore 2 M) : alternatingGroup (Fin 6) ≤ N.map s.projection := by
  have hnon : N.map s.projection ≠ ⊥ := by
    intro h
    exact hN (s.projection_kernel ▸ (Subgroup.map_eq_bot_iff _).mp h)
  have hnorm : s.projection.range ≤ normalizer (N.map s.projection : Set _) := by
    simpa only [normalizer_eq_top, map_top, MonoidHom.range_eq_map] using
      (le_normalizer_map s.projection (H := N))
  have hd : s.projection.range.index ∣ 2 :=
    (alternatingGroup.index_eq_two (α := Fin 6)) ▸ index_dvd_of_le s.image_contains_alternating
  rcases (Nat.dvd_prime Nat.prime_two).mp hd with h1 | h2
  · have ht := index_eq_one.mp h1
    have := (normalizer_eq_top_iff).mp (top_le_iff.mp (ht ▸ hnorm))
    exact Equiv.Perm.alternatingGroup_le_of_normal (by simp)
      ((nontrivial_iff_ne_bot _).mpr hnon)
  · have he := Equiv.Perm.eq_alternatingGroup_of_index_eq_two h2
    have hle : N.map s.projection ≤ alternatingGroup (Fin 6) := by
      rw [← he]
      exact map_le_range s.projection N
    have hn : ((N.map s.projection).subgroupOf (alternatingGroup (Fin 6))).Normal :=
      (normal_subgroupOf_iff_le_normalizer hle).mpr (he ▸ hnorm)
    let := hn
    rcases alternatingGroup.normal_subgroup_eq_bot_or_eq_top (by simp : 5 ≤ Nat.card (Fin 6))
      (N := (N.map s.projection).subgroupOf (alternatingGroup (Fin 6))) with hb | ht
    · have hm := congrArg (fun H : Subgroup (alternatingGroup (Fin 6)) =>
        H.map (alternatingGroup (Fin 6)).subtype) hb
      rw [map_subgroupOf_eq_of_le hle, Subgroup.map_bot] at hm
      exact (hnon hm).elim
    · exact subgroupOf_eq_top.mp ht

theorem residual_le_of_not_le_core (N : Subgroup M) [N.Normal]
    (hN : ¬ N ≤ pCore 2 M) : L ≤ N :=
  s.residual_le_of_image_contains_alternating N (s.image_contains_alternating_of_not_le_core N hN)

theorem residual_le_normalClosure (A : Subgroup M) (hA : ¬ A ≤ pCore 2 M) :
    pResidual 2 M ≤ normalClosure (A : Set M) := by
  rw [s.residual]
  exact s.residual_le_of_not_le_core _ (fun h => hA (le_normalClosure.trans h))

open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceTwo.NaturalCore

/-- Reversal makes the endpoint layer normally generate the actual residual. -/
theorem critical_residual_le_normalClosure (geometry : Geometry R)
    (hb : geometry.b R = 2) {a' : Vertex R}
    (hc : CriticalPair R (alpha R) a' (geometry.exists_critical (alpha R) rfl))
    (hreverse : ¬ Z R a' ≤ Q R (alpha R)) :
    pResidual 2 M ≤ normalClosure (((Z R a').comap (embedM R) : Subgroup M) : Set M) := by
  have ha' := critical_endpoint_color R (alpha R) rfl _ hc
  have hZ : Z R a' ≤ (embedM R).range := by
    change Z R a' ≤ Mbar R
    rw [← stabilizer_m_base]
    apply Z_le_stabilizer_of_dist_two R geometry a' ha'
    · rw [geometry.distance_constant a' ha']
      change 0 < geometry.b R
      omega
    · rw [SimpleGraph.dist_comm]
      exact hc.1.trans hb
  apply s.residual_le_normalClosure
  intro h
  apply hreverse
  rw [← show ((Z R a').comap (embedM R)).map (embedM R) = Z R a' from
    (map_comap_eq _ _).trans (inf_eq_right.mpr hZ), Q_alpha R s.two_group s.core_le]
  exact map_mono h

/-- At distance two the native symplectic core is generated by involutions. -/
theorem involution_generation (geometry : Geometry R) (hb : geometry.b R = 2)
    (hC : EdgeCentralizerCondition R) :
    closure {x : core R (alpha R) | x ^ 2 = 1} = ⊤ := by
  obtain ⟨a', t, hc, hat, ha't⟩ := critical_edge_exists geometry hb
  have ha' := critical_endpoint_color R (alpha R) rfl _ hc
  have hreverse := CFSG.Quasithin.ChapterC.BinaryMS.MS93.critical_reverse
    R geometry hC (alpha R) rfl (by change 0 < geometry.b R; omega) a' ha' hc
  have hZ : Z R a' ≤ (embedM R).range := by
    change Z R a' ≤ Mbar R
    rw [← stabilizer_m_base]
    apply Z_le_stabilizer_of_dist_two R geometry a' ha'
    · rw [geometry.distance_constant a' ha']
      change 0 < geometry.b R
      omega
    · rw [SimpleGraph.dist_comm]
      exact hc.1.trans hb
  let A := (Z R a').comap (embedM R)
  have hAm : A.map (embedM R) = Z R a' :=
    (map_comap_eq _ _).trans (inf_eq_right.mpr hZ)
  let K := ⁅pCore 2 M, pResidual 2 M⁆
  have hKm : K.map (embedM R) = core R (alpha R) :=
    (core_alpha R s.two_group s.core_le rfl).symm
  have hLN : pResidual 2 M ≤ normalClosure (A : Set M) :=
    s.critical_residual_le_normalClosure geometry hb hc hreverse.2
  have hfull : ⁅K, pResidual 2 M⁆ = K :=
    commutator_isPPerfect_idempotent (pResidual 2 M) (pCore 2 M)
      (isPPerfect_pResidual 2) pCore_isPGroup le_normalizer_of_normal
  have hpow (x : M) (hx : x ∈ ⁅K, A⁆) : x ^ 2 = 1 := by
    have hx' : embedM R x ∈ ⁅core R (alpha R), Z R a'⁆ := by
      rw [← hKm, ← hAm, ← map_commutator]
      exact mem_map_of_mem _ hx
    have hx'' := commutator_mono (DistanceTwo.core_le_Q (alpha R)) le_rfl hx'
    have hp := local_commutator_pow_two geometry hb hc hat ha't hx''
    apply embedM_injective R
    simpa only [map_pow, map_one] using hp
  have hgen := closure_involutions_eq_top_of_commutator_generation
    K A (pResidual 2 M) hLN hfull hpow
  let e : K ≃* core R (alpha R) :=
    (K.equivMapOfInjective (embedM R) (embedM_injective R)).trans
      (MulEquiv.subgroupCongr hKm)
  apply top_unique
  intro x hx
  clear hx
  obtain ⟨y, rfl⟩ := e.surjective x
  have hy : y ∈ closure {x : K | x ^ 2 = 1} := hgen.symm ▸ mem_top y
  induction hy using closure_induction with
  | mem z hz =>
    apply Subgroup.subset_closure
    change (e z) ^ 2 = 1
    rw [← map_pow, hz, map_one]
  | one =>
    simpa only [map_one] using (closure {x : core R (alpha R) | x ^ 2 = 1}).one_mem
  | mul y z _ _ hy hz => simpa only [map_mul] using Subgroup.mul_mem _ hy hz
  | inv y _ hy => simpa only [map_inv] using Subgroup.inv_mem _ hy

/-- The actual native holomorph geometry supplies the distance-two consumer. -/
theorem distance_two_involution_generation (hb : s.geometry.b R = 2)
    (hC : EdgeCentralizerCondition R) :
    closure {x : core R (alpha R) | x ^ 2 = 1} = ⊤ :=
  s.involution_generation s.geometry hb hC

end CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup.Source
