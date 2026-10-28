module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.SectionThree.DistanceTwo.NaturalCore.SmallCentralizer
public import Theory.GroupTheory.CommutatorPreimage
public import Theory.GroupTheory.Commutator.NormalizedIndexTwo

/-!
# The kernel acts trivially on the distance-two core quotient

For a critical endpoint alpha', put D = [core_alpha,Z_alpha']. The natural
endpoint calculation bounds |D| by four. Faithfulness of the natural action
at alpha and critical-pair reversal show that [U_alpha,Z_alpha'] is nontrivial.
It lies in D intersect U_alpha. The non-Frattini premise makes this intersection
proper in D, so its index is two. Both factors defining D, and also U_alpha,
are normalized by Q_alpha. The action on that quotient of order two is trivial,
giving [D,Q_alpha] <= U_alpha.

The subgroup of Q_alpha centralizing Q_alpha modulo U_alpha is normalized by
the whole vertex stabilizer. Pull back to the finite group M. The critical
endpoint has nontrivial image in the specified simple SL3(2) quotient, so its
normal closure contains the two-residual. Normal-closure commutator transfer
and residual commutator idempotence then put the entire core in that subgroup.

This proves [core_alpha,Q_alpha] <= U_alpha without a core order calculation,
a natural core quotient, or abelianness of the core. It uses no stronger
conjugate-generation identity for [Q_alpha,Z_alpha'].

Source: Meierfrankenfeld--Stellmacher, *Pushing up weak BN-pairs of rank two*
(1993), critical-pair reversal (2.2)(iii) and the natural branch of (3.6),
printed pp.856 and 870--871. The small endpoint calculation gives directly
the commutator consequence used in the (3.3)--(3.6) argument.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
open scoped commutatorElement
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceTwo.NaturalCore
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}

/-- The local endpoint commutator centralizes Q_alpha modulo U_alpha. -/
theorem critical_core_commutator_Q_le_U (source : LocalSource L R)
    (geometry : Geometry R) (hb : geometry.b R = 2)
    (natural : NaturalU R source.projection)
    (hlarge : ¬ core R (alpha R) ≤
      (frattini (Q R (alpha R))).map (Q R (alpha R)).subtype ⊔ X R (alpha R))
    {a' t : Vertex R}
    (hc : CriticalPair R (alpha R) a' (geometry.exists_critical (alpha R) rfl))
    (hat : Adjacent R (alpha R) t) (ha't : Adjacent R a' t) :
    ⁅⁅core R (alpha R), Z R a'⁆, Q R (alpha R)⁆ ≤ U R (alpha R) := by
  let D := ⁅core R (alpha R), Z R a'⁆
  let W := D ⊓ U R (alpha R)
  have hDK : D ≤ core R (alpha R) := critical_core_commutator_le_core source geometry hc
  let : Finite (core R (alpha R)) := finite_core (alpha R)
  let : Finite D := Finite.of_injective (inclusion hDK) (inclusion_injective hDK)
  let : Finite W := Finite.of_injective (inclusion (show W ≤ D from inf_le_left))
    (inclusion_injective _)
  have hZ : Z R a' ≤ stabilizer R (alpha R) :=
    (source.critical_Z_le_stabilizer geometry (alpha R) rfl a' hc).2
  have hU : U R (alpha R) ≤ core R (alpha R) :=
    U_le_core geometry (by omega) (alpha R) rfl
  have hWne : W ≠ ⊥ := by
    intro hzero
    have hcomm : ⁅U R (alpha R), Z R a'⁆ = ⊥ := by
      apply bot_unique
      rw [← hzero]
      exact le_inf (commutator_mono hU le_rfl)
        (le_normalizer_iff_commutator_le_left.mp (hZ.trans (U_normalized (alpha R))))
    have hreverse := source.critical_reverse geometry (alpha R) rfl a'
      (critical_endpoint_color R (alpha R) rfl _ hc) hc
    apply hreverse.2
    rw [← natural.centralizer_alpha]
    rw [commutator_comm] at hcomm
    exact le_inf hZ (commutator_eq_bot_iff_le_centralizer.mp hcomm)
  have hWcard : 2 ≤ Nat.card W := (one_lt_card_iff_ne_bot W).mpr hWne
  have hDcard : Nat.card D ≤ 4 :=
    critical_core_commutator_card_le_four source geometry natural hc hat ha't
  have hindex : W.relIndex D = 2 := by
    have hmul := (W.subgroupOf D).card_mul_index
    have hcard : Nat.card (W.subgroupOf D) = Nat.card W :=
      Nat.card_congr (subgroupOfEquivOfLe (show W ≤ D from inf_le_left)).toEquiv
    rw [hcard] at hmul
    change Nat.card W * W.relIndex D = Nat.card D at hmul
    have hbound : W.relIndex D ≤ 2 := by nlinarith
    have hpos : W.relIndex D ≠ 0 := (W.subgroupOf D).index_ne_zero_of_finite
    have hne : W.relIndex D ≠ 1 := by
      intro h
      exact critical_core_commutator_not_le_U source geometry hb hlarge hc
        ((relIndex_eq_one.mp h).trans inf_le_right)
    omega
  have hQD : Q R (alpha R) ≤ normalizer (D : Set (FreeAmalgam R)) := by
    intro q hq
    rw [mem_normalizer_iff_map_conj_eq]
    change (⁅core R (alpha R), Z R a'⁆).map (MulAut.conj q).toMonoidHom = _
    rw [map_commutator]
    have hK := mem_normalizer_iff_map_conj_eq.mp (core_normalized (alpha R) hq.1)
    have hZ' := mem_normalizer_iff_map_conj_eq.mp
      (Z_normalized R a' (Q_le_endpoint_stabilizer hat ha't hq))
    change (core R (alpha R)).map (MulAut.conj q).toMonoidHom = core R (alpha R) at hK
    change (Z R a').map (MulAut.conj q).toMonoidHom = Z R a' at hZ'
    rw [hK, hZ']
  have hQU : Q R (alpha R) ≤ normalizer (U R (alpha R) : Set (FreeAmalgam R)) :=
    (show Q R (alpha R) ≤ stabilizer R (alpha R) from fun _ hx => hx.1).trans
      (U_normalized (alpha R))
  have hQW : Q R (alpha R) ≤ normalizer (W : Set (FreeAmalgam R)) :=
    (le_inf hQD hQU).trans inf_normalizer_le_normalizer_inf
  exact (commutator_le_of_normalized_index_two D W (Q R (alpha R))
    inf_le_left hindex hQD hQW).trans inf_le_right

/-- A vertex-normalized bound on the critical core commutator contains the
whole core. Normal closure and the two-residual are taken inside finite M. -/
theorem core_le_of_critical_commutator_le (source : LocalSource L R)
    (geometry : Geometry R) {a' : Vertex R}
    (hc : CriticalPair R (alpha R) a' (geometry.exists_critical (alpha R) rfl))
    (W : Subgroup (FreeAmalgam R))
    (hW : stabilizer R (alpha R) ≤ normalizer (W : Set (FreeAmalgam R)))
    (hcomm : ⁅core R (alpha R), Z R a'⁆ ≤ W) : core R (alpha R) ≤ W := by
  have hreverse := source.critical_reverse geometry (alpha R) rfl a'
    (critical_endpoint_color R (alpha R) rfl _ hc) hc
  have hZ : Z R a' ≤ (embedM R).range := by
    change Z R a' ≤ Mbar R
    rw [← stabilizer_m_base]
    exact (source.critical_Z_le_stabilizer geometry (alpha R) rfl a' hc).2
  let A := (Z R a').comap (embedM R)
  have hAm : A.map (embedM R) = Z R a' :=
    (map_comap_eq _ _).trans (inf_eq_right.mpr hZ)
  let K := ⁅pCore 2 M, pResidual 2 M⁆
  have hKm : K.map (embedM R) = core R (alpha R) :=
    (core_alpha R source.two_group source.core_le rfl).symm
  have hA : ¬ A ≤ pCore 2 M := by
    intro h
    apply hreverse.2
    rw [← hAm, Q_alpha R source.two_group source.core_le]
    exact map_mono h
  let N := normalClosure (A : Set M)
  have hLN : pResidual 2 M ≤ N := by
    let : IsSimpleGroup SL := Atlas.Comparisons.Exceptional.sl3Two_simple
    have hn : (N.map source.projection).Normal :=
      (inferInstance : N.Normal).map _ source.projection_surjective
    have htop : N.map source.projection = ⊤ := by
      rcases hn.eq_bot_or_eq_top with h | h
      · apply False.elim
        apply hA
        have hNQ : N ≤ pCore 2 M := by
          simpa only [source.projection_kernel] using (Subgroup.map_eq_bot_iff _).mp h
        exact le_normalClosure.trans hNQ
      · exact h
    rw [source.residual]
    exact source.residual_le_of_image_top N htop
  have hfull : ⁅K, pResidual 2 M⁆ = K :=
    commutator_isPPerfect_idempotent (pResidual 2 M) (pCore 2 M)
      (isPPerfect_pResidual 2) pCore_isPGroup le_normalizer_of_normal
  let W₀ := W.comap (embedM R)
  let : W₀.Normal := by
    constructor
    intro w hw m
    change embedM R (m * w * m⁻¹) ∈ W
    simpa only [map_mul, map_inv] using
      le_normalizer_iff.mp hW (embedM R m)
        (by rw [alpha, stabilizer_m_base]; exact ⟨m, rfl⟩) _ hw
  have hKA : ⁅K, A⁆ ≤ W₀ := by
    apply map_le_iff_le_comap.mp
    rwa [map_commutator, hKm, hAm]
  have hKW : K ≤ W₀ := hfull.symm.le.trans
    ((commutator_mono le_rfl hLN).trans
      (commutator_normalClosure_le_of_normal K A W₀ hKA))
  rw [← hKm]
  exact map_le_iff_le_comap.mpr hKW

/-- In the natural large-core branch at distance two, Q_alpha acts trivially
on the actual quotient core_alpha/U_alpha. -/
theorem core_commutator_Q_le_U (source : LocalSource L R)
    (geometry : Geometry R) (hb : geometry.b R = 2)
    (natural : NaturalU R source.projection)
    (hlarge : ¬ core R (alpha R) ≤
      (frattini (Q R (alpha R))).map (Q R (alpha R)).subtype ⊔ X R (alpha R)) :
    ⁅core R (alpha R), Q R (alpha R)⁆ ≤ U R (alpha R) := by
  obtain ⟨a', t, hc, hat, ha't⟩ := critical_edge_exists geometry hb
  let S := stabilizer R (alpha R)
  let W := commutatorPreimage (Q R (alpha R)) (Q R (alpha R)) (U R (alpha R))
  have hQU : Q R (alpha R) ≤ normalizer (U R (alpha R) : Set (FreeAmalgam R)) :=
    (show Q R (alpha R) ≤ S from fun _ hx => hx.1).trans (U_normalized (alpha R))
  have hW : S ≤ normalizer (W : Set (FreeAmalgam R)) :=
    commutatorPreimage_normalized _ _ _ _ hQU
      (Q_normalized R (alpha R)) (Q_normalized R (alpha R)) (U_normalized (alpha R))
  have hlocal : ⁅core R (alpha R), Z R a'⁆ ≤ W :=
    le_commutatorPreimage
      ((critical_core_commutator_le_core source geometry hc).trans (core_le_Q (alpha R)))
      (critical_core_commutator_Q_le_U source geometry hb natural hlarge hc hat ha't)
  exact (commutator_mono
    (core_le_of_critical_commutator_le source geometry hc W hW hlocal) le_rfl).trans
      (commutator_commutatorPreimage_le _ _ _ hQU)

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceTwo.NaturalCore
