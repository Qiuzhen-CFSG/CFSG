module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.SectionThree.DistanceTwo.NaturalCore.LocalGeometry
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.SectionThree.CriticalModules.LocalStructure
public import Theory.GroupTheory.PResidual.SubnormalCoreAction
public import Theory.GroupTheory.PResidual.PerfectCover
public import Theory.GroupTheory.Commutator.NormalClosure
public import Theory.GroupTheory.NormalFourCentralizer.Small

/-!
# A small centralizer in the natural distance-two core

Write K = [Q_alpha,Ltilde_alpha]. For a critical endpoint alpha' and its
common edge t, the subgroup D = [K,Z_alpha'] lies in K, in U_alpha', and in
the actual edge commutator [Z_alpha',Q_t]. Since D lies in Q_alpha, Z_alpha
centralizes it. If D were all of the natural eight U_alpha', faithfulness
of that natural action would contradict criticality. Thus |D| is at most
four. D is normal in K, so C_K(D), and consequently C_K(y) for each y in D,
has index at most two.

There is a y in D outside U_alpha: otherwise normal-closure transfer,
critical-pair reversal, the simple SL3(2) quotient and residual commutator
idempotence would give K <= U_alpha, contrary to the non-Frattini premise.
This proves the required element-level consequence of the paper's edge
action estimate directly on the normalized subgroup D of [Z_alpha',Q_t].
It does not require a splitting of Z, a quotient of K, or abelianness of K.

Source: Meierfrankenfeld--Stellmacher, *Pushing up weak BN-pairs of rank two*
(1993), critical-pair reversal (2.2)(iii) and the natural SL3 branch of (3.6),
printed pp.856 and 870--871. The normal-generation argument uses the same
source reduction as the independently proved InvolutionGeneration module.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph

namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceTwo.NaturalCore
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}

/-- Critical-pair reversal and the simple quotient force the local core
commutator to escape U whenever the core escapes the Frattini-small layer. -/
theorem critical_core_commutator_not_le_U (source : LocalSource L R)
    (geometry : Geometry R) (hb : geometry.b R = 2)
    (hlarge : ¬ core R (alpha R) ≤
      (frattini (Q R (alpha R))).map (Q R (alpha R)).subtype ⊔ X R (alpha R))
    {a' : Vertex R}
    (hc : CriticalPair R (alpha R) a' (geometry.exists_critical (alpha R) rfl)) :
    ¬ ⁅core R (alpha R), Z R a'⁆ ≤ U R (alpha R) := by
  have ha' := critical_endpoint_color R (alpha R) rfl _ hc
  have hreverse := source.critical_reverse geometry (alpha R) rfl a' ha' hc
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
  let W := (U R (alpha R)).comap (embedM R)
  have hW : W.Normal := by
    constructor
    intro w hw m
    change embedM R (m * w * m⁻¹) ∈ U R (alpha R)
    simpa only [map_mul, map_inv] using
      le_normalizer_iff.mp (U_normalized (alpha R)) (embedM R m)
        (by rw [alpha, stabilizer_m_base]; exact ⟨m, rfl⟩) _ hw
  let := hW
  intro hcontained
  have hKA : ⁅K, A⁆ ≤ W := by
    apply map_le_iff_le_comap.mp
    rwa [map_commutator, hKm, hAm]
  have hKW : K ≤ W := hfull.symm.le.trans
    ((commutator_mono le_rfl hLN).trans
      (commutator_normalClosure_le_of_normal K A W hKA))
  have hKU : core R (alpha R) ≤ U R (alpha R) := by
    rw [← hKm]
    exact map_le_iff_le_comap.mpr hKW
  have hbpos : 0 < geometry.b R := by omega
  exact hlarge (hKU.trans ((U_le_Z (alpha R)).trans
    ((geometry.omega_bound (alpha R) rfl hbpos).trans le_sup_right)))

/-- The local core commutator is in the actual natural endpoint group.
The identity [Z, G] = [Z, Ltilde] uses the centralizing supplement Q. -/
theorem critical_core_commutator_le_natural (source : LocalSource L R)
    {a' t : Vertex R} (hat : Adjacent R (alpha R) t) (ha't : Adjacent R a' t)
    (ha' : color R a' = false) :
    ⁅core R (alpha R), Z R a'⁆ ≤ U R a' := by
  have hS : core R (alpha R) ≤ stabilizer R a' :=
    (core_le_Q _).trans (Q_le_endpoint_stabilizer hat ha't)
  have he : ⁅Z R a', stabilizer R a'⁆ = U R a' := by
    symm
    apply commutator_eq_of_centralizing_sup
      ((sup_comm _ _).trans (source.local_generation a' ha'))
    · exact le_centralizer_iff.mp
        (commutator_eq_bot_iff_le_centralizer.mp (Z_centralizes_Q R a' ha'))
    · exact (Ltilde_le_stabilizer a').trans (Z_normalized R a')
  rw [commutator_comm]
  exact (commutator_mono le_rfl hS).trans he.le

/-- The endpoint layer normalizes the core inside its own vertex stabilizer. -/
theorem critical_core_commutator_le_core (source : LocalSource L R)
    (geometry : Geometry R) {a' : Vertex R}
    (hc : CriticalPair R (alpha R) a' (geometry.exists_critical (alpha R) rfl)) :
    ⁅core R (alpha R), Z R a'⁆ ≤ core R (alpha R) :=
  le_normalizer_iff_commutator_le_left.mp
    ((source.critical_Z_le_stabilizer geometry (alpha R) rfl a' hc).2.trans
      (core_normalized (alpha R)))

/-- The local core commutator is a proper subgroup of the natural eight.
Equality would make Z_alpha centralize U_alpha', contradicting criticality
and the actual faithful natural action at alpha'. -/
theorem critical_core_commutator_card_le_four (source : LocalSource L R)
    (geometry : Geometry R) (natural : NaturalU R source.projection)
    {a' t : Vertex R}
    (hc : CriticalPair R (alpha R) a' (geometry.exists_critical (alpha R) rfl))
    (hat : Adjacent R (alpha R) t) (ha't : Adjacent R a' t) :
    Nat.card (⁅core R (alpha R), Z R a'⁆ : Subgroup (FreeAmalgam R)) ≤ 4 := by
  have ha' := critical_endpoint_color R (alpha R) rfl _ hc
  have hDU := critical_core_commutator_le_natural source hat ha't ha'
  let : Finite (U R a') := Nat.finite_of_card_ne_zero (by rw [natural.card_at a' ha']; decide)
  have hdvd := card_dvd_of_le hDU
  rw [natural.card_at a' ha'] at hdvd
  have hne : Nat.card (⁅core R (alpha R), Z R a'⁆ : Subgroup (FreeAmalgam R)) ≠ 8 := by
    intro hcard
    have heq : ⁅core R (alpha R), Z R a'⁆ = U R a' :=
      eq_of_le_of_card_ge hDU (by rw [natural.card_at a' ha', hcard])
    have hUQ : U R a' ≤ Q R (alpha R) :=
      heq ▸ (critical_core_commutator_le_core source geometry hc).trans (core_le_Q _)
    apply hc.2
    rw [← natural.centralizer a' ha']
    exact le_inf (source.critical_Z_le_stabilizer geometry (alpha R) rfl a' hc).1
      ((commutator_eq_bot_iff_le_centralizer.mp (Z_centralizes_Q R (alpha R) rfl)).trans
        (centralizer_le hUQ))
  have hdiv := Nat.mem_divisors.mpr ⟨hdvd, (by decide : 8 ≠ 0)⟩
  rw [show Nat.divisors 8 = ({1, 2, 4, 8} : Finset ℕ) by decide] at hdiv
  simp only [Finset.mem_insert, Finset.mem_singleton] at hdiv
  omega

/-- The distance-two non-Frattini branch has an escaping element with core
centralizer of index at most two. The element belongs to the actual edge
commutator [Z_alpha',Q_t]. -/
theorem small_centralizer_witness (source : LocalSource L R)
    (geometry : Geometry R) (hb : geometry.b R = 2)
    (natural : NaturalU R source.projection)
    (hlarge : ¬ core R (alpha R) ≤
      (frattini (Q R (alpha R))).map (Q R (alpha R)).subtype ⊔ X R (alpha R)) :
    ∃ a' t, CriticalPair R (alpha R) a' (geometry.exists_critical (alpha R) rfl) ∧
      Adjacent R (alpha R) t ∧ Adjacent R a' t ∧
      ∃ y : core R (alpha R), (y : FreeAmalgam R) ∈ ⁅Z R a', Q R t⁆ ∧
        (y : FreeAmalgam R) ∉ U R (alpha R) ∧
        (centralizer ({y} : Set (core R (alpha R)))).index ≤ 2 := by
  obtain ⟨a', t, hc, hat, ha't⟩ := critical_edge_exists geometry hb
  let D := ⁅core R (alpha R), Z R a'⁆
  have hDK : D ≤ core R (alpha R) := critical_core_commutator_le_core source geometry hc
  have hcard : Nat.card D ≤ 4 := critical_core_commutator_card_le_four source geometry natural hc hat ha't
  have hescape := critical_core_commutator_not_le_U source geometry hb hlarge hc
  obtain ⟨y, hyD, hyU⟩ := Set.not_subset.mp hescape
  let K := core R (alpha R)
  let E := D.subgroupOf K
  let : Finite K := finite_core (alpha R)
  let : E.Normal := normal_subgroupOf_of_le_normalizer (normalizer_commutator_ge_left _ _)
  have hElem : IsElementaryAbelian 2 D := by
    let := geometry.U_elementary (by omega : 0 < geometry.b R) a'
      (critical_endpoint_color R (alpha R) rfl _ hc)
    exact IsElementaryAbelian.of_le
      (critical_core_commutator_le_natural source hat ha't
        (critical_endpoint_color R (alpha R) rfl _ hc))
  let := hElem
  let : IsElementaryAbelian 2 E := IsElementaryAbelian.subgroupOf hDK
  have hEcard : Nat.card E ≤ 4 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hDK).toEquiv]
    exact hcard
  have hpK : IsPGroup 2 K :=
    (Q_isPGroup R source.two_group source.core_le (alpha R) rfl).to_le (core_le_Q _)
  have hi : (centralizer (E : Set K)).index ≤ 2 :=
    centralizer_index_le_two_of_normal_elementary_card_le_four hpK E hEcard
  have hyK : y ∈ K := hDK hyD
  refine ⟨a', t, hc, hat, ha't, ⟨y, hyK⟩, ?_, hyU, ?_⟩
  · exact ((commutator_mono (core_le_Q (alpha R)) le_rfl).trans
      (local_commutator_le_edge_commutator hat)) hyD
  · exact (index_antitone (centralizer_le (show ({⟨y, hyK⟩} : Set K) ⊆ E from
      Set.singleton_subset_iff.mpr hyD))).trans hi

/-- The small-centralizer field of the natural distance-two extension estimates. -/
theorem small_centralizer (source : LocalSource L R)
    (geometry : Geometry R) (hb : geometry.b R = 2)
    (natural : NaturalU R source.projection)
    (hlarge : ¬ core R (alpha R) ≤
      (frattini (Q R (alpha R))).map (Q R (alpha R)).subtype ⊔ X R (alpha R)) :
    ∃ y : core R (alpha R), (y : FreeAmalgam R) ∉ U R (alpha R) ∧
      (centralizer ({y} : Set (core R (alpha R)))).index ≤ 2 := by
  obtain ⟨_, _, _, _, _, y, _, hy, hi⟩ :=
    small_centralizer_witness source geometry hb natural hlarge
  exact ⟨y, hy, hi⟩

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceTwo.NaturalCore
