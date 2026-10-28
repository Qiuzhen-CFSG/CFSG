module
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.CoreCollapse.OppositeCentralizer.ConstructionSeed

public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.Recognition.FactorBlockInvolutionFusion

/-!
# Nonfusion and the moved plane of the opposite involution

Burnside fusion in the weakly closed abelian conjugate span replaces an
ambient conjugator by an element of its normalizer. The source normalizer
lies in M and therefore preserves V. Since the three-factor product lies
outside L, it cannot be fused to the original point. Applying the same
fusion control to the known involution fusion in RU identifies Ω₁(X∩U).
The fixed-point-free cubic actor supplies the full moved-plane identity
inside the literal parabolic centralizer.

These are proved local clauses, not global centralizer recognition.
Source: Aschbacher--Smith 14.3.22, printed pp.998--999.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.CoreCollapse.OppositeCentralizer
open Chapter12.Section08 Chapter12.Section08.InvariantFlag
open CFSG.Quasithin.ChapterI.Section06To08
variable {G : Type*} [Group G] {T : Sylow 2 G} {V : Subgroup G}

theorem span_eq_conjugateSpanIn (F : InvariantFlag T V 2) :
    span F = conjugateSpanIn (supplement F) (T : Subgroup G) := by
  rw [span_eq_sSup]
  congr 1
  ext A
  constructor
  · rintro ⟨a, he, ha⟩
    exact ⟨ha, a⁻¹, mem_top _, he⟩
  · rintro ⟨ha, a, _, he⟩
    exact ⟨a⁻¹, by simpa only [conjugate, conjSubgroup, inv_inv] using he, ha⟩


variable [Finite G]
/-- Element fusion in the abelian span preserves every subgroup invariant
under its full normalizer. -/
theorem CyclicTIInput.conjugate_mem_seed {F : InvariantFlag T V 2}
    {L : Subgroup G} (hc : CyclicTIInput F L)
    (hNV : normalizer (span F : Set G) ≤ normalizer (V : Set G))
    {x y : G} (hx : x ∈ V) (hy : y ∈ span F) (hxy : IsConj x y) : y ∈ V := by
  let := hc.abelian
  have hweak (a : G) (ha : (span F).map (MulAut.conj a).toMonoidHom ≤ (T : Subgroup G)) :
      a ∈ normalizer (span F : Set G) := by
    apply mem_normalizer_iff_map_conj_eq.mpr
    rw [span_eq_conjugateSpanIn] at ha ⊢
    exact conjugateSpanIn_weakly_closed a ha
  obtain ⟨n, hn, he⟩ := T.weakly_closed_normalizer_controls_centralizer_fusion (span F)
    (conjugateSubgroupClosure_le_self _ _) hweak
    (le_centralizer (span F) (hc.seed_le hx)) (le_centralizer (span F) hy) hxy
  rw [← he]
  exact (mem_normalizer_iff.mp (hNV hn) x).mp hx


/-- Involutions fused to the seed give the precise omega subgroup of an
intersection with the abelian span. -/
theorem CyclicTIInput.omega_span_inf {F : InvariantFlag T V 2}
    {L : Subgroup G} [IsElementaryAbelian 2 V] (hc : CyclicTIInput F L)
    (hNV : normalizer (span F : Set G) ≤ normalizer (V : Set G))
    (B : Subgroup G) (hVB : V ≤ B) (z : G) (hz : z ∈ V)
    (hf : ∀ x ∈ B, orderOf x = 2 → IsConj z x) :
    omegaOneAmbient (span F ⊓ B) = V := by
  apply le_antisymm
  · apply (omegaOneAmbient_le_iff _ _).mpr
    intro x hx hx2
    by_cases hx1 : x = 1
    · exact hx1 ▸ V.one_mem
    · exact hc.conjugate_mem_seed hNV hz hx.1 (hf x hx.2 (orderOf_eq_prime hx2 hx1))
  · exact (omegaOneAmbient_eq_self V).symm.le.trans
      (omegaOneAmbient_mono (le_inf hc.seed_le hVB))


open Recognition Chapter14.Section02 SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06

/-- The cubic actor moves the whole source plane. -/
theorem CubicTriple.plane_moved_by_actor {F : InvariantFlag T V 2}
    {L : Subgroup G} {z d a : G} [IsElementaryAbelian 2 V]
    (s : CubicTriple F L z d a) (hLN : L ≤ normalizer (V : Set G)) :
    ⁅V, zpowers a⁆ = V := by
  have hfix : V ⊓ centralizer (zpowers a : Set G) = ⊥ := by
    apply bot_unique
    intro v hv
    exact s.actor_fixed ▸ (show v ∈ (F.I₂ L).pCoreIn 2 ⊓ centralizer ({a} : Set G) from
      ⟨s.seed_le_core hv.1, (centralizer_le (show ({a} : Set G) ⊆ zpowers a from
        Set.singleton_subset_iff.mpr (mem_zpowers a))) hv.2⟩)
  have hcop : Nat.Coprime (Nat.card (zpowers a)) (Nat.card V) :=
    IsPGroup.coprime_card_of_ne 3 2 (by decide) (zpowers a) V
      (IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, s.actor_order, pow_one]))
      (IsElementaryAbelian.isPGroup 2 V)
  have hmove : ⁅V, zpowers a⁆ = V := by
    have hh := eq_commutator_sup_centralizer_of_solvable_coprime V (zpowers a)
      (zpowers_le.mpr (hLN s.actor_mem))
      (Group.isSolvable_of_comm fun x y => mul_comm' x y) hcop
    simpa only [hfix, sup_bot_eq] using hh.symm
  exact hmove

/-- The same moved plane inside the actual parabolic centralizer. -/
theorem CubicTriple.plane_moved {F : InvariantFlag T V 2}
    {L : Subgroup G} {z d a : G} [IsElementaryAbelian 2 V]
    (s : CubicTriple F L z d a) (hc : CyclicTIInput F L)
    (hLN : L ≤ normalizer (V : Set G)) (hLI : L ≤ F.I₂ L)
    (hIN : F.I₂ L ≤ normalizer (V : Set G)) :
    ⁅V, F.I₂ L ⊓ centralizer ({tripleProduct d a} : Set G)⁆ = V := by
  apply le_antisymm
  · exact le_normalizer_iff_commutator_le_left.mp (inf_le_left.trans hIN)
  · exact (s.plane_moved_by_actor hLN).symm.le.trans
      (commutator_mono le_rfl (zpowers_le.mpr
        ⟨hLI s.actor_mem, s.actor_centralizes_product hc⟩))

theorem source_triple_plane_moved
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hnot : ¬ ClassificationModels.IsTheoremEModel G)
    (F : InvariantFlag T (rankTwoSeed T M) 2)
    [IsElementaryAbelian 2 (rankTwoSeed T M)]
    (hne : ¬ IsMulCommutative F.U)
    (g : G) (hgP : g ∈ F.P (sourceResidual M Mc)) (hgH : g ∉ F.H)
    (hs : Group.IsSolvable F.TerminalHdot)
    (hc : CyclicTIInput F (sourceResidual M Mc)) {z d a : G}
    (s : CubicTriple F (sourceResidual M Mc) z d a) :
    ⁅rankTwoSeed T M, F.I₂ (sourceResidual M Mc) ⊓
      centralizer ({tripleProduct d a} : Set G)⁆ = rankTwoSeed T M := by
  let h := source_lemma_14_2_4 hG T hempty hM hu hmany hcard e
  have dg := rankTwo_closure_geometry h F hne
  have hUT : F.U ≤ (T : Subgroup G) := normalized_pSubgroup_le_sylow T F.H F.U
    (F.invariant 1) F.U_le_H (le_normalizer_conjugateSpanBy _ _) dg.two
  have hTN : (T : Subgroup G) ≤ normalizer (rankTwoSeed T M : Set G) := by
    simpa only [Gi, F.last] using F.invariant 2
  have hIN : F.I₂ (sourceResidual M Mc) ≤ normalizer (rankTwoSeed T M : Set G) :=
    conjugateSpanBy_le (hUT.trans hTN)
      ((F.P_le_seed_normalizer _ h.L_normalizes_seed).trans (normalizer _).le_normalizer)
  have hLI : sourceResidual M Mc ≤ F.I₂ (sourceResidual M Mc) := by
    exact (source_parabolic_residual_core_structure_of_solvable
      hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs).1.symm.le.trans (map_subtype_le _)
  exact s.plane_moved hc h.L_normalizes_seed hLI hIN

/-- The original point is not conjugate to the constructed opposite product. -/
theorem source_triple_nonfusion
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hnot : ¬ ClassificationModels.IsTheoremEModel G)
    (F : InvariantFlag T (rankTwoSeed T M) 2)
    [IsElementaryAbelian 2 (rankTwoSeed T M)]
    (hne : ¬ IsMulCommutative F.U)
    (g : G) (hgP : g ∈ F.P (sourceResidual M Mc)) (hgH : g ∉ F.H)
    (hs : Group.IsSolvable F.TerminalHdot)
    (hself : FactorSelfCentralizing F (sourceResidual M Mc))
    (hc : CyclicTIInput F (sourceResidual M Mc)) {z d a : G}
    (s : CubicTriple F (sourceResidual M Mc) z d a) :
    ¬ IsConj z (tripleProduct d a) := by
  have hwL := source_triple_outside_residual
    hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs hc s
  have hcore := (source_parabolic_residual_core_structure_of_solvable
    hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs).2.2.1
  have hVL : rankTwoSeed T M ≤ sourceResidual M Mc :=
    s.seed_le_core.trans (hcore ▸ pCoreIn_le 2 (sourceResidual M Mc))
  obtain ⟨_, _, _, _, _, _, _, _, hNM⟩ := source_supplement_span
    hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs hself hc.strict
  have hNV : normalizer (span F : Set G) ≤ normalizer (rankTwoSeed T M : Set G) := by
    rw [span_eq_conjugateSpanIn]
    exact hNM.trans RankTwoHypothesis.M_normalizes_seed
  intro hf
  exact hwL (hVL (hc.conjugate_mem_seed hNV
    (F.le_seed 1 (s.point.symm ▸ mem_zpowers z)) (s.product_mem_span hc) hf))

theorem source_span_core_omega
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hnot : ¬ ClassificationModels.IsTheoremEModel G)
    (F : InvariantFlag T (rankTwoSeed T M) 2)
    [IsElementaryAbelian 2 (rankTwoSeed T M)]
    (hne : ¬ IsMulCommutative F.U)
    (g : G) (hgP : g ∈ F.P (sourceResidual M Mc)) (hgH : g ∉ F.H)
    (hs : Group.IsSolvable F.TerminalHdot)
    (hself : FactorSelfCentralizing F (sourceResidual M Mc))
    (hc : CyclicTIInput F (sourceResidual M Mc)) {z d a : G}
    (s : CubicTriple F (sourceResidual M Mc) z d a) :
    omegaOneAmbient (span F ⊓ F.U) = rankTwoSeed T M := by
  obtain ⟨_, _, _, _, _, _, _, _, hNM⟩ := source_supplement_span
    hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs hself hc.strict
  have hNV : normalizer (span F : Set G) ≤ normalizer (rankTwoSeed T M : Set G) := by
    rw [span_eq_conjugateSpanIn]
    exact hNM.trans RankTwoHypothesis.M_normalizes_seed
  have hz2 : orderOf z = 2 := by
    rw [← Nat.card_zpowers, ← s.point]
    simpa using F.card 1 (by decide)
  have hz1 : z ≠ 1 := by intro he; simp [he] at hz2
  have hz : z ∈ F.Vi 1 := s.point.symm ▸ mem_zpowers z
  apply hc.omega_span_inf hNV F.U (le_conjugateSpanBy _ _) z (F.le_seed 1 hz)
  intro x hx hx2
  exact source_ru_involutions_fused_of_solvable
    hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs z hz hz1 x
    (mem_sup_right hx) hx2

end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.CoreCollapse.OppositeCentralizer
