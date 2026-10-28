module
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.CoreCollapse.OppositeCentralizer.ConstructionFusion
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.CoreCollapse.OppositeCentralizer.ConstructionSpan
public import Theory.GroupTheory.InvolutionAbelianSpan
/-!
# Core displacement and the opposite parabolic centralizer

The normal abelian span bounds [R,w] by Ω₁(X∩R)=V. Self-centralization
of the marked elementary factor makes this displacement nonzero, and the
fixed-free cubic actor makes it the whole four-group. The central
commutator map then computes |C_R(w)|=16 and provides conjugators for
all of Vw. The omega calculation gives the literal Frattini factorization
I₂=R C_{I₂}(w), without changing the supplied Sylow subgroup.

These are local construction clauses; the residual centralizer geometry and
global centralizer recognition remain with qt-e-14322-core-collapse.
Source: Aschbacher--Smith 14.3.22, printed p.999.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.CoreCollapse.OppositeCentralizer
open Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Recognition Chapter14.Section02 SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]
variable
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
    (s : CubicTriple F (sourceResidual M Mc) z d a)
include hG hempty hM hu hmany hcard e hnot hne hgP hgH hs hself hc s

/-- The involutions in the literal span-core intersection are exactly the source plane. -/
theorem source_span_parabolic_core_omega :
    omegaOneAmbient (span F ⊓ (F.I₂ (sourceResidual M Mc)).pCoreIn 2) = rankTwoSeed T M := by
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
  apply hc.omega_span_inf hNV _ s.seed_le_core z (F.le_seed 1 hz)
  intro x hx hx2
  exact source_ru_involutions_fused_of_solvable
    hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs z hz hz1 x
    (mem_sup_left hx) hx2

/-- The original parabolic core displaces the constructed opposite involution through the full source plane. -/
theorem source_triple_core_commutator :
    ⁅(F.I₂ (sourceResidual M Mc)).pCoreIn 2, zpowers (tripleProduct d a)⁆ = rankTwoSeed T M := by
  let R := (F.I₂ (sourceResidual M Mc)).pCoreIn 2
  let L := sourceResidual M Mc
  let w := tripleProduct d a
  let h := source_lemma_14_2_4 hG T hempty hM hu hmany hcard e
  have hcore := (source_parabolic_residual_core_structure_of_solvable
    hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs).2.2.1
  change L.pCoreIn 2 = R at hcore
  have hRL : R ≤ L := by rw [← hcore]; exact pCoreIn_le 2 L
  have hLN : L ≤ normalizer (R : Set G) := by
    rw [← hcore]
    exact L.le_normalizer.trans (normalizer_le_normalizer_characteristic_image L (pCore 2 L))
  have hTN : (T : Subgroup G) ≤ normalizer (R : Set G) := by
    rw [← hcore]
    exact h.sylow_normalizes_L.trans (normalizer_le_normalizer_characteristic_image L (pCore 2 L))
  have hwT := (s.product_mem_sylow_and_square hc).1
  have hw2 := (s.product_mem_sylow_and_square hc).2
  let := hc.abelian
  have hbound : ⁅R, zpowers w⁆ ≤ rankTwoSeed T M := by
    have hh := commutator_le_omega_of_abelian_span R (span F) w
      (hRL.trans (le_sup_left.trans hc.normalized)) (s.product_mem_span hc) (hTN hwT) hw2
    rw [source_span_parabolic_core_omega hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs hself hc s] at hh
    exact hh
  have hneW : ⁅R, zpowers w⁆ ≠ ⊥ := by
    intro he
    have hRC : R ≤ centralizer ({w} : Set G) := by
      have hh := commutator_eq_bot_iff_le_centralizer.mp he
      rw [zpowers_eq_closure, centralizer_closure] at hh
      exact hh
    obtain ⟨_, A, hAR, hVA, hEA, hAc, hAU, hAN, _⟩ :=
      source_factor_supplement_action_of_solvable
        hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs
    have hwA : w ∈ A := by
      rw [hself A hEA hAR hVA hAc hAU hAN]
      intro x hx
      exact mem_centralizer_singleton_iff.mp (hRC (hAR hx))
    exact source_triple_outside_residual hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs hc s
      (hRL (hAR hwA))
  apply invariant_four_eq_of_fixed_free (rankTwoSeed T M) ⁅R, zpowers w⁆ a
    (by simpa [F.last] using F.card 2 (by decide)) hbound hneW
  · apply mem_normalizer_iff_map_conj_eq.mpr
    rw [map_commutator, mem_normalizer_iff_map_conj_eq.mp (hLN s.actor_mem), MonoidHom.map_zpowers]
    have hac : Commute a w := mem_centralizer_singleton_iff.mp (s.actor_centralizes_product hc)
    have haw : (MulAut.conj a) w = w := by
      change a * w * a⁻¹ = w
      exact mul_inv_eq_iff_eq_mul.mpr hac.eq
    change ⁅R, zpowers ((MulAut.conj a) w)⁆ = _
    rw [haw]
  · apply bot_unique
    intro v hv
    exact s.actor_fixed ▸ (show v ∈ R ⊓ centralizer ({a} : Set G) from ⟨s.seed_le_core hv.1, hv.2⟩)

omit hself hc s in
/-- The common plane of the two elementary factors is central in their join R. -/
theorem source_seed_centralizes_parabolic_core :
    rankTwoSeed T M ≤ centralizer ((F.I₂ (sourceResidual M Mc)).pCoreIn 2 : Set G) := by
  obtain ⟨A, B, _, _, hVA, hVB, hEA, hEB, _, _, _, hsup, _⟩ :=
    source_elementary_factors_of_solvable
      hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs
  let := hEA
  let := hEB
  rw [← hsup]
  apply le_centralizer_iff.mp
  apply sup_le
  · exact le_centralizer_iff.mp (hVA.trans A.le_centralizer)
  · exact le_centralizer_iff.mp (hVB.trans B.le_centralizer)

/-- The source commutator calculation supplies actual R-conjugators and the centralizer order sixteen. -/
theorem source_triple_core_orbit_and_card :
    (∀ v ∈ rankTwoSeed T M, ∃ r ∈ (F.I₂ (sourceResidual M Mc)).pCoreIn 2,
      r * tripleProduct d a * r⁻¹ = v * tripleProduct d a) ∧
    Nat.card ((F.I₂ (sourceResidual M Mc)).pCoreIn 2 ⊓
      centralizer ({tripleProduct d a} : Set G) : Subgroup G) = 16 := by
  let R := (F.I₂ (sourceResidual M Mc)).pCoreIn 2
  have h := source_lemma_14_2_4 hG T hempty hM hu hmany hcard e
  have hcore := (source_parabolic_residual_core_structure_of_solvable
    hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs).2.2.1
  change (sourceResidual M Mc).pCoreIn 2 = R at hcore
  have hwN : tripleProduct d a ∈ normalizer (R : Set G) := by
    rw [← hcore]
    exact (h.sylow_normalizes_L.trans
      (normalizer_le_normalizer_characteristic_image (sourceResidual M Mc) (pCore 2 (sourceResidual M Mc))))
      (s.product_mem_sylow_and_square hc).1
  have hwL := source_triple_outside_residual
    hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs hc s
  have hw1 : tripleProduct d a ≠ 1 := fun he => hwL (he ▸ (sourceResidual M Mc).one_mem)
  have hw := (s.involution_of_ne_one hc hw1).2
  have hcomm := source_triple_core_commutator hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs hself hc s
  have hcent := source_seed_centralizes_parabolic_core hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs
  refine ⟨exists_conjugator_of_central_commutator R (rankTwoSeed T M) (tripleProduct d a) hw hwN hcomm hcent, ?_⟩
  have hh := involution_centralizer_card_of_central_commutator R (rankTwoSeed T M) (tripleProduct d a) hw hwN hcomm hcent
  have hVcard : Nat.card (rankTwoSeed T M) = 4 := by simpa [F.last] using F.card 2 (by decide)
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, hRcard, _⟩ :=
    source_elementary_factors_of_solvable hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs
  change Nat.card R = 64 at hRcard
  rw [hVcard, hRcard] at hh
  change Nat.card (R ⊓ centralizer ({tripleProduct d a} : Set G) : Subgroup G) = 16
  omega

/-- The constructed opposite involution is fused to its product with the original marked point. -/
theorem source_triple_product_fusion : IsConj (tripleProduct d a) (tripleProduct d a * z) := by
  have hzV : z ∈ rankTwoSeed T M := F.le_seed 1 (s.point.symm ▸ mem_zpowers z)
  obtain ⟨r, _, hr⟩ := (source_triple_core_orbit_and_card
    hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs hself hc s).1 z hzV
  apply isConj_iff.mpr
  refine ⟨r, ?_⟩
  have hzcomm := mem_centralizer_singleton_iff.mp (s.plane_centralizes_product hc hzV)
  simpa only [hzcomm] using hr

omit hnot hne hgP hgH hs hself in
/-- The full omega subgroup is the original plane joined with the literal opposite involution. -/
theorem source_span_omega :
    omegaOneAmbient (span F) = rankTwoSeed T M ⊔ zpowers (tripleProduct d a) := by
  let := hc.abelian
  have h := source_lemma_14_2_4 hG T hempty hM hu hmany hcard e
  have hzV : z ∈ rankTwoSeed T M := F.le_seed 1 (s.point.symm ▸ mem_zpowers z)
  have hd4 : orderOf d = 4 := by rw [← Nat.card_zpowers, s.generator, hc.card]
  apply omega_three_cyclic_four_span (span F) (rankTwoSeed T M)
    d ((MulAut.conj a⁻¹) d) (tripleProduct d a) hd4
    (((MulAut.conj a⁻¹).orderOf_eq d).trans hd4) (s.product_mem_sylow_and_square hc).2
    (by simpa only [← map_pow, s.square] using s.squares_distinct.1)
    (s.span_eq_pair_sup_product hc) hc.seed_le (s.square.symm ▸ hzV)
  rw [← map_pow, s.square]
  exact (mem_normalizer_iff.mp (h.L_normalizes_seed ((sourceResidual M Mc).inv_mem s.actor_mem)) z).mp hzV

/-- Transitivity on Vw supplies the Frattini factorization inside the original I₂. -/
theorem source_triple_parabolic_frattini :
    F.I₂ (sourceResidual M Mc) = (F.I₂ (sourceResidual M Mc)).pCoreIn 2 ⊔
      (F.I₂ (sourceResidual M Mc) ⊓ centralizer ({tripleProduct d a} : Set G)) := by
  let := hc.abelian
  have h := source_lemma_14_2_4 hG T hempty hM hu hmany hcard e
  have dg := rankTwo_closure_geometry h F hne
  have hUT : F.U ≤ (T : Subgroup G) := normalized_pSubgroup_le_sylow T F.H F.U
    (F.invariant 1) F.U_le_H (le_normalizer_conjugateSpanBy _ _) dg.two
  have hUP : F.U ≤ F.P (sourceResidual M Mc) := by rw [F.P_rankTwo]; exact hUT.trans le_sup_right
  have hIP : F.I₂ (sourceResidual M Mc) ≤ F.P (sourceResidual M Mc) := conjugateSpanBy_le_self hUP
  have hIX : F.I₂ (sourceResidual M Mc) ≤ normalizer (span F : Set G) := by
    rw [F.P_rankTwo] at hIP
    exact hIP.trans hc.normalized
  have hIV : F.I₂ (sourceResidual M Mc) ≤ normalizer (rankTwoSeed T M : Set G) :=
    hIP.trans (F.P_le_seed_normalizer _ h.L_normalizes_seed)
  have hwL := source_triple_outside_residual
    hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs hc s
  have hw1 : tripleProduct d a ≠ 1 := fun he => hwL (he ▸ (sourceResidual M Mc).one_mem)
  have hcore := (source_parabolic_residual_core_structure_of_solvable
    hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs).2.2.1
  have hVL : rankTwoSeed T M ≤ sourceResidual M Mc :=
    s.seed_le_core.trans (hcore ▸ pCoreIn_le 2 (sourceResidual M Mc))
  exact eq_sup_centralizer_of_involution_coset (F.I₂ (sourceResidual M Mc))
    ((F.I₂ (sourceResidual M Mc)).pCoreIn 2) (rankTwoSeed T M) (span F) (tripleProduct d a)
    (pCoreIn_le _ _) hc.seed_le (s.product_mem_span hc) (s.involution_of_ne_one hc hw1).2
    (fun hw => hwL (hVL hw)) hIX hIV
    (source_span_omega hG T hempty hM hu hmany hcard e F hc s)
    (source_triple_core_orbit_and_card hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs hself hc s).1

end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.CoreCollapse.OppositeCentralizer
