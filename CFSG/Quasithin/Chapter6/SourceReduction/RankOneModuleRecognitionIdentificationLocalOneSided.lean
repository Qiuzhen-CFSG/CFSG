module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionIdentificationLocalNoncyclic
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionNaturalContainedConjugateFieldGeometryLines
public import Theory.GroupTheory.ConjugateSpanCentralizer
public import Theory.GroupTheory.AbelianCommutatorIndex
public import Theory.GroupTheory.CommutatorPreimage.Membership

/-!
# The initial one-sided conjugate configuration

Suppose the original natural layer B normalizes A = B^g but does not
centralize it. Its fixed subgroup U is a field plane. The literal closure
J = ⟨B^{C_G(U)}⟩ is elementary abelian and lies in O₂(C_G(U)). Natural
offender geometry identifies F = [A,B] as the central plane of A, and the
closure has the same action on A as B. In particular [A,J] = F = A ∩ J.

The small intersection B ∩ A and the global s-value force N_A(B) = F.
Thus A meets the kernel of the actual action on J/U in precisely F, of
index four. These are the opening reductions of 6.2.7, before its action
classification contradiction; one-sided commutation is not assumed or
asserted. The companion Chapter 12 module applies them to [R₂(LT),L].

Source: Aschbacher--Smith, 6.2.7, printed p.682, through the paragraph
identifying A* as a four-group. Uses 6.2.4(1,4) and 6.2.5(5), pp.680--681.
-/

public section
open Subgroup Theory.GroupTheory Representation.BinaryOffender
open scoped IsMulCommutative Pointwise commutatorElement
namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L M R : Subgroup G} {n : ℕ}

/-- The centralizer closure of any plane in the original layer is elementary. -/
theorem local_plane_closure_elementary
    (h : Hypothesis611 KnownSimple.IsKnownSimple T L M R n)
    (hnatural : Conclusion6127 (T : Subgroup G) L M R n)
    (hE : ChapterE.Section06.HypothesisE61 KnownSimple.IsKnownSimple T M (layer L R))
    (hfactor : CentralLineNormalizerFactorization M (ZS (T : Subgroup G) L R))
    {U : Subgroup G} (hUV : U ≤ layer L R) (hUc : 4 ≤ Nat.card U) :
    IsElementaryAbelian 2 (conjugateSpanBy (layer L R) (centralizer (U : Set G))) := by
  let := h.layer_elementary
  let B := layer L R
  let H := centralizer (U : Set G)
  have hEC : conjugateSpanBy B H ≤ centralizer (B : Set G) := by
    apply (closure_le _).mpr
    rintro x ⟨g, hg, b, hb, rfl⟩
    have hUconj : U.map (MulAut.conj g).toMonoidHom = U :=
      mem_normalizer_iff_map_conj_eq.mp (Subgroup.centralizer_le_normalizer _ hg)
    have hUmeet : U ≤ B ⊓ B.map (MulAut.conj g).toMonoidHom :=
      le_inf hUV (hUconj ▸ map_mono hUV)
    have hc := local_commuting_noncyclic h hnatural hE hfactor g
      (hUc.trans (card_le_of_le hUmeet))
    exact le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hc)
      (mem_map_of_mem _ hb)
  let : IsMulCommutative (conjugateSpanBy B H) :=
    (conjugateSpanBy_commutative_iff B H).mpr (le_centralizer_iff.mp hEC)
  exact conjugateSpanBy_elementary_of_commutative B H

private theorem elementary_extension_same_action
    (h : Hypothesis611 KnownSimple.IsKnownSimple T L M R n)
    (hnatural : Conclusion6127 (T : Subgroup G) L M R n)
    (hE : ChapterE.Section06.HypothesisE61 KnownSimple.IsKnownSimple T M (layer L R))
    (g : G) (A : Subgroup G) [IsElementaryAbelian 2 A]
    (hAN : A ≤ normalizer (layer L R : Set G))
    (hgA : (layer L R).map (MulAut.conj g).toMonoidHom ≤ A)
    (hnon : ¬ (layer L R).map (MulAut.conj g).toMonoidHom ≤ centralizer (layer L R : Set G)) :
    ChapterE.inducedAutomizer (layer L R) A =
      ChapterE.inducedAutomizer (layer L R) ((layer L R).map (MulAut.conj g).toMonoidHom) := by
  let := h.layer_elementary
  let B := layer L R
  let J := B.map (MulAut.conj g).toMonoidHom
  let : IsElementaryAbelian 2 J := IsElementaryAbelian.map _
  let : IsElementaryAbelian 2 (ChapterE.inducedAutomizer B A) :=
    ChapterE.inducedAutomizer_elementary B A hAN
  let : IsElementaryAbelian 2 (ChapterE.inducedAutomizer B J) :=
    ChapterE.inducedAutomizer_elementary B J (hgA.trans hAN)
  have hnat : IsNaturalModule L B n := hnatural.1 ▸ hnatural.2.1
  have hbound := elementaryActionRankBound_of_natural h hnat hE A inferInstance hAN
  have he := conjugate_action_corank_eq_of_natural h hnat hE
    (natural_layer_rank_bounds h hnat hE).2.2 g (hgA.trans hAN) hnon
  have hpow (K : Subgroup (ChapterE.Automizer B)) [IsElementaryAbelian 2 K] :
      Nat.card K = 2 ^ rank K := by
    obtain ⟨m, hm⟩ := (IsElementaryAbelian.isPGroup 2 K).exists_card_eq
    rw [rank, hm, Nat.log_pow (by decide : 1 < 2)]
  apply (eq_of_le_of_card_ge (map_mono (comap_mono hgA)) ?_).symm
  change Nat.card (ChapterE.inducedAutomizer B A) ≤ Nat.card (ChapterE.inducedAutomizer B J)
  rw [hpow (ChapterE.inducedAutomizer B A), hpow (ChapterE.inducedAutomizer B J),
    ChapterE.rank_inducedAutomizer _ _ hAN,
    ChapterE.rank_inducedAutomizer _ _ (hgA.trans hAN), he]
  exact Nat.pow_le_pow_right (by decide) hbound



private theorem one_sided_line_geometry
    (h : Hypothesis611 KnownSimple.IsKnownSimple T L M R n)
    (hnatural : Conclusion6127 (T : Subgroup G) L M R n)
    (hE : ChapterE.Section06.HypothesisE61 KnownSimple.IsKnownSimple T M (layer L R))
    (g : G)
    (hBA : layer L R ≤ normalizer ((layer L R).map (MulAut.conj g).toMonoidHom : Set G))
    (hnon : ¬ (layer L R).map (MulAut.conj g).toMonoidHom ≤ centralizer (layer L R : Set G)) :
    let B := layer L R
    let A := B.map (MulAut.conj g).toMonoidHom
    let F := ⁅A, B⁆
    F = A ⊓ centralizer (B : Set G) ∧ Nat.card F = 4 ∧
      centralizer (F : Set G) ≤ normalizer (A : Set G) := by
  let := h.layer_elementary
  let B := layer L R
  let A' := B.map (MulAut.conj g⁻¹).toMonoidHom
  have hnat : IsNaturalModule L B n := hnatural.1 ▸ hnatural.2.1
  have hNL := hE.normalizer_le.trans
    ((normal_subgroupOf_iff_le_normalizer h.L_le).mp h.L_normal)
  have hA'N : A' ≤ normalizer (B : Set G) := fusion_inverse_normalizes hBA
  have hA'non : ¬ A' ≤ centralizer (B : Set G) := fusion_inverse_noncentralizing hnon
  obtain ⟨S, hS⟩ := NaturalAction.offender_lifts_sylow (by have := h.n_gt_one; omega)
    hnat hNL (conjugate_offender_of_normalizes (by have := h.n_gt_one; omega)
      hnat hNL (natural_layer_rank_bounds h hnat hE).2.2 g⁻¹ hA'N hA'non)
  have hSN := (map_subtype_le (S : Subgroup L)).trans (normalizer_commutator_ge_right R L)
  have hfix := NaturalAction.fixed_eq_of_induced_eq hA'N hSN hS
  have hcomm := (NaturalAction.commutator_eq_of_induced_eq hA'N hSN hS).trans
    (hnat.sylow_fixed_geometry S).2
  have he : ⁅B, A'⁆ = B ⊓ centralizer (A' : Set G) := hcomm.trans hfix.symm
  have hc : Nat.card (⁅B, A'⁆ : Subgroup G) = 4 := by
    rw [hcomm, (hnat.sylow_fixed_geometry S).1, hnatural.1]
    decide
  obtain ⟨l, hl, hline⟩ := NaturalAction.sylow_line_orbit T h.sylow_normalizes_L
    (normalizer_commutator_ge_right R L) S
  have hgl : ⁅B, A'⁆ = (ZS (T : Subgroup G) L R).map (MulAut.conj l).toMonoidHom :=
    hcomm.trans hline
  have hback : A'.map (MulAut.conj g).toMonoidHom = B := by
    simpa only [A', inv_inv] using fusion_map_conj_inverse B g⁻¹
  have hm : (⁅B, A'⁆ : Subgroup G).map (MulAut.conj g).toMonoidHom =
      ⁅B.map (MulAut.conj g).toMonoidHom, B⁆ := by rw [map_commutator, hback]
  refine ⟨?_, ?_, ?_⟩
  · have hh := congrArg (Subgroup.map (MulAut.conj g).toMonoidHom) he
    rwa [hm, ← map_inf_centralizer_of_injective _ (MulAut.conj g).injective, hback] at hh
  · rw [← hm, card_map_of_injective (MulAut.conj g).injective, hc]
  · rw [← hm, hgl]
    exact conjugate_line_centralizer_le_normalizer h hnat hE hnatural.2.2.2.1 g l hl

/-- A noncommuting one-sided pair supplies the actual escaping field plane. -/
theorem local_one_sided_field_plane
    (h : Hypothesis611 KnownSimple.IsKnownSimple T L M R n)
    (hnatural : Conclusion6127 (T : Subgroup G) L M R n)
    (hE : ChapterE.Section06.HypothesisE61 KnownSimple.IsKnownSimple T M (layer L R))
    (hfactor : CentralLineNormalizerFactorization M (ZS (T : Subgroup G) L R))
    (g : G)
    (hBA : layer L R ≤ normalizer ((layer L R).map (MulAut.conj g).toMonoidHom : Set G))
    (hnon : ¬ (layer L R).map (MulAut.conj g).toMonoidHom ≤ centralizer (layer L R : Set G)) :
    let B := layer L R
    let A := B.map (MulAut.conj g).toMonoidHom
    let U := B ⊓ centralizer (A : Set G)
    Nat.card U = 4 ∧ IsInvolutoryFieldFixedSpace L M B U n ∧
      ¬ centralizer (U : Set G) ≤ normalizer (B : Set G) := by
  let := h.layer_elementary
  let B := layer L R
  let A := B.map (MulAut.conj g).toMonoidHom
  let U := B ⊓ centralizer (A : Set G)
  have hnat : IsNaturalModule L B n := hnatural.1 ▸ hnatural.2.1
  have hcor := conjugate_action_corank_eq_of_natural h hnat hE
    (natural_layer_rank_bounds h hnat hE).2.2 g⁻¹
    (fusion_inverse_normalizes hBA) (fusion_inverse_noncentralizing hnon)
  have hcor' : ChapterE.subgroupCorank B U = n := by
    simpa only [inv_inv] using (fusion_pullback_corank B g⁻¹).trans hcor
  have hc : Nat.card U = 4 := by
    rw [card_eq_pow_of_half_corank inf_le_left (by simpa [Nat.mul_comm] using hnat.card) hcor', hnatural.1]
    decide
  have hAN : ¬ A ≤ normalizer (B : Set G) := by
    intro he
    exact hnon (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp
      (local_commuting_normalized h hnatural hE hfactor g hBA he)))
  have hescape : ¬ centralizer (U : Set G) ≤ normalizer (B : Set G) :=
    fun he => hAN ((le_centralizer_iff.mpr (show U ≤ centralizer (A : Set G) from inf_le_right)).trans he)
  exact ⟨hc, local_escaping_plane_field h hnatural hE inf_le_left hc hescape, hescape⟩

/-- The literal closure, commutator, and layer intersection in the contrary branch. -/
theorem local_one_sided_closure_geometry
    (h : Hypothesis611 KnownSimple.IsKnownSimple T L M R n)
    (hnatural : Conclusion6127 (T : Subgroup G) L M R n)
    (hE : ChapterE.Section06.HypothesisE61 KnownSimple.IsKnownSimple T M (layer L R))
    (hfactor : CentralLineNormalizerFactorization M (ZS (T : Subgroup G) L R))
    (g : G)
    (hBA : layer L R ≤ normalizer ((layer L R).map (MulAut.conj g).toMonoidHom : Set G))
    (hnon : ¬ (layer L R).map (MulAut.conj g).toMonoidHom ≤ centralizer (layer L R : Set G)) :
    let B := layer L R
    let A := B.map (MulAut.conj g).toMonoidHom
    let U := B ⊓ centralizer (A : Set G)
    let H := centralizer (U : Set G)
    let J := conjugateSpanBy B H
    let F := ⁅A, B⁆
    Nat.card U = 4 ∧ IsInvolutoryFieldFixedSpace L M B U n ∧
      IsElementaryAbelian 2 J ∧ J ≤ H.pCoreIn 2 ∧
      Nat.card F = 4 ∧ F = A ⊓ centralizer (B : Set G) ∧
      F ≤ J ∧ J ≤ normalizer (A : Set G) ∧
      ⁅A, J⁆ = F ∧ A ⊓ J = F := by
  let := h.layer_elementary
  let B := layer L R
  let A := B.map (MulAut.conj g).toMonoidHom
  let U := B ⊓ centralizer (A : Set G)
  let H := centralizer (U : Set G)
  let J := conjugateSpanBy B H
  let F := ⁅A, B⁆
  let : IsElementaryAbelian 2 A := IsElementaryAbelian.map _
  have hnat : IsNaturalModule L B n := hnatural.1 ▸ hnatural.2.1
  obtain ⟨hUc, hfield, hescape⟩ := local_one_sided_field_plane h hnatural hE hfactor g hBA hnon
  obtain ⟨hfixed, hFc, hFN⟩ := one_sided_line_geometry h hnatural hE g hBA hnon
  let hJe := local_plane_closure_elementary h hnatural hE hfactor (show U ≤ B from inf_le_left) hUc.ge
  let : IsElementaryAbelian 2 J := hJe
  have hBJ : B ≤ J := le_conjugateSpanBy _ _
  have hAH : A ≤ H := le_centralizer_iff.mpr inf_le_right
  have hAJ : A ≤ normalizer (J : Set G) := hAH.trans (le_normalizer_conjugateSpanBy _ _)
  have hFJ : F ≤ J := (commutator_mono le_rfl hBJ).trans (le_normalizer_iff_commutator_le_right.mp hAJ)
  have hJN : J ≤ normalizer (A : Set G) :=
    (J.le_centralizer.trans (centralizer_le hFJ)).trans hFN
  have hJcore : J ≤ H.pCoreIn 2 :=
    conjugateSpanBy_le (local_field_plane_core h hnat hE hfield (by
      intro he; rw [he, card_bot] at hUc; omega)).1
      (H.le_normalizer.trans (normalizer_le_normalizer_characteristic_image H (pCore 2 H)))
  let J' := J.map (MulAut.conj g⁻¹).toMonoidHom
  let : IsElementaryAbelian 2 J' := IsElementaryAbelian.map _
  have hJ'N : J' ≤ normalizer (B : Set G) := by
    have hh := map_mono (f := (MulAut.conj g⁻¹).toMonoidHom) hJN
    rwa [map_equiv_normalizer_eq, fusion_map_conj_inverse] at hh
  have he := elementary_extension_same_action h hnatural hE g⁻¹ J' hJ'N
    (map_mono hBJ) (fusion_inverse_noncentralizing hnon)
  have hcomm := NaturalAction.commutator_eq_of_induced_eq hJ'N
    (fusion_inverse_normalizes hBA) he
  have hJ'back : J'.map (MulAut.conj g).toMonoidHom = J := by
    simpa only [J', inv_inv] using fusion_map_conj_inverse J g⁻¹
  have hB'back : (B.map (MulAut.conj g⁻¹).toMonoidHom).map
      (MulAut.conj g).toMonoidHom = B := by
    simpa only [inv_inv] using fusion_map_conj_inverse B g⁻¹
  have hcomm' : ⁅A, J⁆ = F := by
    have hh := congrArg (Subgroup.map (MulAut.conj g).toMonoidHom) hcomm
    rwa [map_commutator B J', map_commutator B (B.map (MulAut.conj g⁻¹).toMonoidHom), hJ'back, hB'back] at hh
  have hmeet : A ⊓ J = F := by
    apply le_antisymm _ (le_inf (hfixed.le.trans inf_le_left) hFJ)
    rw [hfixed]
    exact le_inf inf_le_left (inf_le_right.trans (J.le_centralizer.trans (centralizer_le hBJ)))
  exact ⟨hUc, hfield, hJe, hJcore, hFc, hfixed, hFJ, hJN, hcomm', hmeet⟩

/-- The normalizer intersection is exactly the central-type commutator plane. -/
theorem local_one_sided_normalizer
    (h : Hypothesis611 KnownSimple.IsKnownSimple T L M R n)
    (hnatural : Conclusion6127 (T : Subgroup G) L M R n)
    (hE : ChapterE.Section06.HypothesisE61 KnownSimple.IsKnownSimple T M (layer L R))
    (hfactor : CentralLineNormalizerFactorization M (ZS (T : Subgroup G) L R))
    (g : G)
    (hBA : layer L R ≤ normalizer ((layer L R).map (MulAut.conj g).toMonoidHom : Set G))
    (hnon : ¬ (layer L R).map (MulAut.conj g).toMonoidHom ≤ centralizer (layer L R : Set G)) :
    (layer L R).map (MulAut.conj g).toMonoidHom ⊓ normalizer (layer L R : Set G) =
      ⁅(layer L R).map (MulAut.conj g).toMonoidHom, layer L R⁆ := by
  let := h.layer_elementary
  let B := layer L R
  let A := B.map (MulAut.conj g).toMonoidHom
  let : IsElementaryAbelian 2 A := IsElementaryAbelian.map _
  have hnat : IsNaturalModule L B n := hnatural.1 ▸ hnatural.2.1
  have hs := (natural_layer_rank_bounds h hnat hE).2.2
  have hsmall : Nat.card (B ⊓ A : Subgroup G) < 4 := by
    by_contra hn
    exact hnon (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp
      (local_commuting_noncyclic h hnatural hE hfactor g (Nat.le_of_not_gt hn))))
  obtain ⟨hfixed, _, _⟩ := one_sided_line_geometry h hnatural hE g hBA hnon
  rw [hfixed]
  apply le_antisymm _ (inf_le_inf_left _ (Subgroup.centralizer_le_normalizer _))
  intro a ha
  have hi := centralizer_relIndex_le_card_of_abelian_commutator B B (B ⊓ A)
    le_rfl a ha.2 (by
      intro b hb
      exact ⟨(le_normalizer_iff_commutator_le_left.mp (zpowers_le.mpr ha.2))
        (commutator_mem_commutator hb (mem_zpowers a)),
        (le_normalizer_iff_commutator_le_right.mp hBA)
        (commutator_mem_commutator hb ha.1)⟩)
  have hcor : ChapterE.subgroupCorank B (B ⊓ centralizer ({a} : Set G)) < n := by
    rw [hnatural.1]
    unfold ChapterE.subgroupCorank
    rw [inf_relIndex_left]
    exact (Nat.log_lt_iff_lt_pow (by decide)
      ((centralizer ({a} : Set G)).subgroupOf B).index_ne_zero_of_finite).mpr
      (hi.trans_lt hsmall)
  have he := ChapterE.centralizer_inf_eq_of_corank_lt_globalS
    (show B ⊓ centralizer ({a} : Set G) ≤ B from inf_le_left)
    (show (ChapterE.subgroupCorank B (B ⊓ centralizer ({a} : Set G)) : ℕ∞) < ChapterE.globalS B from by
      rw [hs]; exact_mod_cast hcor) (IsElementaryAbelian.isPGroup 2 A)
  exact ⟨ha.1, (he.le ⟨ha.1, fun b hb => mem_centralizer_singleton_iff.mp hb.2⟩).2⟩

/-- The conjugate layer has kernel F and image of order four on J/U. -/
theorem local_one_sided_quotient_kernel
    (h : Hypothesis611 KnownSimple.IsKnownSimple T L M R n)
    (hnatural : Conclusion6127 (T : Subgroup G) L M R n)
    (hE : ChapterE.Section06.HypothesisE61 KnownSimple.IsKnownSimple T M (layer L R))
    (hfactor : CentralLineNormalizerFactorization M (ZS (T : Subgroup G) L R))
    (g : G)
    (hBA : layer L R ≤ normalizer ((layer L R).map (MulAut.conj g).toMonoidHom : Set G))
    (hnon : ¬ (layer L R).map (MulAut.conj g).toMonoidHom ≤ centralizer (layer L R : Set G)) :
    let B := layer L R
    let A := B.map (MulAut.conj g).toMonoidHom
    let U := B ⊓ centralizer (A : Set G)
    let H := centralizer (U : Set G)
    let J := conjugateSpanBy B H
    A ⊓ commutatorPreimage H J U = ⁅A, B⁆ ∧
      (commutatorPreimage H J U).relIndex A = 4 := by
  let B := layer L R
  let A := B.map (MulAut.conj g).toMonoidHom
  let U := B ⊓ centralizer (A : Set G)
  let H := centralizer (U : Set G)
  let J := conjugateSpanBy B H
  let F := ⁅A, B⁆
  let K := commutatorPreimage H J U
  obtain ⟨_, _, hJe, _, hFc, hfix, hFJ, _, _, _⟩ :=
    local_one_sided_closure_geometry h hnatural hE hfactor g hBA hnon
  let : IsElementaryAbelian 2 J := hJe
  have hBJ : B ≤ J := le_conjugateSpanBy _ _
  have hAH : A ≤ H := le_centralizer_iff.mpr inf_le_right
  have hFA : F ≤ A := hfix.le.trans inf_le_left
  have hKN : K ≤ normalizer (B : Set G) := by
    apply le_normalizer_iff_commutator_le_left.mpr
    rw [commutator_comm]
    exact ((commutator_mono le_rfl hBJ).trans
      (commutator_commutatorPreimage_le H J U (Subgroup.centralizer_le_normalizer _))).trans inf_le_left
  have he : A ⊓ K = F := by
    apply le_antisymm
    · exact (inf_le_inf_left _ hKN).trans_eq
        (local_one_sided_normalizer h hnatural hE hfactor g hBA hnon)
    · apply le_inf hFA
      apply le_commutatorPreimage (hFA.trans hAH)
      rw [commutator_eq_bot_iff_le_centralizer.mpr (hFJ.trans J.le_centralizer)]
      exact bot_le
  refine ⟨he, ?_⟩
  rw [← inf_relIndex_right, inf_comm K A, he]
  have hc := (F.subgroupOf A).card_mul_index
  rw [Nat.card_congr (subgroupOfEquivOfLe hFA).toEquiv, hFc,
    card_map_of_injective (MulAut.conj g).injective, hnatural.2.1.card] at hc
  change 4 * F.relIndex A = 2 ^ (2 * 2) at hc
  change F.relIndex A = 4
  omega

/-- The original layer fills the action of its centralizer closure on A;
the closure has precisely four cosets modulo its fixed subgroup. -/
theorem local_one_sided_closure_action_index
    (h : Hypothesis611 KnownSimple.IsKnownSimple T L M R n)
    (hnatural : Conclusion6127 (T : Subgroup G) L M R n)
    (hE : ChapterE.Section06.HypothesisE61 KnownSimple.IsKnownSimple T M (layer L R))
    (hfactor : CentralLineNormalizerFactorization M (ZS (T : Subgroup G) L R))
    (g : G)
    (hBA : layer L R ≤ normalizer ((layer L R).map (MulAut.conj g).toMonoidHom : Set G))
    (hnon : ¬ (layer L R).map (MulAut.conj g).toMonoidHom ≤ centralizer (layer L R : Set G)) :
    let B := layer L R
    let A := B.map (MulAut.conj g).toMonoidHom
    let U := B ⊓ centralizer (A : Set G)
    (centralizer (A : Set G)).relIndex (conjugateSpanBy B (centralizer (U : Set G))) = 4 := by
  let B := layer L R
  let A := B.map (MulAut.conj g).toMonoidHom
  let U := B ⊓ centralizer (A : Set G)
  let J := conjugateSpanBy B (centralizer (U : Set G))
  let J' := J.map (MulAut.conj g⁻¹).toMonoidHom
  let A' := B.map (MulAut.conj g⁻¹).toMonoidHom
  obtain ⟨_, _, hJe, _, _, _, _, hJN, _, _⟩ :=
    local_one_sided_closure_geometry h hnatural hE hfactor g hBA hnon
  let := h.layer_elementary
  let : IsElementaryAbelian 2 J := hJe
  let : IsElementaryAbelian 2 J' := IsElementaryAbelian.map _
  have hBJ : B ≤ J := le_conjugateSpanBy _ _
  have hJ'N : J' ≤ normalizer (B : Set G) := by
    have hh := map_mono (f := (MulAut.conj g⁻¹).toMonoidHom) hJN
    rwa [map_equiv_normalizer_eq, fusion_map_conj_inverse] at hh
  have he := elementary_extension_same_action h hnatural hE g⁻¹ J' hJ'N
    (map_mono hBJ) (fusion_inverse_noncentralizing hnon)
  have hnat : IsNaturalModule L B n := hnatural.1 ▸ hnatural.2.1
  have hcor : ChapterE.subgroupCorank J' (J' ⊓ centralizer (B : Set G)) = n := by
    rw [← ChapterE.rank_inducedAutomizer B J' hJ'N, he,
      ChapterE.rank_inducedAutomizer B A' (fusion_inverse_normalizes hBA)]
    exact conjugate_action_corank_eq_of_natural h hnat hE
      (natural_layer_rank_bounds h hnat hE).2.2 g⁻¹
      (fusion_inverse_normalizes hBA) (fusion_inverse_noncentralizing hnon)
  have hi : (centralizer (B : Set G)).relIndex J' = 4 := by
    rw [← inf_relIndex_left]
    have hp := J'.relIndex_eq_two_pow_quotient_finrank (J' ⊓ centralizer (B : Set G))
    rw [← ChapterE.subgroupCorank_eq_quotient_finrank, hcor, hnatural.1] at hp
    exact hp
  have ht := relIndex_map_map_of_injective (centralizer (A : Set G)) J
    (f := (MulAut.conj g⁻¹).toMonoidHom) (MulAut.conj g⁻¹).injective
  rw [Theory.Quasithin.map_centralizer, fusion_map_conj_inverse] at ht
  exact ht.symm.trans hi

end CFSG.Quasithin.Chapter6.Source.RankOneRecognition
