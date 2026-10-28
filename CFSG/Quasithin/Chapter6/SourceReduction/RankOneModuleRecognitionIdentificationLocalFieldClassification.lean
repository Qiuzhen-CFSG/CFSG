module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionIdentificationLocalFieldReduced
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.ComponentPlaneComplete
public import Theory.Representation.BinaryConjugationSection.QuadraticCommutator
public import Theory.Representation.BinaryConjugationSection.CommutatorImage
public import Theory.Representation.BinaryConjugationSection.FixedIndex

/-!
# Classification on the literal field-plane quotient

In the contrary one-sided configuration, the actual commutator plane maps
onto the whole moved space of the conjugate four-group. The action is
quadratic. The exact image order gives two cases: a trivial intersection
with the field plane and a moved plane, or an intersection of order two
and a moved line. In the disjoint case, the literal commutator preimage
identifies the fixed space and gives fixed codimension exactly two. Every nontrivial
subgroup of the original four-group has the same fixed space, making
that four-group itself a minimal best offender.

An involution of the original field plane supplies the SQTK cover of its
centralizer. Reducedness gives trivial two-core in the faithful action.
The complete adequate B.5 theorem therefore classifies its actual normal
best-offender subgroup. Replacement selects a minimal best offender inside
the original four-group; the same whole-moved bound supplies Irr+ and the
small actor catalogue for every component moved by that seed.

The companion Chapter 12 module applies all of this to the original
commutator layer. The cubic-action exclusions of these alternatives and
the subsequent graph escape remain part of the local-analysis proof.

Source: Aschbacher--Smith, 6.2.7, printed pp.682--683; B.1.4, pp.68--69;
B.5.1--6, pp.99--105, with the adequate outer-six-three convention.
-/

public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped commutatorElement IsMulCommutative
open CFSG.Quasithin.ChapterB.QuasisimpleSource CFSG.Quasithin.ChapterB.SourceInduction
namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition.LocalFieldQuotientAction
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L M R : Subgroup G} {n : ℕ}

private theorem field_centralizer_sqtk
    (h : Hypothesis611 KnownSimple.IsKnownSimple T L M R n)
    {U : Subgroup G} (hUB : U ≤ layer L R) (hUne : U ≠ ⊥) :
    IsSQTK KnownSimple.IsKnownSimple (Centralizer U) := by
  let := h.layer_elementary
  obtain ⟨u, hu⟩ := ne_bot_iff_exists_ne_one.mp hUne
  have hu1 : (u : G) ≠ 1 := fun he => hu (Subtype.ext he)
  have hu2 : orderOf (u : G) = 2 := orderOf_eq_prime
    (elemPow_eq_one_of_isElementaryAbelian (p := 2) (u : G) (hUB u.property)) hu1
  let C := centralizer ({(u : G)} : Set G)
  have hHC : Centralizer U ≤ C := centralizer_le (Set.singleton_subset_iff.mpr u.property)
  let j := inclusion hHC
  have hs := h.simpleQTKE.involution_centralizer_sqtk hu2
  exact ⟨hs.stronglyQuasithin.of_injective j (inclusion_injective hHC),
    hs.isKGroup.of_injective j (inclusion_injective hHC)⟩

omit [Finite G] in
private theorem section_image_top
    {H J U : Subgroup G} {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    {σ : Representation (ZMod 2) H W} (c : BinaryConjugationSection H J U σ) :
    c.imageSpace J = ⊤ := by
  apply top_unique
  intro w _
  obtain ⟨j, hj⟩ := c.onto (Multiplicative.ofAdd w)
  exact (c.mem_imageSpace_iff J w).mpr ⟨j, j.property, congrArg Multiplicative.toAdd hj⟩

/-- The commutator plane is exactly the moved image on the original section. -/
theorem section_plane_geometry
    (h : Hypothesis611 KnownSimple.IsKnownSimple T L M R n)
    (hnatural : Conclusion6127 (T : Subgroup G) L M R n)
    (hE : ChapterE.Section06.HypothesisE61 KnownSimple.IsKnownSimple T M (layer L R))
    (hfactor : CentralLineNormalizerFactorization M (ZS (T : Subgroup G) L R))
    (g : G)
    (hBA : layer L R ≤ normalizer ((layer L R).map (MulAut.conj g).toMonoidHom : Set G))
    (hnon : ¬ (layer L R).map (MulAut.conj g).toMonoidHom ≤ centralizer (layer L R : Set G))
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W] [Finite W]
    (ρ : Representation (ZMod 2) (action (layer L R)
      (layer L R ⊓ centralizer ((layer L R).map (MulAut.conj g).toMonoidHom : Set G))).range W)
    (c : BinaryConjugationSection
      (Centralizer (layer L R ⊓ centralizer ((layer L R).map (MulAut.conj g).toMonoidHom : Set G)))
      (conjugateSpanBy (layer L R)
        (Centralizer (layer L R ⊓ centralizer ((layer L R).map (MulAut.conj g).toMonoidHom : Set G))))
      (layer L R ⊓ centralizer ((layer L R).map (MulAut.conj g).toMonoidHom : Set G))
      (ρ.comp (action (layer L R)
        (layer L R ⊓ centralizer ((layer L R).map (MulAut.conj g).toMonoidHom : Set G))).rangeRestrict)) :
    let B := layer L R
    let A := B.map (MulAut.conj g).toMonoidHom
    let U := B ⊓ centralizer (A : Set G)
    let I := (A.subgroupOf (Centralizer U)).map (action B U).rangeRestrict
    IsQuadratic ρ I ∧ moved ρ I = c.imageSpace ⁅A,B⁆ ∧
      Module.finrank (ZMod 2) (moved ρ I) ≤ 2 ∧
      Nat.card (U ⊓ ⁅A,B⁆ : Subgroup G) * 2 ^ Module.finrank (ZMod 2) (moved ρ I) = 4 ∧
      ((U ⊓ ⁅A,B⁆ = ⊥ ∧ Module.finrank (ZMod 2) (moved ρ I) = 2) ∨
        (Nat.card (U ⊓ ⁅A,B⁆ : Subgroup G) = 2 ∧
          Module.finrank (ZMod 2) (moved ρ I) = 1)) ∧
      (U ⊓ ⁅A,B⁆ = ⊥ → fixedCodim ρ I = 2) := by
  let B := layer L R
  let A := B.map (MulAut.conj g).toMonoidHom
  let U := B ⊓ centralizer (A : Set G)
  let H := Centralizer U
  let J := conjugateSpanBy B H
  let F := ⁅A,B⁆
  let π := (action B U).rangeRestrict
  let I := (A.subgroupOf H).map π
  obtain ⟨_, _, hJe, _, hFc, hFA, hFJ, _, hcomm, _⟩ :=
    local_one_sided_closure_geometry h hnatural hE hfactor g hBA hnon
  change Nat.card F = 4 at hFc
  change ⁅A, J⁆ = F at hcomm
  let := h.layer_elementary
  let : IsElementaryAbelian 2 A := IsElementaryAbelian.map _
  have hAH : A ≤ H := le_centralizer_iff.mpr inf_le_right
  have hAF : ⁅A,F⁆ = ⊥ := commutator_eq_bot_iff_le_centralizer.mpr
    (le_centralizer_iff.mp ((hFA.le.trans inf_le_left).trans A.le_centralizer))
  have hm : moved ρ I = c.imageSpace F := by
    rw [show F = ⁅A,J⁆ from hcomm.symm, c.imageSpace_commutator A J hAH le_rfl,
      section_image_top c, subspaceCommutator_comp_map]
  have hd : Module.finrank (ZMod 2) (moved ρ I) ≤ 2 := by
    rw [hm]
    have hc : Nat.card (c.imageSpace F) ≤ 4 := by
      rw [c.imageSpace_card_eq_relIndex F hFJ]
      exact (Nat.le_of_dvd (Nat.card_pos (α := F)) (relIndex_dvd_card U F)).trans_eq hFc
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod] at hc
    exact (Nat.pow_le_pow_iff_right (by decide : 1 < (2 : ℕ))).mp hc
  have hi := relIndex_mul_relIndex (⊥ : Subgroup G) (U ⊓ F) F bot_le inf_le_right
  simp only [relIndex_bot_left, inf_relIndex_right] at hi
  rw [← c.imageSpace_card_eq_relIndex F hFJ, ← hm,
    Module.natCard_eq_pow_finrank (K := ZMod 2) (V := moved ρ I), Nat.card_zmod, hFc] at hi
  have hsmall : Nat.card (U ⊓ F : Subgroup G) < 4 := by
    have hle : U ⊓ F ≤ B ⊓ A := le_inf
      (inf_le_left.trans inf_le_left) (inf_le_right.trans (hFA.le.trans inf_le_left))
    by_contra hn
    have hc := local_commuting_noncyclic h hnatural hE hfactor g
      ((Nat.le_of_not_gt hn).trans (card_le_of_le hle))
    exact hnon (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hc))
  have hcodim (hdis : U ⊓ F = ⊥) : fixedCodim ρ I = 2 := by
    let C := J ⊓ centralizer (A : Set G)
    have hJU : J ≤ normalizer (U : Set G) :=
      c.section_le.trans (Subgroup.centralizer_le_normalizer _)
    have hpre : commutatorPreimage J A U = C := by
      apply le_antisymm
      · intro x hx
        obtain ⟨hxJ,hxU⟩ := (mem_commutatorPreimage_iff J A U hJU x).mp hx
        refine ⟨hxJ, ?_⟩
        intro a ha
        have hxF : ⁅x,a⁆ ∈ F := by
          rw [← hcomm, commutator_comm]
          exact commutator_mem_commutator hxJ ha
        have hx1 : ⁅x,a⁆ = 1 := by
          have hxI : ⁅x,a⁆ ∈ U ⊓ F := ⟨hxU a ha,hxF⟩
          simpa only [hdis,mem_bot] using hxI
        exact (commutatorElement_eq_one_iff_mul_comm.mp hx1).symm
      · apply le_commutatorPreimage inf_le_left
        rw [commutator_eq_bot_iff_le_centralizer.mpr
          (show C ≤ centralizer (A : Set G) from inf_le_right)]
        exact bot_le
    have hfixed := c.fixed_image_eq A hAH hJU
    rw [hpre, fixedSpace_comp_map] at hfixed
    have hindex : C.relIndex J = 2 ^ 2 := by
      rw [show C = J ⊓ centralizer (A : Set G) from rfl, inf_relIndex_left]
      exact local_one_sided_closure_action_index h hnatural hE hfactor g hBA hnon
    have hc := c.imageSpace_codimension_of_index C inf_le_left
      (le_inf c.kernel_le (show U ≤ centralizer (A : Set G) from inf_le_right)) 2 hindex
    rw [hfixed] at hc
    change Module.finrank (ZMod 2) (fixedSpace ρ I) + 2 = Module.finrank (ZMod 2) W at hc
    have hs := fixedCodim_add_finrank ρ I
    omega
  refine ⟨BinaryConjugationSection.isQuadratic_of_triple_commutator_le H J U A ρ π c
    (by rw [hcomm, hAF]; exact bot_le), hm, hd, hi, ?_, hcodim⟩
  have hc : Module.finrank (ZMod 2) (moved ρ I) = 0 ∨
      Module.finrank (ZMod 2) (moved ρ I) = 1 ∨
      Module.finrank (ZMod 2) (moved ρ I) = 2 := by omega
  rcases hc with he | he | he
  · rw [he] at hi
    change Nat.card (U ⊓ F : Subgroup G) * 1 = 4 at hi
    omega
  · rw [he] at hi
    change Nat.card (U ⊓ F : Subgroup G) * 2 = 4 at hi
    have hc2 : Nat.card (U ⊓ F : Subgroup G) = 2 := by omega
    exact Or.inr ⟨hc2, he⟩
  · rw [he] at hi
    change Nat.card (U ⊓ F : Subgroup G) * 4 = 4 at hi
    refine Or.inl ⟨?_, he⟩
    have hc1 : Nat.card (U ⊓ F : Subgroup G) = 1 := by omega
    exact (eq_of_le_of_card_ge (bot_le : (⊥ : Subgroup G) ≤ U ⊓ F)
      (by rw [hc1,card_bot])).symm


/-- When the planes are disjoint, every subgroup of the actual four-group
of index less than four has the same fixed space. -/
theorem fixed_family_of_disjoint
    (h : Hypothesis611 KnownSimple.IsKnownSimple T L M R n)
    (hnatural : Conclusion6127 (T : Subgroup G) L M R n)
    (hE : ChapterE.Section06.HypothesisE61 KnownSimple.IsKnownSimple T M (layer L R))
    (hfactor : CentralLineNormalizerFactorization M (ZS (T : Subgroup G) L R))
    (g : G)
    (hBA : layer L R ≤ normalizer ((layer L R).map (MulAut.conj g).toMonoidHom : Set G))
    (hnon : ¬ (layer L R).map (MulAut.conj g).toMonoidHom ≤ centralizer (layer L R : Set G))
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W] [Finite W]
    (ρ : Representation (ZMod 2) (action (layer L R)
      (layer L R ⊓ centralizer ((layer L R).map (MulAut.conj g).toMonoidHom : Set G))).range W)
    (c : BinaryConjugationSection
      (Centralizer (layer L R ⊓ centralizer ((layer L R).map (MulAut.conj g).toMonoidHom : Set G)))
      (conjugateSpanBy (layer L R)
        (Centralizer (layer L R ⊓ centralizer ((layer L R).map (MulAut.conj g).toMonoidHom : Set G))))
      (layer L R ⊓ centralizer ((layer L R).map (MulAut.conj g).toMonoidHom : Set G))
      (ρ.comp (action (layer L R)
        (layer L R ⊓ centralizer ((layer L R).map (MulAut.conj g).toMonoidHom : Set G))).rangeRestrict)) :
    let B := layer L R
    let A := B.map (MulAut.conj g).toMonoidHom
    let U := B ⊓ centralizer (A : Set G)
    let I := (A.subgroupOf (Centralizer U)).map (action B U).rangeRestrict
    U ⊓ ⁅A,B⁆ = ⊥ → IsElementaryTwo I → I ∈ ChapterE.fixedSpaceFamily ρ 2 := by
  let B := layer L R
  let A := B.map (MulAut.conj g).toMonoidHom
  let U := B ⊓ centralizer (A : Set G)
  let H := Centralizer U
  let J := conjugateSpanBy B H
  let F := ⁅A,B⁆
  let π := (action B U).rangeRestrict
  let I := (A.subgroupOf H).map π
  change U ⊓ F = ⊥ → IsElementaryTwo I → I ∈ ChapterE.fixedSpaceFamily ρ 2
  intro hdis hIe
  obtain ⟨_,_,hJe,_,_,_,_,_,hcomm,_⟩ :=
    local_one_sided_closure_geometry h hnatural hE hfactor g hBA hnon
  let := h.layer_elementary
  let : IsElementaryAbelian 2 A := IsElementaryAbelian.map _
  let : IsElementaryAbelian 2 J := hJe
  change ⁅A, J⁆ = F at hcomm
  have hAH : A ≤ H := le_centralizer_iff.mpr inf_le_right
  have hJU : J ≤ normalizer (U : Set G) :=
    c.section_le.trans (Subgroup.centralizer_le_normalizer _)
  have hpre (E : Subgroup G) (hEA : E ≤ A) :
      commutatorPreimage J E U = J ⊓ centralizer (E : Set G) := by
    apply le_antisymm
    · intro x hx
      obtain ⟨hxJ,hxU⟩ := (mem_commutatorPreimage_iff J E U hJU x).mp hx
      refine ⟨hxJ, ?_⟩
      intro a ha
      have hxF : ⁅x,a⁆ ∈ F := by
        rw [← hcomm, commutator_comm]
        exact commutator_mem_commutator hxJ (hEA ha)
      have hx1 : ⁅x,a⁆ = 1 := by
        have hxI : ⁅x,a⁆ ∈ U ⊓ F := ⟨hxU a ha,hxF⟩
        simpa only [hdis,mem_bot] using hxI
      exact (commutatorElement_eq_one_iff_mul_comm.mp hx1).symm
    · apply le_commutatorPreimage inf_le_left
      rw [commutator_eq_bot_iff_le_centralizer.mpr
        (show J ⊓ centralizer (E : Set G) ≤ centralizer (E : Set G) from inf_le_right)]
      exact bot_le
  refine ⟨by decide,hIe,?_⟩
  intro Q hQI hQidx
  let A0 := A.subgroupOf H
  let E0 := A0 ⊓ Q.comap π
  let E := E0.map H.subtype
  have hEA : E ≤ A := by
    rintro x ⟨a,ha,rfl⟩
    exact ha.1
  have hEH : E ≤ H := map_subtype_le _
  have hE0 : E.subgroupOf H = E0 := by
    change (E0.map H.subtype).comap H.subtype = E0
    rw [comap_map_eq_self_of_injective H.subtype_injective]
  have hEQ : E0.map π = Q := by
    apply le_antisymm
    · rintro q ⟨a,ha,rfl⟩
      exact ha.2
    · intro q hq
      obtain ⟨a,ha,he⟩ := hQI hq
      exact ⟨a,⟨ha,by change π a ∈ Q; rwa [he]⟩,he⟩
  have hidx : E.relIndex A = Q.relIndex I := by
    have hi := relIndex_map_map_of_injective E0 A0 H.subtype_injective
    rw [map_subgroupOf_eq_of_le hAH] at hi
    rw [hi]
    change (A0 ⊓ Q.comap π).relIndex A0 = _
    rw [inf_relIndex_left, relIndex_comap]
  have hs : ChapterE.globalS A = (2 : ℕ∞) := by
    rw [ChapterE.globalS_map_equiv]
    rw [(natural_layer_rank_bounds h (hnatural.1 ▸ hnatural.2.1) hE).2.2, hnatural.1]
    norm_num
  have hc := ChapterE.centralizer_inf_eq_of_corank_lt_globalS hEA
    (show (ChapterE.subgroupCorank A E : ℕ∞) < ChapterE.globalS A from by
      rw [hs]
      apply ENat.natCast_lt_natCast.mpr
      simpa only [ChapterE.subgroupCorank,hidx] using hQidx)
    (IsElementaryAbelian.isPGroup 2 J)
  have hfixA := c.fixed_image_eq A hAH hJU
  rw [hpre A le_rfl, fixedSpace_comp_map] at hfixA
  have hfixE := c.fixed_image_eq E hEH hJU
  rw [hpre E hEA, fixedSpace_comp_map,hE0,hEQ] at hfixE
  rw [← hfixA,← hfixE,hc]

private theorem minimal_of_four_fixed_family
    {D W : Type*} [Group D] [Finite D] [AddCommGroup W] [Module (ZMod 2) W]
    [FiniteDimensional (ZMod 2) W] (ρ : Representation (ZMod 2) D W)
    {I : Subgroup D} (hI : IsOffender ρ I) (hIc : Nat.card I = 4)
    (hfamily : I ∈ ChapterE.fixedSpaceFamily ρ 2) (hcodim : fixedCodim ρ I = 2) :
    IsMinimalBestOffender ρ I := by
  obtain ⟨Q,hQI,hQ,_,_⟩ := hI.exists_quadratic_minimalBestOffender ρ
  let : Nontrivial Q := (Subgroup.nontrivial_iff_ne_bot _).mpr hQ.1.1.1
  have hQge : 2 ≤ Nat.card Q := Finite.one_lt_card
  have hmul := (Q.subgroupOf I).card_mul_index
  rw [Nat.card_congr (subgroupOfEquivOfLe hQI).toEquiv,hIc] at hmul
  change Nat.card Q * Q.relIndex I = 4 at hmul
  have hbound := Nat.mul_le_mul_right (Q.relIndex I) hQge
  change 2 * Q.relIndex I ≤ Nat.card Q * Q.relIndex I at hbound
  rw [hmul] at hbound
  have hidx : Q.relIndex I < 4 := by omega
  have hlog : Nat.log 2 (Q.relIndex I) < 2 :=
    (Nat.log_lt_iff_lt_pow (by decide) (Q.subgroupOf I).index_ne_zero_of_finite).mpr hidx
  have hfix := hfamily.2.2 Q hQI hlog
  have hdim : fixedCodim ρ Q = 2 := by
    rw [fixedCodim, ← hfix]
    exact hcodim
  have hr : 2 ≤ rank Q := hdim ▸ (hQ.1.isOffender ρ).2
  have hcard : 4 ≤ Nat.card Q := by
    rw [hQ.1.1.card_eq_two_pow_rank]
    exact Nat.pow_le_pow_right (by decide : 1 ≤ (2 : ℕ)) hr
  have heq : Q = I := eq_of_le_of_card_ge hQI (by rw [hIc]; exact hcard)
  exact heq ▸ hQ

/-- Apply the full adequate B.5 theorem to the actual normal offender subgroup,
retaining the original conjugate image, its commutator plane, and coordinates. -/
theorem exists_classified_offender_action
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
    letI := (reduced_space h hnatural hE hfactor
      (local_one_sided_field_plane h hnatural hE hfactor g hBA hnon).2.1
      (local_one_sided_field_plane h hnatural hE hfactor g hBA hnon).1.ge).elementary
    let H := Centralizer U
    let J := conjugateSpanBy B H
    let π := (action B U).rangeRestrict
    let I := (A.subgroupOf H).map π
    ∃ (ρ : Representation (ZMod 2) (action B U).range (Additive (space B U)))
      (c : BinaryConjugationSection H J U (ρ.comp π)),
      Function.Injective ρ ∧ IsOffender ρ I ∧ IsQuadratic ρ I ∧ Nat.card I = 4 ∧
      moved ρ I = c.imageSpace ⁅A,B⁆ ∧ Module.finrank (ZMod 2) (moved ρ I) ≤ 2 ∧
      Nat.card (U ⊓ ⁅A,B⁆ : Subgroup G) * 2 ^ Module.finrank (ZMod 2) (moved ρ I) = 4 ∧
      ((U ⊓ ⁅A,B⁆ = ⊥ ∧ Module.finrank (ZMod 2) (moved ρ I) = 2) ∨
        (Nat.card (U ⊓ ⁅A,B⁆ : Subgroup G) = 2 ∧
          Module.finrank (ZMod 2) (moved ρ I) = 1)) ∧
      (U ⊓ ⁅A,B⁆ = ⊥ → fixedCodim ρ I = 2 ∧
        I ∈ ChapterE.fixedSpaceFamily ρ 2 ∧ IsMinimalBestOffender ρ I ∧
        ∀ K, IsComponent (action B U).range K → ⁅K,I⁆ = K →
          IsIrrPlus ρ K (moved ρ K) ∧ SmallMoved.ActorList K) ∧
      NontrivialAdequateAlternative (ρ.comp (offenderSubgroup ρ).subtype) ∧
      (∃ Q ≤ I, IsMinimalBestOffender ρ Q ∧ IsQuadratic ρ Q ∧
        ∀ K, IsComponent (action B U).range K → ⁅K,Q⁆ = K →
          IsIrrPlus ρ K (moved ρ K) ∧ SmallMoved.ActorList K) ∧
      ∀ j : J, ∃ hj : (j : G) ∈ H, projection U ⟨j, hj⟩ =
        ((c.coordinates j).toAdd.toMul : Ambient U) := by
  let B := layer L R
  let A := B.map (MulAut.conj g).toMonoidHom
  let U := B ⊓ centralizer (A : Set G)
  let H := Centralizer U
  let J := conjugateSpanBy B H
  obtain ⟨hUc, hfield, _⟩ := local_one_sided_field_plane h hnatural hE hfactor g hBA hnon
  let := (reduced_space h hnatural hE hfactor hfield hUc.ge).elementary
  let f := action B U
  let I := (A.subgroupOf H).map f.rangeRestrict
  obtain ⟨ρ, c, hfaith, hI, hIc, hmark⟩ :=
    exists_faithful_offender h hnatural hE hfactor g hBA hnon
  obtain ⟨hquad, hmoved, hdim, hprod, hcases, hcodim⟩ := section_plane_geometry h hnatural hE hfactor g hBA hnon ρ c
  change Nat.card U = 4 at hUc
  have hUne : U ≠ ⊥ := by intro he; rw [he,card_bot] at hUc; contradiction
  let cover : SQTKQuotient KnownSimple.IsKnownSimple f.range := {
    Cover := H
    kernel := f.ker
    sqtk := field_centralizer_sqtk h inf_le_left hUne
    equiv := QuotientGroup.quotientKerEquivRange f }
  have hcore : pCore 2 f.range = ⊥ := action_range_core h hnatural hE hfactor hfield hUc.ge
  have hN : offenderSubgroup ρ ≠ ⊥ := offenderSubgroup_ne_bot_of_ff ρ ⟨I,hI⟩
  let : Nontrivial (offenderSubgroup ρ) := (Subgroup.nontrivial_iff_ne_bot _).mpr hN
  have hclass := nontrivialAdequateAlternative_knownSimple _
    (offenderSubgroup_hypothesis ρ hfaith hcore cover)
  obtain ⟨Q,hQI,hQ,hQquad,_⟩ := hI.exists_quadratic_minimalBestOffender ρ
  have hQdim : Module.finrank (ZMod 2) (moved ρ Q) ≤ 2 := by
    apply (Submodule.finrank_mono ?_).trans hdim
    apply Submodule.span_mono
    rintro _ ⟨a,ha,v,hv,rfl⟩
    exact ⟨a,hQI ha,v,hv,rfl⟩
  refine ⟨ρ,c,hfaith,hI,hquad,hIc,hmoved,hdim,hprod,hcases,?_,hclass,?_,hmark⟩
  · intro hdis
    have hfam := fixed_family_of_disjoint h hnatural hE hfactor g hBA hnon ρ c hdis hI.1
    have hmin := minimal_of_four_fixed_family ρ hI hIc hfam (hcodim hdis)
    exact ⟨hcodim hdis,hfam,hmin,fun K hK hKI =>
      component_irrPlus_and_actor_of_minimal_plane ρ hfaith hcore cover hK hmin hKI hdim⟩
  · refine ⟨Q,hQI,hQ,hQquad,?_⟩
    intro K hK hKQ
    exact component_irrPlus_and_actor_of_minimal_plane ρ hfaith hcore cover hK hQ hKQ hQdim

end CFSG.Quasithin.Chapter6.Source.RankOneRecognition.LocalFieldQuotientAction
