module
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.OddNormalizer.Quintic.ComponentContract
public import CFSG.Quasithin.ChapterC.Section02.SourceExtraction.C27.StarModels
public import Theory.GroupTheory.PrimeRankZero

/-!
# The literal inputs to the two component comparisons in 14.6.15

Order-five generation supplies an escaping generator when K₁ is not in J.
In the other branch it proves that J has five-rank one, so the extraction
identity makes J normal in N_G(K₂). This supplies the original C.2.7 input
and its checked star-model catalogue, keeping the core and action quotients
distinct. No marked parabolic classification is asserted here.

Source: Aschbacher--Smith, 14.6.15, printed p.1035; C.2.7, pp.145--147.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section06.OddNormalizer.Quintic.ComponentExclusion
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open Chapter15.Section03.AbelianAmalgam
open Chapter15.Section03.AbelianAmalgam.GenerationOne
open Chapter1.RadicalExclusions.ModelReduction FullSieve FullSieve.SourceInterface
variable {G : Type*} [Group G] [Finite G]

section Generators
variable {T Mc H H1 H2 U Z W1 W2 : Subgroup G} {g : G}
    (d : NormalizerGeometry T Mc H H1 H2 U Z W1 W2 g)
    (j : EscapingComponent Mc (residualClosure H Mc) d.K1 d.K2 (Mc.pCoreIn 2))

omit [Finite G] in
/-- The exchanged first factor is nontrivial. -/
theorem first_ne_bot : d.K1 ≠ ⊥ := by
  intro hb
  obtain ⟨s,_,hs,_⟩ := d.exchanged
  apply hs
  rw [hb]
  rw [normalizer_eq_top]
  exact mem_top s

omit [Finite G] in
/-- This uses the literal order-five generators, without choosing a model. -/
theorem exists_first_generator : ∃ k ∈ d.K1, orderOf k = 5 := by
  by_contra! hn
  apply first_ne_bot d
  rw [←d.first_generated]
  apply bot_unique
  apply (closure_le _).mpr
  rintro k ⟨hk,ho⟩
  exact (hn k hk ho).elim

omit [Finite G] in
/-- The contrary branch supplies an actual generator outside the component. -/
theorem exists_first_generator_outside (h : ¬d.K1 ≤ j.J) :
    ∃ k ∈ d.K1, orderOf k = 5 ∧ k ∉ j.J := by
  by_contra! hn
  apply h
  exact d.first_generated.ge.trans ((closure_le _).mpr (fun k hk => hn k hk.1 hk.2))

omit [Finite G] in
/-- K₁ normalizes this same component through K_z. -/
theorem first_normalizes_component : d.K1 ≤ normalizer (j.J : Set G) :=
  (show d.K1 ≤ residualClosure H Mc from d.join_eq ▸ le_sup_left).trans
    j.normalized_by_closure

/-- In the contained branch a five-element forces the asserted rank bound
to be an equality. -/
theorem rank_one (h : d.K1 ≤ j.J) : primeRank 5 j.J = 1 := by
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  obtain ⟨k,hk,ho⟩ := exists_first_generator d
  have hd : 5 ∣ Nat.card j.J := by
    have he : orderOf (⟨k,h hk⟩ : j.J) = 5 := (Subgroup.orderOf_coe _).symm.trans ho
    exact he ▸ orderOf_dvd_natCard (⟨k,h hk⟩ : j.J)
  have hn : primeRank 5 j.J ≠ 0 :=
    fun hz => PrimeRank.eq_zero_iff_not_dvd_card.mp hz hd
  exact Nat.le_antisymm j.quintic_rank (Nat.one_le_iff_ne_zero.mpr hn)

/-- Normality is relative to G₂, as in the source. -/
theorem relative_normal (h : d.K1 ≤ j.J) :
    (j.J.subgroupOf (normalizer (d.K2 : Set G))).Normal :=
  (j.rank_one_identification (rank_one d j h)).2

/-- The residual identity also places J in the actual centralizer of K₂. -/
theorem centralizes_second (h : d.K1 ≤ j.J) :
    j.J ≤ centralizer (d.K2 : Set G) := by
  rw [(j.rank_one_identification (rank_one d j h)).1]
  exact (map_subtype_le _).trans inf_le_right

end Generators

variable (T : Sylow 2 G) (M Mc H H0 H1 H2 : Subgroup G)
    [IsElementaryAbelian 2 (conjugateSpanBy (localModule T M) H)]
    (a : LocalQuotientAction H (conjugateSpanBy (localModule T M) H) (centralInvolutions T))

local instance : IsElementaryAbelian 2
    (ChapterF.Section09.Setup.UH
      ⟨T,sourceResidual M Mc,localModule T M,localModule T M,centralInvolutions T,H⟩) :=
  inferInstanceAs (IsElementaryAbelian 2 (conjugateSpanBy (localModule T M) H))

/-- The unchanged rank-two prefix and the literal earlier-source inputs.
Geometry and the escaping component are supplied separately. None of the
two terminal model comparisons is a field of this context. -/
structure Context where
  ambient : IsSimpleQTKE KnownSimple.IsKnownSimple G
  empty : MainForward.faithfulLocalComponents T = ∅
  maximal : IsOrderingMaximal T M
  unique : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc}
  many : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard
  module_card : Nat.card (localModule T M) = 4
  action : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3)
  abelian : IsMulCommutative (conjugateSpanBy (localModule T M) Mc)
  outside : H ∈ Chapter1.HOutside G (T : Set G) (M : Set G)
  primitive : PrimitiveResidual H 5
  maximal_prime : MaximalOddPrime (T : Subgroup G) M 5
  factors : ExchangedFactorSetup a (T : Subgroup G) 5 H0 H1 H2
  alternatives : SourceClosureAlternatives (T : Subgroup G) Mc H 5
  critical : CriticalPair
    (source_rankTwo_f9_hypothesis ambient T empty maximal unique many module_card action
      abelian H outside) a Mc H1

variable {T M Mc H H0 H1 H2 a}
    (s : Context T M Mc H H0 H1 H2 a)
    (d : NormalizerGeometry (T : Subgroup G) Mc H H1 H2
      (conjugateSpanBy (localModule T M) Mc) (centralInvolutions T)
      (firstSupport a H1) (firstSupport a H2) s.critical.endpoint.representative)
    (j : EscapingComponent Mc (residualClosure H Mc) d.K1 d.K2 (Mc.pCoreIn 2))

/-- The original subgroup B uses the Q₁-conjugate span, not JQ₁. -/
noncomputable def borelIntersection : Subgroup G :=
  conjugateSpanBy j.J (Mc.pCoreIn 2) ⊓ (Mc ⊓ normalizer (d.K2 : Set G))

/-- Construct C.2.7 only in the branch in which Q₁ normalizes J. -/
theorem normalized_input (hn : Mc.pCoreIn 2 ≤ normalizer (j.J : Set G)) :
    Input KnownSimple.IsKnownSimple (normalizer (d.K2 : Set G)) (Mc.pCoreIn 2)
      (Mc ⊓ normalizer (d.K2 : Set G)) j.J := by
  have hs := (source_secondNormalizer_setup s.ambient T s.empty s.maximal s.unique
    s.many s.module_card s.action s.abelian H s.outside a H1 H2 s.critical d).2.2
  exact ⟨hs,⟨j.component_le,j.component⟩,j.quasisimple,
    j.characteristic_component,j.outside,hn⟩

/-- Containment of K₁ supplies normalization by Q₁ from relative normality. -/
theorem radical_normalizes (h : d.K1 ≤ j.J) :
    Mc.pCoreIn 2 ≤ normalizer (j.J : Set G) := by
  let := relative_normal d j h
  have hs := (source_secondNormalizer_setup s.ambient T s.empty s.maximal s.unique
    s.many s.module_card s.action s.abelian H s.outside a H1 H2 s.critical d).2.2
  exact hs.radical_le.trans (le_normalizer_of_normal_subgroupOf j.component_le)

/-- The full original C.2.7 input in the contained branch. -/
theorem contained_input (h : d.K1 ≤ j.J) :
    Input KnownSimple.IsKnownSimple (normalizer (d.K2 : Set G)) (Mc.pCoreIn 2)
      (Mc ⊓ normalizer (d.K2 : Set G)) j.J :=
  normalized_input s d j (radical_normalizes s d j h)

/-- Once normality is established, the actual Q₁-conjugate span is J. -/
theorem contained_span (h : d.K1 ≤ j.J) :
    conjugateSpanBy j.J (Mc.pCoreIn 2) = j.J :=
  le_antisymm (conjugateSpanBy_le le_rfl (radical_normalizes s d j h))
    (le_conjugateSpanBy _ _)

/-- This identifies the literal source B with the C.2.7 intersection. -/
theorem contained_intersection (h : d.K1 ≤ j.J) :
    borelIntersection s d j = j.J ⊓ Mc := by
  rw [borelIntersection,contained_span s d j h]
  exact le_antisymm (inf_le_inf_left _ inf_le_left)
    (fun x hx => ⟨hx.1,hx.2,j.component_le hx.1⟩)

/-- The checked group catalogue concerns the star image, not J/O₂(J). -/
theorem contained_star_model (h : d.K1 ≤ j.J) :
    ChapterC.C27Source.StarModels.Model (starImage j.J (Mc.pCoreIn 2) j.J) :=
  ChapterC.C27Source.star_model_from_source (contained_input s d j h)

/-- The genuine comparison from the core quotient to the action quotient
has central kernel, of order prime to five. -/
theorem contained_comparison_kernel (h : d.K1 ≤ j.J) :
    (coreToStar (radical_normalizes s d j h)).ker ≤ center (j.J ⧸ pCore 2 j.J) ∧
      ¬5 ∣ Nat.card (coreToStar (radical_normalizes s d j h)).ker := by
  exact ⟨ChapterC.C27Source.coreToStar_ker_central_from_source (contained_input s d j h),
    ChapterC.C27Source.coreToStar_ker_not_five_from_source (contained_input s d j h)⟩

include s in
/-- The source's G₁ is the centralizer of the same central involutions. -/
theorem partner_eq_centralizer : Mc = centralizer (centralInvolutions T : Set G) :=
  (source_lemma_14_1_18 s.ambient T s.empty s.maximal s.unique s.many
    s.module_card s.action).2.2.2.2.2.2.2.2.2.2.2.2.2.1

include s in
/-- The abelian Mc-span is a normal two-subgroup of Mc. Thus the original
H-span lies in Q₁, a fact needed for the literal Z ≤ B at the endpoint. -/
theorem original_module_le_radical :
    conjugateSpanBy (localModule T M) H ≤ Mc.pCoreIn 2 := by
  have hHMc : H ≤ Mc := by
    have he := (Section02.source_lemma_14_2_3 s.ambient T s.empty s.maximal s.unique
      s.many s.module_card s.action H s.outside.1 s.outside.2).1
    exact (show Mc ∈ maximalTwoLocalOvergroups H from he ▸ Set.mem_singleton Mc).2
  have hrank := Section02.source_lemma_14_2_4 s.ambient T s.empty s.maximal s.unique
    s.many s.module_card s.action
  have hVT : localModule T M ≤ (T : Subgroup G) := by
    simpa only [Section02.rankTwoSeed_eq_localModule] using hrank.seed_le_sylow
  have hTMc : (T : Subgroup G) ≤ Mc := by
    rw [partner_eq_centralizer s]
    exact le_centralizer_iff.mp (centralInvolutions_le_centralizer_sylow T)
  let : IsElementaryAbelian 2 (localModule T M) :=
    IsElementaryAbelian.of_le (le_conjugateSpanBy (localModule T M) H)
  let : IsMulCommutative (conjugateSpanBy (localModule T M) Mc) := s.abelian
  let : IsElementaryAbelian 2 (conjugateSpanBy (localModule T M) Mc) :=
    ModuleBound.span_elementary _ _
  exact (conjugateSpanBy_mono le_rfl hHMc).trans
    (le_pCoreIn_of_normalizes (IsElementaryAbelian.isPGroup 2 _)
      (conjugateSpanBy_le_self (hVT.trans hTMc)) (le_normalizer_conjugateSpanBy _ _))

/-- In the contained branch, the 14.6.12 commutator puts Z inside J,
and hence inside the literal intersection B. -/
theorem point_le_intersection (h : d.K1 ≤ j.J) :
    centralInvolutions T ≤ borelIntersection s d j := by
  have hZJ : centralInvolutions T ≤ j.J := by
    apply s.factors.point_first.trans
    exact (commutator_mono (original_module_le_radical s)
      (d.residual_first_le.trans h)).trans
        (le_normalizer_iff_commutator_le_right.mp (radical_normalizes s d j h))
  rw [contained_intersection s d j h]
  exact le_inf hZJ (a.kernel_le.trans
    ((original_module_le_radical s).trans (pCoreIn_le 2 Mc)))

/-- Every element of Z centralizes the actual B, so Z lies in its center. -/
theorem point_le_intersection_center (h : d.K1 ≤ j.J) :
    centralInvolutions T ≤ (center (borelIntersection s d j)).map
      (borelIntersection s d j).subtype := by
  have hBZ : borelIntersection s d j ≤ centralizer (centralInvolutions T : Set G) :=
    (inf_le_right.trans inf_le_left).trans_eq (partner_eq_centralizer s)
  intro z hz
  refine ⟨⟨z,point_le_intersection s d j h hz⟩,mem_center_iff.mpr ?_,rfl⟩
  intro x
  exact Subtype.ext ((le_centralizer_iff.mp hBZ hz) x x.property)

end CFSG.Quasithin.Chapter14.Section06.OddNormalizer.Quintic.ComponentExclusion
