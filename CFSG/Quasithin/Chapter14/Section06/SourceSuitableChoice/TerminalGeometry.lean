module
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.Factorization
public import CFSG.Quasithin.Chapter14.Section06.SourceClassificationInputs
public import Theory.GroupTheory.CrossingFusionCentralizer
public import Theory.GroupTheory.FixedFactorConjugateSpan
public import Theory.SpecificGroups.BinaryLinear.ThreePointQuotientLift
public import Theory.GroupTheory.TwoLayerCentralizer
public import Theory.GroupTheory.NonsolvableTwoLocal

/-!
# The geometry needed by the original terminal witness

The second parabolic is the full, literal centralizer of u modulo the central
line. A full binary plane action, or a binary three-space point-stabilizer
action, with two-group kernel identifies its two-core quotient with S3. The seed's fixed-factor decomposition gives rank
four for its residual span. This also proves that the parabolic escapes M.
Fusion across two noncommuting conjugate modules supplies an element of C_G(u)
outside Mc; the residual supplies escape from M.

The records below specify action maps, seed coordinates and crossing-module
geometry, not the rank or outside-family conclusions. Constructing those
inputs from the two source branches remains a separate obligation. In the
final branch this includes eliminating A6 and the two-component alternatives.

Source: Aschbacher--Smith, 14.6.17(4--5), 14.6.24(2--4), and the final
paragraph on printed p.1042. The residual throughout is O^2.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
open scoped commutatorElement
namespace CFSG.Quasithin.Chapter14.Section06
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]

/-- A marked action of the actual parabolic, with its full image and kernel. -/
structure SourcePointStabilizerAction (P : Subgroup G) where
  actor : P →* BinaryLinear.GL (Fin 3 → ZMod 2)
  point : Fin 3 → ZMod 2
  nonzero : point ≠ 0
  image : actor.range = MulAction.stabilizer (BinaryLinear.GL (Fin 3 → ZMod 2)) point
  kernel : IsPGroup 2 actor.ker

/-- The full binary plane action of the solvable second factor. -/
structure SourceBinaryPlaneAction (P : Subgroup G) where
  actor : P →* BinaryLinear.GL (Fin 2 → ZMod 2)
  surjective : Function.Surjective actor
  kernel : IsPGroup 2 actor.ker

/-- The two actual action models used in the two source endgames. -/
inductive SourceParabolicAction (P : Subgroup G) where
  | plane : SourceBinaryPlaneAction P → SourceParabolicAction P
  | point : SourcePointStabilizerAction P → SourceParabolicAction P

/-- Seed coordinates before computing the rank of its residual span.
The central factor a is independent of the eight-group W; the commutators
of the other seed factor generate W modulo the original central line. -/
structure SourceResidualSpanCoordinates (V Z R : Subgroup G) where
  W : Subgroup G
  elementary : IsElementaryAbelian 2 W
  card : Nat.card W = 8
  a : G
  b : G
  order : orderOf a = 2
  independent : a ∉ W
  seed : V = Z ⊔ zpowers (a * b)
  line : Z ≤ W
  second : b ∈ W
  normalizes : R ≤ normalizer (W : Set G)
  fixed : a ∈ centralizer (R : Set G)
  commutes : a ∈ centralizer (W : Set G)
  generated : W ≤ Z ⊔ closure {x : G | ∃ r ∈ R, x = ⁅b,r⁆}

/-- The actual crossing used by the fusion argument. A specified pair of vectors is
H-conjugate, while a conjugate of A containing u fails to commute
with A. Both original A and all its Mc-conjugates lie in the abelian span. -/
structure SourceCrossingGeometry (V H Mc : Subgroup G) (u : G) where
  A : Subgroup G
  contained : A ≤ conjugateSpanBy V Mc
  normalizes : H ≤ normalizer (A : Set G)
  g : G
  mem_conjugate : u ∈ A.map (MulAut.conj g).toMonoidHom
  matching : ∃ h ∈ H, (MulAut.conj h) u = (MulAut.conj g⁻¹) u
  crossing : ¬ A ≤ centralizer (A.map (MulAut.conj g).toMonoidHom : Set G)

theorem SourceResidualSpanCoordinates.rank_four {V Z R : Subgroup G}
    (c : SourceResidualSpanCoordinates V Z R) :
    primeRank 2 (conjugateSpanBy V R) = 4 := by
  let := c.elementary
  exact primeRank_conjugateSpanBy_fixed_factor Z V R c.W c.a c.b c.order c.independent
    c.seed c.line c.second c.normalizes c.fixed c.commutes c.generated c.card

theorem SourceParabolicAction.quotient {P : Subgroup G}
    (a : SourceParabolicAction P) :
    Nonempty ((P ⧸ pCore 2 P) ≃* Equiv.Perm (Fin 3)) := by
  cases a with
  | plane a =>
    exact BinaryLinear.PointStabilizerRank.binary_plane_quotient_of_action
      a.actor a.surjective a.kernel
  | point a =>
    exact BinaryLinear.PointStabilizerRank.three_point_quotient_of_action
      a.actor a.point a.nonzero a.image a.kernel

/-- The residual of every subgroup of the literal quotient centralizer
centralizes u itself. This is the coprime-action step in both endgames. -/
theorem suitable_parabolic_residual_centralizes
    {D : ChapterF.Section09.Setup G} (h : D.Hypothesis)
    (u : G) (hu : u ∈ D.UH) (P : Subgroup G) (hP : P ≤ h.kernel (zpowers u)) :
    (pResidual 2 P).map P.subtype ≤ centralizer ({u} : Set G) := by
  have huH : zpowers u ≤ D.H := zpowers_le.mpr (h.UH_le_H hu)
  have hPH : P ≤ D.H := fun x hx => ((h.mem_kernel_iff huH).mp (hP hx)).1
  have hc := residual_centralizes_of_two_layer P (zpowers u) D.V₁
    (IsPGroup.of_card (p := 2) (n := 1) (by simpa using h.point_card))
    (hPH.trans h.H_centralizes) (by
      rw [commutator_comm]
      exact commutator_le.mpr (fun x hx y hy =>
        ((h.mem_kernel_iff huH).mp (hP hy)).2 x hx))
  exact hc.trans (centralizer_le (Set.singleton_subset_iff.mpr (mem_zpowers u)))

variable (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hunique : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hab : IsMulCommutative (conjugateSpanBy (localModule T M) Mc))
    (H : Subgroup G) (hH : H ∈ Chapter1.HOutside G (T : Set G) (M : Set G))

include hG hempty hM hunique hmany hcard e hab H hH

omit hG hempty hM hunique hmany e hab H hH in
/-- Rank four forces the actual residual to escape M, since M preserves the
original plane of order four. In particular the whole parabolic escapes M. -/
theorem source_residual_not_le_of_span_coordinates
    (P : Subgroup G)
    (c : SourceResidualSpanCoordinates (localModule T M) (centralInvolutions T)
      ((pResidual 2 P).map P.subtype)) :
    ¬ (pResidual 2 P).map P.subtype ≤ M := by
  intro hPM
  have hMV : M ≤ normalizer (localModule T M : Set G) := by
    simpa only [Section02.rankTwoSeed_eq_localModule] using
      (Chapter12.Section08.RankTwoHypothesis.M_normalizes_seed (T := T) (M := M))
  have heq : conjugateSpanBy (localModule T M) ((pResidual 2 P).map P.subtype) =
      localModule T M :=
    le_antisymm (conjugateSpanBy_le le_rfl (hPM.trans hMV)) (le_conjugateSpanBy _ _)
  have hfour := c.rank_four
  rw [heq] at hfour
  have htwo : primeRank 2 (localModule T M) ≤ 2 := by
    apply (primeRank_le_iff_elementary_card_le _).mpr
    intro E _
    exact (card_le_card_group E).trans (by simpa using hcard.le)
  omega

/-- The complete outside-family assertion from the original crossing and
residual coordinates, including membership in the local family H. -/
theorem source_centralizer_mem_outside_of_geometry
    (u : G) (hu : u ∈ conjugateSpanBy (localModule T M) H)
    (hmove : ¬ Mc.pCoreIn 2 ≤ centralizer ({u} : Set G))
    (P : Subgroup G)
    (hP : P ≤ (source_rankTwo_f9_hypothesis hG T hempty hM hunique hmany hcard e hab H hH).kernel
      (zpowers u))
    (c : SourceResidualSpanCoordinates (localModule T M) (centralInvolutions T)
      ((pResidual 2 P).map P.subtype))
    (f : SourceCrossingGeometry (localModule T M) H Mc u) :
    centralizer ({u} : Set G) ∈ outsideOvergroups (Chapter1.H G)
      ((T : Subgroup G) ⊓ centralizer ({u} : Set G)) Mc M := by
  let h := source_rankTwo_f9_hypothesis hG T hempty hM hunique hmany hcard e hab H hH
  let : IsElementaryAbelian 2 (conjugateSpanBy (localModule T M) H) :=
    h.UH_elementary_of_V_le_QH ((le_conjugateSpanBy _ _).trans h.UH_le_QH)
  have hu2 : u ^ 2 = 1 := elemPow_eq_one_of_isElementaryAbelian
    (A := conjugateSpanBy (localModule T M) H) u hu
  have hune : u ≠ 1 := by
    intro he
    apply hmove
    intro x _
    rw [he, mem_centralizer_singleton_iff]
    simp
  have huord : orderOf u = 2 := orderOf_eq_prime hu2 hune
  let := hab
  refine ⟨Chapter1.mem_H_of_isTwoLocal (isTwoLocal_involution_centralizer huord),
    inf_le_right, ?_, ?_⟩
  · exact centralizer_not_le_of_crossing_match f.A H
      (conjugateSpanBy (localModule T M) Mc) Mc f.contained f.normalizes
      (le_normalizer_conjugateSpanBy _ _) u f.g f.matching f.crossing
  · intro hCM
    exact source_residual_not_le_of_span_coordinates T hcard P c
      ((suitable_parabolic_residual_centralizes h u hu P hP).trans hCM)

/-- Construct the literal second parabolic C_H(u mod Z) and the terminal
witness, keeping the chosen H, M, Mc and u throughout. -/
theorem source_terminal_witness_of_geometry
    (u : G) (hu : u ∈ conjugateSpanBy (localModule T M) H)
    (hindex : (suitableQuotientCentralizer
      (source_rankTwo_f9_hypothesis hG T hempty hM hunique hmany hcard e hab H hH) u).relIndex
        (T : Subgroup G) = 2)
    (hmove : ¬ Mc.pCoreIn 2 ≤ centralizer ({u} : Set G))
    (hproduct : ∀ t ∈ (T : Subgroup G), t ∉ suitableQuotientCentralizer
      (source_rankTwo_f9_hypothesis hG T hempty hM hunique hmany hcard e hab H hH) u →
        ¬ Mc.pCoreIn 2 ≤ centralizer ({u * (MulAut.conj t⁻¹) u} : Set G))
    (hU3 : Mc ⊓ normalizer (suitableQuotientCentralizer
      (source_rankTwo_f9_hypothesis hG T hempty hM hunique hmany hcard e hab H hH) u : Set G) =
        (T : Subgroup G))
    (hcoreIndex : 4 < (H.pCoreIn 2).relIndex (T : Subgroup G))
    (hrank : 4 ≤ Nat.log 2 ((centralizer (H.pCoreIn 2 : Set G)).relIndex
      (conjugateSpanBy (localModule T M) H)))
    (a : SourceParabolicAction
      ((source_rankTwo_f9_hypothesis hG T hempty hM hunique hmany hcard e hab H hH).kernel
        (zpowers u)))
    (c : SourceResidualSpanCoordinates (localModule T M) (centralInvolutions T)
      ((pResidual 2 ((source_rankTwo_f9_hypothesis hG T hempty hM hunique hmany hcard e hab
        H hH).kernel (zpowers u))).map
        ((source_rankTwo_f9_hypothesis hG T hempty hM hunique hmany hcard e hab
          H hH).kernel (zpowers u)).subtype))
    (f : SourceCrossingGeometry (localModule T M) H Mc u) :
    SourceTerminalWitness hG T hempty hM hunique hmany hcard e hab := by
  let h := source_rankTwo_f9_hypothesis hG T hempty hM hunique hmany hcard e hab H hH
  let P := h.kernel (zpowers u)
  have hHMc : H ≤ Mc := by
    have he := (Section02.source_lemma_14_2_3 hG T hempty hM hunique hmany hcard e
      H hH.1 hH.2).1
    exact (show Mc ∈ maximalTwoLocalOvergroups H from he ▸ Set.mem_singleton Mc).2
  have hPout : ¬ P ≤ M := by
    intro hPM
    exact source_residual_not_le_of_span_coordinates T hcard P c ((map_subtype_le _).trans hPM)
  let d : SourceSecondParabolicData h Mc M := {
    u := u
    mem_span := hu
    index := hindex
    moves_core := hmove
    product_moves_core := hproduct
    local_normalizer := hU3
    H2 := P
    quotient_sylow := suitable_quotient_sylow_of_local_normalizer h u Mc hHMc hU3
    le_quotient_centralizer := le_rfl
    quotient_model := a.quotient
    outside := hPout
    core_index := hcoreIndex
    module_rank := hrank }
  exact ⟨H,hH,d,source_centralizer_mem_outside_of_geometry hG T hempty hM hunique hmany
    hcard e hab H hH u hu hmove P le_rfl c f,c.rank_four⟩

/-- Apply the geometry to the same vector on the separated supports.
The existing suitable-choice theorem supplies U1--U3 and local Sylow data. -/
theorem source_terminal_witness_of_separated_support
    (K W S : Subgroup G)
    (hK : K ≤ ChapterA.Section04.twoGeneralizedFittingPreimage Mc)
    (hWU : W ≤ conjugateSpanBy (localModule T M) H)
    (hZW : centralInvolutions T ≤ W)
    (hKW : K ≤ normalizer (W : Set G))
    (hST : S ≤ (T : Subgroup G)) (hindex : S.relIndex (T : Subgroup G) = 2)
    (hU3 : Mc ⊓ normalizer (S : Set G) = (T : Subgroup G))
    (hseparate : ∀ t ∈ (T : Subgroup G), t ∉ S →
      W ⊓ W.map (MulAut.conj t⁻¹).toMonoidHom ≤ centralInvolutions T ∧
      K ≤ normalizer (W.map (MulAut.conj t⁻¹).toMonoidHom : Set G))
    (u : G) (huW : u ∈ W)
    (hfixed : ∀ s ∈ S, ⁅u,s⁆ ∈ centralInvolutions T)
    (hmoved : ∃ k ∈ K, ⁅u,k⁆ ∉ centralInvolutions T)
    (hcoreIndex : 4 < (H.pCoreIn 2).relIndex (T : Subgroup G))
    (hrank : 4 ≤ Nat.log 2 ((centralizer (H.pCoreIn 2 : Set G)).relIndex
      (conjugateSpanBy (localModule T M) H)))
    (a : SourceParabolicAction
      ((source_rankTwo_f9_hypothesis hG T hempty hM hunique hmany hcard e hab H hH).kernel
        (zpowers u)))
    (c : SourceResidualSpanCoordinates (localModule T M) (centralInvolutions T)
      ((pResidual 2 ((source_rankTwo_f9_hypothesis hG T hempty hM hunique hmany hcard e hab
        H hH).kernel (zpowers u))).map
        ((source_rankTwo_f9_hypothesis hG T hempty hM hunique hmany hcard e hab
          H hH).kernel (zpowers u)).subtype))
    (f : SourceCrossingGeometry (localModule T M) H Mc u) :
    SourceTerminalWitness hG T hempty hM hunique hmany hcard e hab := by
  obtain ⟨heq,hm,hp,_⟩ := source_suitable_of_separated_support
    hG T hempty hM hunique hmany hcard e hab H hH K W S hK hWU hZW hKW
      hST hindex hU3 hseparate u huW hfixed hmoved
  apply source_terminal_witness_of_geometry hG T hempty hM hunique hmany hcard e hab H hH
    u (hWU huW) _ hm hp _ hcoreIndex hrank a c f
  · rwa [heq]
  · rwa [heq]

end CFSG.Quasithin.Chapter14.Section06
