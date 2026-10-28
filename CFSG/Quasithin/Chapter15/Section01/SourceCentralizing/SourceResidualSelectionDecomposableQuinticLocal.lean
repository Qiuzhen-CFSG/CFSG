module

public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionDecomposableQuinticSeed
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionDecomposableQuinticIntersection
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionDecomposableComponents
public import Theory.GroupAction.FixedSubgroupImageNormalizer

/-!
# Actual third-local control in the quintic decomposable row

The full original central seed already spans under the preimage of J-hat,
so a distinct maximal local cannot contain that product in its intersection
action. The exchanged dihedral product calculation then forces the actual
intersection to normalize the original Thompson image. Transport to its
fixed subgroup and the original ordering imply V(N) <= C_V(J1(T)).

The extra cubic action remains permitted. The endpoint is containment of
the actual third-local module in the original sixteen-element fixed group;
no equality of these modules or global residual conclusion is assumed.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section01
open Section03 Section03.InitialSource ChapterA.Section05To06 ChapterD ChapterD.UniqueFactor
open ChapterD.RatioDecomposition
variable {G : Type*} [Group G] [Finite G]

private theorem fixed_normalizer_of_thompson_image
    (T : Sylow 2 G) {M V X : Subgroup G} (hTM : (T : Subgroup G) ≤ M)
    (hV : PreparedChosenModule T M V) (hXM : X ≤ M)
    (hn : (X.subgroupOf M).map (actionHom M V hV.normalized).rangeRestrict ≤
      normalizer (((ChapterB.thompsonJ (T : Subgroup G) 1).subgroupOf M).map
        (actionHom M V hV.normalized).rangeRestrict : Set _)) :
    X ≤ normalizer (thompsonFixed T V : Set G) := by
  let f := (actionHom M V hV.normalized).rangeRestrict
  let J := ChapterB.thompsonJ (T : Subgroup G) 1
  have hJM : J ≤ M := (ChapterB.thompsonJ_le _ _).trans hTM
  let : (V.subgroupOf M).Normal := normal_subgroupOf_of_le_normalizer hV.normalized
  have hker : f.ker ≤ centralizer (V.subgroupOf M : Set M) := by
    intro x hx v hv
    have hx' : x ∈ (actionHom M V hV.normalized).ker := congrArg Subtype.val hx
    rw [actionHom_ker] at hx'
    exact Subtype.ext (hx' v hv)
  have he : V.subgroupOf M ⊓ centralizer (J.subgroupOf M : Set M) =
      (thompsonFixed T V).subgroupOf M := by
    ext x
    constructor
    · rintro ⟨hx,hc⟩
      refine ⟨hx,?_⟩
      intro j hj
      exact congrArg M.subtype (hc ⟨j,hJM hj⟩ hj)
    · rintro ⟨hx,hc⟩
      exact ⟨hx,fun j hj => Subtype.ext (hc j hj)⟩
  have hh := normalizes_fixed_of_image_normalizes f (V.subgroupOf M) (J.subgroupOf M)
    (X.subgroupOf M) le_normalizer_of_normal hker hn
  rw [he,←subgroupOf_normalizer_eq (inf_le_left.trans hV.le_selected)] at hh
  intro x hx
  exact hh (show (⟨x,hXM hx⟩ : M) ∈ X.subgroupOf M from hx)

private theorem local_module_le_fixed_of_intersection
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M V N : Subgroup G} (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hfull : V = localModule T M)
    (hN : N ∈ maximalTwoLocalOvergroups (T : Subgroup G))
    (hn : M ⊓ N ≤ normalizer (thompsonFixed T V : Set G)) :
    localModule T N ≤ thompsonFixed T V := by
  have hord := source_ordering_of_centralizing_orderingMaximal hG T hempty hM hJ N hN
  have hseed : centralInvolutions T ≤ thompsonFixed T V := by
    refine le_inf ?_ ?_
    · rw [hfull]
      exact le_conjugateSpanBy _ _
    · intro z hz j hj
      exact ((mem_omegaOneCenterAmbient_iff _ z).mp hz).2.2 j
        (ChapterB.thompsonJ_le _ _ hj)
  change conjugateSpanBy (centralInvolutions T) N ≤ _
  apply (closure_le _).mpr
  rintro x ⟨n,hnN,z,hz,rfl⟩
  obtain ⟨a,ha,c,hc,rfl⟩ := hord n hnN
  have hcz := mem_centralizer_iff.mp hc.2 z
    (le_conjugateSpanBy (centralInvolutions T) N hz)
  have he : (a*c)*z*(a*c)⁻¹ = a*z*a⁻¹ := by
    calc
      _ = a*(c*z)*c⁻¹*a⁻¹ := by group
      _ = a*(z*c)*c⁻¹*a⁻¹ := by rw [hcz]
      _ = _ := by group
  rw [he]
  exact le_normalizer_iff.mp hn a ⟨ha.2,ha.1⟩ z (hseed hz)

/-- The actual third-local intersection preserves the original sixteen-element
Thompson fixed subgroup, which contains that local's original module. -/
theorem PreparedChosenModule.decomposable_five_third_local_control
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc V N : Subgroup G} (hM : IsOrderingMaximal T M)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (h : PreparedChosenModule T M V) (hfull : V = localModule T M) :
    letI := h.elementary
    ∀ {U : Submodule (ZMod 2) (Additive V)}
      (c : FactorData (imageRepresentation M V h.normalized)
        (Jhat (imageRepresentation M V h.normalized)) U)
      (d : Decomposition c.representation), d.FittingFull →
    ∀ (s : DecomposableMarker.ThompsonPair (T := T) h.normalized c d)
      (π : internalActionImage M V h.normalized →* Equiv.Perm d.Index),
      (∀ g k, (c.ambientFactor d k).actor.map (MulAut.conj g).toMonoidHom =
        (c.ambientFactor d (π g k)).actor) →
      (∀ g k, (c.ambientFactor d k).space.map (imageRepresentation M V h.normalized g) =
        (c.ambientFactor d (π g k)).space) →
      SourceCases.Decomposable (imageRepresentation M V h.normalized) (T : Subgroup G) M
        (actionHom M V h.normalized).rangeRestrict c d π →
      cubicRatio (imageRepresentation M V h.normalized) = 2 → s.prime = 5 →
      N ∈ maximalTwoLocalOvergroups (T : Subgroup G) → N ≠ M → N ≠ Mc →
      ¬ M ⊓ N ≤ Mc ∧
        M ⊓ N ≤ normalizer (thompsonFixed T V : Set G) ∧
        localModule T N ≤ thompsonFixed T V := by
  subst V
  let := h.elementary
  intro U c d hd s π hp hs hdec hq hfive hN hNM hNMc
  have hnot := h.decomposable_five_third_image_not_contains hG T hempty hM hJ rfl
    c d hd s π hp hs hdec hfive hN hNM
  let f := (actionHom M (localModule T M) h.normalized).rangeRestrict
  let A := ((M ⊓ N).subgroupOf M).map f
  have hSA : ((T : Subgroup G).subgroupOf M).map f ≤ A :=
    map_mono (subgroupOf_mono M (le_inf hM.1.2 hN.2))
  have hAN := (s.image_contains_or_normalizes_of_prime_five hM.1.2 h.normalized
    c d π hp hdec hfive A hSA).resolve_left hnot
  have hr := source_centralizing_full_cases_twoRank hG T hM U c d hd π hp hs
    (Or.inr (Or.inr (Or.inl hdec)))
  have ha := (h.thompson_actors T hM.1.2 hq
    (fun E hE => hE.rank_le_of_primeRank_le hr)).1
  have hm := (h.source_thompson_escape_and_movement hG T hempty hM hmany hJ).2
  have he := (chosen_thompson_images_of_source_decomposable T hM.1.2 h.normalized
    hm ha c d π hp hdec).1
  have hn : M ⊓ N ≤ normalizer (thompsonFixed T (localModule T M) : Set G) := by
    apply fixed_normalizer_of_thompson_image T hM.1.2 h inf_le_left
    rwa [he]
  exact ⟨(h.third_maximal_action_constraints hG T hempty hM hJ hu hN hNM hNMc).1,
    hn,local_module_le_fixed_of_intersection hG T hempty hM hJ rfl hN hn⟩

end CFSG.Quasithin.Chapter15.Section01
