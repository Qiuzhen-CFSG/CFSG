module

public import CFSG.Quasithin.Chapter3.Section02.ChosenSource325.FixedInvarianceInput
public import CFSG.Quasithin.Chapter3.Section02.FundamentalModule
public import Theory.GroupTheory.ReducedNormal.SubspaceGroupConsequences
public import Theory.GroupTheory.ReducedNormal.SubspaceQuotientAction
public import Theory.Representation.BinaryOffender.EquivariantBest

/-!
# The actual faithful fixed-seed action in source 3.2.5

B.2.7 places the Sylow Thompson image inside the genuine best-offender
subgroup. The centralizer quotient and the faithful reduced-subspace action
are compared by their original equivariant coordinates. Thus L=[L,J(T)]
places the literal component image in that offender subgroup.

For the Fundamental Setup with L=L₀, the image is an ordinary component,
the original seed remains Irr⁺, and its nonzero fixed space survives the
faithful restriction. All these facts are constructed before applying the
separate B.5 classification input. The final equality is explicitly
conditional on that input; the orbit is not identified with the seed in
any transport step.

Source: Aschbacher--Smith, combined manuscript of 1 March 2004,
3.2.5, printed p.580; B.2.7, p.77; D.3.3 and D.3.20, pp.193 and204.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open Representation.BinaryOffender.Homogeneous
open scoped IsMulCommutative

namespace CFSG.Quasithin.Chapter3.Section02.ChosenSource325

variable {G : Type*} [Group G] [Finite G]

/-- B.2.7 on the faithful action of an arbitrary invariant reduced subspace. -/
theorem reduced_thompson_image_le (M : Subgroup G) (S : Sylow 2 M)
    (W : Submodule (ZMod 2) (Additive (ReducedNormal.ModuleGroup M)))
    (hW : (⊤ : Subgroup M) ≤ subspaceStabilizer (ReducedNormal.representation M) W) :
    (Stellmacher.elementaryAbelianMaxJ (S : Subgroup M)).map
      (invariantActionHom (ReducedNormal.representation M) W hW) ≤
      offenderSubgroup (subspaceImageRepresentation (ReducedNormal.representation M) W) := by
  let U := ReducedNormal.intrinsicSubspace M W
  let : U.Normal := ReducedNormal.intrinsicSubspace_normal M W hW
  let α := ChapterB.InternalThompsonAction.action U
  let β := subspaceImageRepresentation (ReducedNormal.representation M) W
  let e := ReducedNormal.intrinsicQuotientEquiv M W hW
  let E := (ReducedNormal.intrinsicLinearEquiv M W).symm
  have hE (g) (w) : E (α g w) = β (e g) (E w) := by
    apply (ReducedNormal.intrinsicLinearEquiv M W).injective
    rw [LinearEquiv.apply_symm_apply]
    exact (ReducedNormal.intrinsicLinearEquiv_equivariant M W hW g (E w)).trans
      (by rw [LinearEquiv.apply_symm_apply]; rfl) |>.symm
  have hO : (offenderSubgroup α).map e.toMonoidHom ≤ offenderSubgroup β := by
    apply map_le_iff_le_comap.mpr
    apply iSup_le
    intro A
    apply iSup_le
    rintro ⟨hA, _⟩
    exact map_le_iff_le_comap.mp
      ((hA.map_equivariant α β e E hE).le_offenderSubgroup β)
  have ht := (map_mono (ChapterB.InternalThompsonAction.thompson_image_le S U)).trans hO
  have he : e.toMonoidHom.comp (ChapterB.InternalThompsonAction.actionMk U) =
      invariantActionHom (ReducedNormal.representation M) W hW := by
    apply MonoidHom.ext
    intro g
    exact ReducedNormal.intrinsicQuotientEquiv_mk M W hW g
  rw [map_map, he] at ht
  exact ht

/-- The literal commutator hypothesis places the actor in the offender group. -/
theorem reduced_actor_le_offender (M : Subgroup G) (S : Sylow 2 M)
    (W : Submodule (ZMod 2) (Additive (ReducedNormal.ModuleGroup M)))
    (hW : (⊤ : Subgroup M) ≤ subspaceStabilizer (ReducedNormal.representation M) W)
    (X : Subgroup M)
    (hX : X = ⁅X, Stellmacher.elementaryAbelianMaxJ (S : Subgroup M)⁆) :
    restrictedSubgroup (ReducedNormal.representation M) W X ≤
      offenderSubgroup (subspaceImageRepresentation (ReducedNormal.representation M) W) := by
  let f := invariantActionHom (ReducedNormal.representation M) W hW
  let β := subspaceImageRepresentation (ReducedNormal.representation M) W
  let : (offenderSubgroup β).Normal := offenderSubgroup_normal β
  rw [← invariantActionHom_map _ _ hW, hX, map_commutator]
  exact (commutator_mono le_rfl (reduced_thompson_image_le M S W hW)).trans
    (commutator_le_right _ _)

end CFSG.Quasithin.Chapter3.Section02.ChosenSource325

namespace CFSG.Quasithin.Chapter3.Section02.FundamentalSetup
open ChapterD.Section03 ChosenSource325
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}

/-- All faithful D.3.20 inputs on the original full FSU orbit are proved,
including the component image and its actual offender containment. -/
theorem exists_faithful_fixed_seed
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    (h127 : Chapter1.Section02.NonsolvableUniquenessConclusion T L)
    (hL : localOrbit T L = L)
    (hcomm : L = ⁅L, Stellmacher.elementaryAbelianMaxJ (T : Subgroup G)⁆)
    (hfix : D.seed ⊓ centralizer (L : Set G) ≠ ⊥) :
    ∃ J : Submodule (ZMod 2) (Additive (ReducedNormal.ModuleGroup D.maximalLocal)),
      ReducedNormal.subspaceImage D.maximalLocal J = D.seed ∧
      ReducedNormal.subspaceImage D.maximalLocal
        (orbitSpan (ReducedNormal.representation D.maximalLocal) ⊤ J) = D.fullModule ∧
      FixedSeedHypotheses
        (subspaceImageRepresentation (ReducedNormal.representation D.maximalLocal)
          (orbitSpan (ReducedNormal.representation D.maximalLocal) ⊤ J))
        (D.ambientSylow.mapSurjective (invariantActionHom_surjective
          (ReducedNormal.representation D.maximalLocal) _ (orbitSpan_invariant _ ⊤ J)))
        (restrictedSubgroup (ReducedNormal.representation D.maximalLocal)
          (orbitSpan (ReducedNormal.representation D.maximalLocal) ⊤ J)
          ((localOrbit T L).subgroupOf D.maximalLocal))
        (J.comap (orbitSpan (ReducedNormal.representation D.maximalLocal) ⊤ J).subtype) := by
  obtain ⟨J, hJ, hW, hi⟩ := D.exists_internal_seed h127
  let M := D.maximalLocal
  let ρ := ReducedNormal.representation M
  let W := orbitSpan ρ ⊤ J
  let X := (localOrbit T L).subgroupOf M
  let f := invariantActionHom ρ W (orbitSpan_invariant ρ ⊤ J)
  have hf : Function.Surjective f := invariantActionHom_surjective ρ W _
  have hmap (A : Subgroup M) : A.map f = restrictedSubgroup ρ W A :=
    invariantActionHom_map ρ W _ A
  have hLM : L ≤ M := by rw [← hL]; exact (localOrbit T L).le_normalizer
  have hXcomm : X = ⁅X, Stellmacher.elementaryAbelianMaxJ (D.ambientSylow : Subgroup M)⁆ := by
    apply map_injective M.subtype_injective
    rw [map_commutator, ← Stellmacher.elementaryAbelianMaxJ_map_injective M.subtype M.subtype_injective]
    rw [map_subgroupOf_eq_of_le (localOrbit T L).le_normalizer]
    change localOrbit T L = ⁅localOrbit T L,
      Stellmacher.elementaryAbelianMaxJ (((T : Subgroup G).subgroupOf M).map M.subtype)⁆
    rw [map_subgroupOf_eq_of_le (le_normalizer_componentOrbit L T), hL]
    exact hcomm
  have hXO := reduced_actor_le_offender M D.ambientSylow W (orbitSpan_invariant ρ ⊤ J) X hXcomm
  have hXcomp : IsComponent (subspaceActionImage ρ W) (restrictedSubgroup ρ W X) := by
    have hLc : (L.subgroupOf M).IsCComponent := D.component_in_maximalLocal
    let e := subgroupOfEquivOfLe hLM
    let q := e.toMonoidHom.pCoreQuotientEquiv (p := 2) e.surjective
      (by rw [e.toMonoidHom.ker_eq_bot e.injective]; exact IsPGroup.of_bot)
    let := D.quasisimple
    have hq : IsQuasisimple ((L.subgroupOf M) ⧸ pCore 2 (L.subgroupOf M)) :=
      IsQuasisimple.of_mulEquiv q.symm
    have hXL : X = L.subgroupOf M := congrArg (fun A : Subgroup G => A.subgroupOf M) hL
    have hk : (L.subgroupOf M).pCoreIn 2 ≤ f.ker := hXL ▸ hi.orbitMap_kills_core
    have hn : (L.subgroupOf M).map f ≠ ⊥ := by
      rw [← hXL, hmap]
      exact hi.orbit_actor_ne_bot
    rw [← hmap, hXL]
    exact hLc.isComponent_map_of_twoCore_killed hq f hf hk hn
  have hfixed : (J.comap W.subtype) ⊓
      fixedSpace (subspaceImageRepresentation ρ W) (restrictedSubgroup ρ W X) ≠ ⊥ := by
    intro hz
    have hjz : J ⊓ fixedSpace ρ X = ⊥ := by
      apply le_bot_iff.mp
      intro v hv
      have hvW : v ∈ W := le_orbitSpan ρ ⊤ J hv.1
      have hm : (⟨v,hvW⟩ : W) ∈ (J.comap W.subtype) ⊓
          fixedSpace (subspaceImageRepresentation ρ W) (restrictedSubgroup ρ W X) := by
        refine ⟨hv.1, ?_⟩
        rw [fixedSpace_restrictedSubgroup ρ W X (le_top.trans (orbitSpan_invariant ρ ⊤ J))]
        exact hv.2
      have he : (⟨v,hvW⟩ : W) = 0 := (Submodule.mem_bot (R := ZMod 2)).mp (hz ▸ hm)
      exact congrArg Subtype.val he
    have he := congrArg (ReducedNormal.subspaceImage M) hjz
    rw [ReducedNormal.subspaceImage_inf_fixedSpace M J (localOrbit T L)
      (localOrbit T L).le_normalizer, ReducedNormal.subspaceImage_bot, hJ, hL] at he
    exact hfix he
  exact ⟨J, hJ, hW, { hi.faithfulOrbit_source with
    component := hXcomp, offender := hXO, fixed := hfixed }⟩

/-- The original seed is normalizer-invariant once the independent B.5
fixed-component implication has been supplied. -/
theorem fullModule_eq_seed_of_fixedComponent
    (hclass : FixedComponentInput.{u,u})
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    (h127 : Chapter1.Section02.NonsolvableUniquenessConclusion T L)
    (hL : localOrbit T L = L)
    (hcomm : L = ⁅L, Stellmacher.elementaryAbelianMaxJ (T : Subgroup G)⁆)
    (hfix : D.seed ⊓ centralizer (L : Set G) ≠ ⊥) : D.fullModule = D.seed := by
  obtain ⟨J, hJ, hW, hs⟩ := D.exists_faithful_fixed_seed h127 hL hcomm hfix
  let ρ := ReducedNormal.representation D.maximalLocal
  let W := orbitSpan ρ ⊤ J
  have ht := source_seed_eq_top_of_fixedComponent hclass hs.toSourceHypotheses
    hs.component hs.offender hs.fixed
  have hJW : J = W := by
    apply le_antisymm (le_orbitSpan ρ ⊤ J)
    intro v hv
    have hm : (⟨v,hv⟩ : W) ∈ J.comap W.subtype := ht ▸ Submodule.mem_top
    exact hm
  exact hW.symm.trans ((congrArg (ReducedNormal.subspaceImage D.maximalLocal) hJW.symm).trans hJ)


end CFSG.Quasithin.Chapter3.Section02.FundamentalSetup
