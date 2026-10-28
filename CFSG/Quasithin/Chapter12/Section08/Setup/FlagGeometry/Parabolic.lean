module

public import CFSG.Quasithin.Chapter12.Section08.Setup.SourceData
public import CFSG.Quasithin.Chapter12.Section08.Parabolic.Centers.MinimalParabolics.NaturalGeometry.MarkedGeneration
public import Theory.SpecificGroups.BinaryLinear.OrderedResidualConjugators

/-!
# The original omitted-point parabolic and its conjugator

Under one specified coordinate marking, the literal F.P L is the inverse
image of the minimal parabolic deleting cut zero. Its adjacent coordinate
swap lifts through the original full LT action and moves the point, hence
lies outside F.H. The same proof covers n=2, when P is all of LT; no full
L action or ambient natural marking is needed.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, Notation 12.8.2,
printed p.849, and the definition of P and choice of g immediately before
Lemma 12.8.9, printed p.852 of `refs/quasithin.pdf`.
-/

@[expose] public section

open Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section08.SetupFlagGeometry
open BinaryLinear BinaryLinear.OuterCyclic BinaryLinear.InvariantNodeActions
variable {G : Type*} [Group G] {T : Sylow 2 G} {L V : Subgroup G}
  [IsElementaryAbelian 2 V] {m : ℕ}

/-- The coordinate map is the original seed action followed by the specified
change of coordinates, for both source alternatives. -/
noncomputable def coordinateAction
    (hLV : L ≤ normalizer (V : Set G)) (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (β : Additive V ≃ₗ[ZMod 2] Space (m + 1)) :
    (L ⊔ (T : Subgroup G) : Subgroup G) →* LinearGroup (m + 1) :=
  (InvariantFlag.naturalFlagActorEquiv β).toMonoidHom.comp
    (setupSeedAction _ V (sup_le hLV hTV))

/-- Deleting the original point is exactly deleting coordinate cut zero. -/
theorem P_eq_coordinate_preimage (F : InvariantFlag T V (m + 1))
    (hm : 0 < m) (hLV : L ≤ normalizer (V : Set G))
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (β : Additive V ≃ₗ[ZMod 2] Space (m + 1)) (b : Basis m)
    (hcuts : ∀ i : Fin m, F.naturalFlagSpace β (i.val + 1) = cutSpace b i) :
    (F.P L).subgroupOf (L ⊔ (T : Subgroup G)) =
      (minimalParabolic b ⟨0, hm⟩).comap (coordinateAction hLV hTV β) := by
  rw [← F.orderedParabolic_one, ← F.naturalOrderedParabolic_comap L hLV 1]
  ext x
  change F.naturalFlagAction L hLV x ∈ F.naturalOrderedParabolic 1 ↔
    InvariantFlag.naturalFlagActorEquiv β (F.naturalFlagAction L hLV x) ∈
      minimalParabolic b ⟨0, hm⟩
  rw [← F.naturalOrderedParabolic_map_of_marking β b hcuts ⟨0, hm⟩,
    mem_map_equiv, MulEquiv.symm_apply_apply]

/-- Lift the adjacent swap across the deleted point through LT, including
n=2. No full action of L is needed. -/
theorem exists_adjacent_lift (F : InvariantFlag T V (m + 1))
    (hm : 0 < m) (hLV : L ≤ normalizer (V : Set G))
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hfull : Function.Surjective (setupSeedAction (L ⊔ (T : Subgroup G)) V (sup_le hLV hTV)))
    (β : Additive V ≃ₗ[ZMod 2] Space (m + 1)) (b : Basis m)
    (hcuts : ∀ i : Fin m, F.naturalFlagSpace β (i.val + 1) = cutSpace b i) :
    ∃ x : (L ⊔ (T : Subgroup G) : Subgroup G), (x : G) ∈ F.P L ∧
      (x : G) ∉ F.H ∧
      coordinateAction hLV hTV β x =
        BinaryLinear.OrderedResidualConjugators.adjacentSwap b ⟨0, hm⟩ := by
  let e := InvariantFlag.naturalFlagActorEquiv β
  let i : Fin m := ⟨0, hm⟩
  let s := BinaryLinear.OrderedResidualConjugators.adjacentSwap b i
  obtain ⟨x, hx⟩ := hfull (e.symm s)
  have he : coordinateAction hLV hTV β x = s := by
    change e (setupSeedAction _ V _ x) = s
    rw [hx, e.apply_symm_apply]
  refine ⟨x, ?_, ?_, he⟩
  · have hp : x ∈ (minimalParabolic b i).comap (coordinateAction hLV hTV β) := by
      change coordinateAction hLV hTV β x ∈ minimalParabolic b i
      rw [he]
      exact BinaryLinear.OrderedResidualConjugators.adjacentSwap_mem_minimalParabolic b i
    rwa [← P_eq_coordinate_preimage F hm hLV hTV β b hcuts] at hp
  · intro hh
    have ha : F.naturalFlagAction L hLV x ∈ F.naturalFlagStabilizer 1 :=
      (F.naturalFlagAction_mem_stabilizer L hLV 1 x).mpr hh
    have hs : s ∈ parabolic (cutSpace b i) := by
      rw [← hcuts i, ← F.naturalFlagStabilizer_map β 1, mem_map_equiv]
      have hh' : e (F.naturalFlagAction L hLV x) = s := he
      rw [← hh', e.symm_apply_apply]
      exact ha
    have hv := (hs (b i.castSucc)).mpr ((basis_mem_cutSpace b i _).mpr le_rfl)
    rw [BinaryLinear.OrderedResidualConjugators.adjacentSwap_basis,
      Equiv.swap_apply_left, basis_mem_cutSpace] at hv
    exact Nat.not_succ_le_self _ hv

end CFSG.Quasithin.Chapter12.Section08.SetupFlagGeometry
