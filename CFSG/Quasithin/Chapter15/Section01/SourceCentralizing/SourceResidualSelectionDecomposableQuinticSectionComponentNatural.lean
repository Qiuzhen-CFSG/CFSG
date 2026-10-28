module

public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionDecomposableQuinticSectionModelWhole
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SeedPlaneMarked

/-!
# Whole natural coordinates for the original half-cost component

Apply complete B.5 to the literal prepared seed inside the offender subgroup.
The original whole moved-space equality makes this seed the entire module,
so its faithful quotient loses neither actor rank nor fixed codimension.
The exact half-cost classification then supplies natural coordinates on the
whole seed. The component and module equivalences return these coordinates
to the same original component and the same whole module.
-/

public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.DecomposableQuinticControl
open ChapterB.QuasisimpleSource ChapterB.SourceInduction
open ChapterB.SourceInduction.ComponentReduction
open ChapterB.SourceInduction.ComponentReduction.PreliminaryActions
variable {G W : Type*} [Group G] [Finite G] [AddCommGroup W] [Module (ZMod 2) W]
  [FiniteDimensional (ZMod 2) W]

private noncomputable def wholeSeedActionEquiv
    (σ : Representation (ZMod 2) G W) {A L : Subgroup G}
    (hLA : ⁅L,A⁆ = L) (p : Prepared σ KnownSimple.IsKnownSimple hLA)
    (ht : naturalSeedSpace σ L A = ⊤) (n : ℕ)
    (e : ActionEquiv ((seedQuotientAction σ hLA).comp (seedComponentImage σ hLA).subtype)
      (linearNatural BinaryField.two n)) :
    ActionEquiv (σ.comp L.subtype) (linearNatural BinaryField.two n) := by
  let j : W ≃ₗ[ZMod 2] naturalSeedSpace σ L A :=
    { toFun := fun w => ⟨w,ht ▸ Submodule.mem_top⟩
      invFun := Subtype.val
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  let e₀ := seedComponentActionEquiv σ hLA p
  refine ⟨e₀.groupEquiv.trans e.groupEquiv,j.trans e.linearEquiv,?_⟩
  intro l w
  exact (congrArg e.linearEquiv (e₀.intertwines l (j w))).trans
    (e.intertwines (e₀.groupEquiv l) (j w))

/-- A whole moved component and the actual half-cost offender give natural
binary coordinates on the entire original module. -/
theorem whole_component_natural_of_half_cost
    (σ : Representation (ZMod 2) G W) (hf : Function.Injective σ)
    (hcore : pCore 2 G = ⊥) (cover : SQTKQuotient KnownSimple.IsKnownSimple G)
    {A L : Subgroup G} (hL : IsComponent G L)
    (hA : IsMinimalBestOffender σ A) (hLA : ⁅L,A⁆ = L)
    (hcost : (rank A = 2 ∧ fixedCodim σ A = 1) ∨
      (rank A = 4 ∧ fixedCodim σ A = 2))
    (hd : Module.finrank (ZMod 2) (moved σ A) ≤ 2)
    (hm : moved σ L = ⊤) :
    ∃ n : ℕ, (n = 3 ∨ n = 4 ∨ n = 5) ∧
      Nonempty (ActionEquiv (σ.comp L.subtype) (linearNatural BinaryField.two n)) := by
  let N := offenderSubgroup σ
  obtain ⟨hLN,hAN,hcomm,p,⟨q⟩,hseed,hmseed⟩ :=
    component_marked_seed_of_minimal_plane σ hf hcore cover hL hA hLA hd
  let τ := σ.comp N.subtype
  have hseedTop : naturalSeedSpace τ (L.subgroupOf N) (A.subgroupOf N) = ⊤ := by
    rw [hseed]
    change subspaceCommutator (σ.comp N.subtype) ⊤ (L.subgroupOf N) = ⊤
    rw [subspaceCommutator_comp_map,map_subgroupOf_eq_of_le hLN]
    exact hm
  have hA₀ : IsElementaryTwo (A.subgroupOf N) :=
    ((hA.1.isOffender σ).subgroupOf σ hAN).1
  have hcost₀ : (rank (A.subgroupOf N) = 2 ∧ fixedCodim τ (A.subgroupOf N) = 1) ∨
      (rank (A.subgroupOf N) = 4 ∧ fixedCodim τ (A.subgroupOf N) = 2) := by
    change (rank (A.subgroupOf N) = 2 ∧
      fixedCodim (σ.comp N.subtype) (A.subgroupOf N) = 1) ∨
      (rank (A.subgroupOf N) = 4 ∧
      fixedCodim (σ.comp N.subtype) (A.subgroupOf N) = 2)
    rw [rank_subgroupOf hAN,fixedCodim_subgroupOf σ hAN]
    exact hcost
  obtain ⟨hr,hc⟩ := seed_cost_of_whole τ (hf.comp N.subtype_injective)
    hcomm hA₀ hseedTop
  have hseedCost : (rank (seedOffenderImage τ hcomm) = 2 ∧
      fixedCodim (seedQuotientAction τ hcomm) (seedOffenderImage τ hcomm) = 1) ∨
      (rank (seedOffenderImage τ hcomm) = 4 ∧
      fixedCodim (seedQuotientAction τ hcomm) (seedOffenderImage τ hcomm) = 2) := by
    rw [hr,hc]
    exact hcost₀
  have hd₀ : Module.finrank (ZMod 2) (moved τ (A.subgroupOf N)) ≤ 2 := by
    change Module.finrank (ZMod 2) (subspaceCommutator (σ.comp N.subtype) ⊤
      (A.subgroupOf N)) ≤ 2
    rw [subspaceCommutator_comp_map,map_subgroupOf_eq_of_le hAN]
    exact hd
  obtain ⟨n,hn,⟨e⟩⟩ := whole_natural_of_half_cost (seedQuotientAction τ hcomm)
    p.minimal.1.1 (p.minimal.isQuadratic _) hseedCost
    (seedOffender_moved_le τ hcomm hd₀) hmseed q.sectionData q.clause_one
  let e₀ := wholeSeedActionEquiv τ hcomm p hseedTop n e
  refine ⟨n,hn,⟨⟨(subgroupOfEquivOfLe hLN).symm.trans e₀.groupEquiv,
    e₀.linearEquiv,?_⟩⟩⟩
  intro l w
  exact e₀.intertwines ((subgroupOfEquivOfLe hLN).symm l) w

end CFSG.Quasithin.Chapter15.DecomposableQuinticControl
