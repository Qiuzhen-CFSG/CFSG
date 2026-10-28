module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanLocalOmega
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanGlobalPrimeParabolicOrbit

/-!
# The original moving subgroup supplies its local Cartan control

An actual local Cartan escape centralizes the entire original Sylow
omega-center. For an H-star member moving that center, every compatible
Cartan therefore has the local control used in 5.2.2. At left degree two
the Cartan itself has order three, so failure of global normalization
constructs the original cubic zero-core pair directly.

The mixed-pair obstruction remains necessary after this reduction. No
classification of that pair or global group is assumed here.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric
open CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Prime
variable {G : Type*} [Group G] [Finite G]

/-- Movement of the original omega-center discharges every local-control
implication for the same H and the same compatible Cartan pair. -/
theorem cartanLocalControl_of_omega_movement
    {T : Sylow 2 G} {L W H A B : Subgroup G} {n : ℕ}
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H) (c : CartanPair T L H A B)
    (hZ : ¬ H ≤ omegaCentralizer T) : CartanLocalControl A H := by
  by_contra hcontrol
  obtain ⟨Y,hY,hescape⟩ := exists_local_cartan_escape hcontrol
  exact hZ (omegaCentralizer_of_local_cartan_escape h hH hgen c hY hescape)

/-- At field four the original escaping Cartan is itself the cubic actor;
no prime-subgroup selection or extra zero-core hypothesis is required. -/
theorem cubic_cartanActor_of_omega_movement
    {T : Sylow 2 G} {L W H A B : Subgroup G}
    (h : Input KnownSimple.IsKnownSimple T L W 2)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H) (c : CartanPair T L H A B)
    (hZ : ¬ H ≤ omegaCentralizer T)
    (hescape : ¬ A ≤ normalizer (residual H : Set G)) :
    CartanPrimeActor A H 3 A := by
  refine ⟨Or.inl rfl,le_rfl,?_,?_⟩
  · simpa using c.left_card h.linear h.sylow_normalizes
  · exact (cartanLocalControl_of_omega_movement h hH hgen c hZ).core_eq_bot_of_not_normalizes
      le_rfl hescape

/-- Every remaining field-four moving Cartan constructs its own genuine
cubic F.1.1 pair, retaining the actual residual factor selection and core. -/
theorem cubic_source_pair_of_omega_movement
    {T : Sylow 2 G} {L W H A B : Subgroup G}
    (h : Input KnownSimple.IsKnownSimple T L W 2)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H)
    (hthree : ¬ ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 4)
    (c : CartanPair T L H A B) (hZ : ¬ H ≤ omegaCentralizer T)
    (hescape : ¬ A ≤ normalizer (residual H : Set G)) :
    ∃ R : Subgroup G, LocalData T L H B A R ∧ SelectedSourceModels H R ∧
      (generated L H A R).pCoreIn 2 = ⊥ ∧
      ChapterF.Source.HypothesisF11 ![A ⊔ Global.sourceS L H,R] (Global.sourceS L H) :=
  source_prime_pair_zero_core h hH hgen hthree c
    (cubic_cartanActor_of_omega_movement h hH hgen c hZ hescape)

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric
