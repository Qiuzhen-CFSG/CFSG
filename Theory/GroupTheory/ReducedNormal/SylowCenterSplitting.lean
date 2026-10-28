module

public import Theory.GroupTheory.ReducedNormal.SylowCenterClosure
public import Theory.GroupTheory.Commutator.NormalClosureSupplement
public import Theory.GroupTheory.PResidual.SylowSupplement

/-!
# Splitting the Sylow omega-center orbit

For U = ⟨Ω₁(Z(T))ᴳ⟩, the Sylow complement centralizes the generating
seed, so [U,G] = [U,O²(G)]. If the latter moved group has a disjoint
residual-fixed complement in U, that complement is already central in G:
its commutators lie in both summands. Since U is elementary and lies in
T, the complement is precisely C_{Ω₁(Z(T))}(G).

This is the literal subgroup splitting used in Aschbacher–Smith B.2.14
and 13.2.8(2), printed pp.78 and880. The solvable FF classification
supplies the residual complement in the source consumer.
-/

public section
open Subgroup Stellmacher
namespace Theory.GroupTheory
variable {G : Type*} [Group G] [Finite G]

/-- The whole group and its two-residual move the same original omega orbit. -/
theorem omegaCenter_span_commutator (T : Sylow 2 G) (U : Subgroup G)
    (hU : U = normalClosure (omegaOneCenterAmbient (T : Subgroup G) : Set G)) :
    ⁅U,(⊤ : Subgroup G)⁆ = ⁅U,pResidual 2 G⁆ := by
  have hZ : omegaOneCenterAmbient (T : Subgroup G) ≤ centralizer (T : Set G) :=
    fun _ hz => ((mem_omegaOneCenterAmbient_iff _ _).mp hz).2.2
  have he := normalClosure_commutator_eq_of_centralizing_supplement
    (omegaOneCenterAmbient (T : Subgroup G)) (pResidual 2 G) (T : Subgroup G)
    (pResidual_sup_sylow_eq_top T) hZ
  rw [← hU] at he
  apply le_antisymm _ (commutator_mono le_rfl le_top)
  rw [he]
  exact commutator_mono (hU ▸ le_normalClosure) le_rfl

/-- A residual-fixed complement in the omega orbit is exactly the original central seed. -/
theorem omegaCenter_span_fixed_complement (T : Sylow 2 G) (U : Subgroup G)
    [U.Normal] [IsElementaryAbelian 2 U]
    (hU : U = normalClosure (omegaOneCenterAmbient (T : Subgroup G) : Set G))
    (hUT : U ≤ (T : Subgroup G))
    (hd : Disjoint (⁅U,pResidual 2 G⁆ : Subgroup G)
      (U ⊓ centralizer (pResidual 2 G : Set G))) :
    U ⊓ centralizer (pResidual 2 G : Set G) =
      omegaOneCenterAmbient (T : Subgroup G) ⊓ center G := by
  let C := U ⊓ centralizer (pResidual 2 G : Set G)
  have hc : ⁅C,(⊤ : Subgroup G)⁆ = ⊥ := by
    apply bot_unique
    apply (le_inf ?_ (commutator_le_left _ _)).trans hd.eq_bot.le
    rw [← omegaCenter_span_commutator T U hU]
    exact commutator_mono inf_le_left le_rfl
  have hcz : C ≤ center G := by
    have hh := commutator_eq_bot_iff_le_centralizer.mp hc
    simpa only [Subgroup.coe_top, centralizer_univ] using hh
  apply le_antisymm
  · intro c hc
    refine ⟨(mem_omegaOneCenterAmbient_iff _ _).mpr ⟨hUT hc.1,
      elemPow_eq_one_of_isElementaryAbelian c hc.1,?_⟩,hcz hc⟩
    intro t _
    exact mem_center_iff.mp (hcz hc) t
  · intro z hz
    exact ⟨(hU ▸ le_normalClosure) hz.1,center_le_centralizer _ hz.2⟩

/-- The full direct-sum identity with the same original central seed. -/
theorem omegaCenter_span_splitting (T : Sylow 2 G) (U : Subgroup G)
    [U.Normal] [IsElementaryAbelian 2 U]
    (hU : U = normalClosure (omegaOneCenterAmbient (T : Subgroup G) : Set G))
    (hUT : U ≤ (T : Subgroup G))
    (hs : (⁅U,pResidual 2 G⁆ : Subgroup G) ⊔
      (U ⊓ centralizer (pResidual 2 G : Set G)) = U)
    (hd : Disjoint (⁅U,pResidual 2 G⁆ : Subgroup G)
      (U ⊓ centralizer (pResidual 2 G : Set G))) :
    (⁅U,(⊤ : Subgroup G)⁆ : Subgroup G) ⊔
      (omegaOneCenterAmbient (T : Subgroup G) ⊓ center G) = U ∧
      Disjoint (⁅U,(⊤ : Subgroup G)⁆ : Subgroup G)
        (omegaOneCenterAmbient (T : Subgroup G) ⊓ center G) := by
  rw [omegaCenter_span_commutator T U hU,
    ← omegaCenter_span_fixed_complement T U hU hUT hd]
  exact ⟨hs,hd⟩

end Theory.GroupTheory
