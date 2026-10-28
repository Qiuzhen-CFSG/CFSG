module
public import CFSG.Quasithin.Chapter13.Section02.A5Outside.OriginalCentralization.OriginalSelectedCoreModuleCentralization
public import CFSG.Quasithin.Chapter13.Section05.A5Source.ModuleIntersections
public import Theory.GroupTheory.PGroup.IrreducibleOmegaCore

/-!
# The original module inside a selected pair core

The central omega of a nonzero generated pair core cannot lie in the
chosen module: irreducibility would identify the two, and the right factor
would then normalize the module and lie in the original local normalizer.

The selected core centralizes the chosen module. Therefore either they
are disjoint, or the whole chosen module lies strictly inside the central
omega of that same core, and inside its commutator with L. No invariance
of the chosen module under the right factor is assumed.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section02.A5Outside.OriginalCentralization
open Section05.A5Source Chapter6.Source.RankOneGeneric
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ H R : Subgroup G}

/-- A nonzero original pair core has central omega outside the chosen module. -/
theorem original_generated_pair_core_omega_not_le_module
    (d : Context T L V V₁ V₂ V₃)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : R ⊔ (T : Subgroup G) = H)
    (hne : (ChapterF.Source.generated ![L,R] (Global.sourceS L H)).pCoreIn 2 ≠ ⊥) :
    ¬ omegaCenterIn ((ChapterF.Source.generated ![L,R] (Global.sourceS L H)).pCoreIn 2) ≤ V := by
  let N := ChapterF.Source.generated ![L,R] (Global.sourceS L H)
  let U := N.pCoreIn 2
  have hNU : N ≤ normalizer (U : Set G) :=
    N.le_normalizer.trans (normalizer_le_normalizer_characteristic_image N (pCore 2 N))
  have hNZ : N ≤ normalizer (omegaCenterIn U : Set G) :=
    hNU.trans (normalizer_le_normalizer_omegaCenterIn U)
  have hZ : omegaCenterIn U ≠ ⊥ := by
    have hn := inf_omegaCenterIn_ne_bot_of_normalized_twoGroup U U le_rfl
      (isPGroup_pCoreIn 2 N) U.le_normalizer hne
    intro hz
    exact hn (by rw [hz,inf_bot_eq])
  intro hZV
  have he := (d.irreducible_module (omegaCenterIn U) hZV
    ((show L ≤ N from le_sup_left.trans le_sup_left).trans hNZ)).resolve_left hZ
  have hRV : R ≤ normalizer (V : Set G) :=
    he ▸ ((show R ≤ N from le_sup_right.trans le_sup_left).trans hNZ)
  exact hH.1.2 (hgen ▸ sup_le (hRV.trans d.module_normalizer) d.normalizes_L)

/-- A selected pair core either misses V or has a strictly larger central
omega whose L-commutator contains the whole original V. -/
theorem original_selected_pair_core_module_intersection
    (d : Context T L V V₁ V₂ V₃)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : R ⊔ (T : Subgroup G) = H)
    (hind : ((T : Subgroup G) ⊓ normalizer (R : Set G)).relIndex (T : Subgroup G) ≤ 2)
    (hSR : Global.sourceS L H ≤ normalizer (R : Set G)) :
    let U := (ChapterF.Source.generated ![L,R] (Global.sourceS L H)).pCoreIn 2
    Disjoint V U ∨ (V < omegaCenterIn U ∧ V ≤ ⁅omegaCenterIn U,L⁆) := by
  let N := ChapterF.Source.generated ![L,R] (Global.sourceS L H)
  let U := N.pCoreIn 2
  have hLU : L ≤ normalizer (U : Set G) :=
    (show L ≤ N from le_sup_left.trans le_sup_left).trans
      (N.le_normalizer.trans (normalizer_le_normalizer_characteristic_image N (pCore 2 N)))
  rcases d.irreducible_module (V ⊓ U) inf_le_left
    ((le_inf d.chosen.normalizes hLU).trans inf_normalizer_le_normalizer_inf) with hi | hi
  · exact Or.inl (disjoint_iff.mpr hi)
  · have hVU : V ≤ U := hi.symm.le.trans inf_le_right
    have hVC : V ≤ centralizer (U : Set G) := le_centralizer_iff.mp
      (original_selected_pair_core_centralizes_module d hH hgen hind hSR)
    have hVZ : V ≤ omegaCenterIn U := by
      let : IsElementaryAbelian 2 V := d.elementary
      intro v hv
      exact (mem_omegaCenterIn_iff U v).mpr
        ⟨hVU hv,hVC hv,elemPow_eq_one_of_isElementaryAbelian v hv⟩
    have hne : U ≠ ⊥ := fun hu => d.chosen.ne_bot (bot_unique (hVU.trans_eq hu))
    exact Or.inr ⟨lt_of_le_not_ge hVZ
      (original_generated_pair_core_omega_not_le_module d hH hgen hne),
      d.chosen.eq_commutator.trans_le (commutator_mono hVZ le_rfl)⟩

end CFSG.Quasithin.Chapter13.Section02.A5Outside.OriginalCentralization
