module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearThree.CoreActions.ThreeLayer
public import Theory.GroupTheory.Commutator.GeneratedCoreLifts

/-!
The exchanged residual fixes the natural derived subgroup. Its exact action
on the doubled-dual quotient is trivial or fully moving; generated-core lifts
reduce both alternatives through the derived subgroup, retaining the fixed
part of the full center. Simultaneous full displacement forces conjugation
invariance of the characteristic derived layer and contradicts its two
residual actions. Source: Aschbacher--Smith15.3.23, p.1129.
-/

public section
open Subgroup Representation
open CFSG.Quasithin.Chapter15.Section04.LocalSetup.CoreElimination.BlockSieve.ExchangedCases.SL3Geometry.SourceCases
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearThree.OriginalSource.FullCover.Dynamics
open CoreActions CoreActions.ThreeLayer
variable {G : Type*} [Group G] [Finite G]
local notation "SL" => Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)

theorem YL_not_fixes_derived (d : LocalData G) (L : Subgroup G)
    {e : (L ⧸ pCore 2 L) ≃* SL}
    (m : LayerModel L ⁅commutatorCore L,commutatorCore L⁆ ⊥ e (NaturalCopies (ZMod 2) 1))
    (hU : ⁅d.V,YL d L⁆ ≠ ⊥) :
    ¬ YL d L ≤ centralizer ((⁅commutatorCore L,commutatorCore L⁆ : Subgroup G) : Set G) := by
  intro hfix
  have hYL : YL d L ≤ L := (ComponentIntersection.intersectionResidual_le _ _).trans inf_le_right
  have htwo : IsPGroup 2 (YL d L) :=
    (L.isPGroup_pCoreIn 2).to_le ((le_inf hYL hfix).trans (natural_centralizer_le_core m))
  have hi := (ComponentIntersection.intersectionResidual_isPPerfect d.Yplus L).hom_eq_one_of_isPGroup
    htwo (MonoidHom.id (YL d L))
  have hb : YL d L = ⊥ := by
    apply le_bot_iff.mp
    intro y hy
    exact congrArg (fun f : YL d L →* YL d L => (f ⟨y,hy⟩ : G)) hi
  exact hU (by rw [hb,commutator_bot_right])
theorem core_not_conjugation_invariant (d : LocalData G) (L : Subgroup G)
    {e : (L ⧸ pCore 2 L) ≃* SL}
    (m : LayerModel L (⁅commutatorCore L,commutatorCore L⁆) ⊥ e (NaturalCopies (ZMod 2) 1))
    (hU : ⁅d.V, YL d L⁆ ≠ ⊥)
    (hfix : YC d L ≤ centralizer ((⁅commutatorCore L,commutatorCore L⁆ : Subgroup G) : Set G))
    (t : G) (hex : (YL d L).conjBy t = YC d L) :
    (commutatorCore L).conjBy t ≠ commutatorCore L := by
  intro hQ
  have hZ : (⁅commutatorCore L,commutatorCore L⁆).map (MulAut.conj t).toMonoidHom = ⁅commutatorCore L,commutatorCore L⁆ := by
    rw [map_commutator]
    change ⁅(commutatorCore L).conjBy t,(commutatorCore L).conjBy t⁆ = _
    rw [hQ]
  apply YL_not_fixes_derived d L m hU
  intro y hy z hz
  have hy' : (MulAut.conj t) y ∈ YC d L := hex ▸ mem_map_of_mem (MulAut.conj t).toMonoidHom hy
  have hz' : (MulAut.conj t) z ∈ (⁅commutatorCore L,commutatorCore L⁆ : Subgroup G) := hZ ▸ mem_map_of_mem (MulAut.conj t).toMonoidHom hz
  have h := hfix hy' _ hz'
  apply (MulAut.conj t).injective
  simpa only [map_mul] using h


theorem commonCore_displacement (d : LocalData G) {I : Subgroup G}
    (c : ComponentWitness d I)
    {e : (c.L ⧸ pCore 2 c.L) ≃* SL}
    (m : LayerModel c.L (⁅commutatorCore c.L,commutatorCore c.L⁆) ⊥ e (NaturalCopies (ZMod 2) 1))
    (hSQ : commutatorCore c.L ≤ d.S)
    (hSYL : d.S ≤ normalizer (YL d c.L : Set G))
    (hSC : d.S ≤ normalizer (YC d c.L : Set G))
    (hfix : YC d c.L ≤ centralizer ((⁅commutatorCore c.L,commutatorCore c.L⁆ : Subgroup G) : Set G))
    (hfullL : ⁅commutatorCore c.L, YL d c.L⁆ = commutatorCore c.L)
    (hfullC : ⁅commutatorCore c.L, YC d c.L⁆ = commutatorCore c.L) :
    ⁅commonCore d c.L, YL d c.L⁆ = commutatorCore c.L ∧
    ⁅commonCore d c.L, YC d c.L⁆ = commutatorCore c.L := by
  have hQK : commutatorCore c.L ≤ commonCore d c.L :=
    le_inf (core_le_YL_core d c.L hSQ hSYL hfullL) (core_le_YC_core d c.L hSQ hSC hfullC)
  have hKL : commonCore d c.L ≤ c.L := inf_le_left.trans
    (((YL d c.L).pCoreIn_le 2).trans ((ComponentIntersection.intersectionResidual_le _ _).trans inf_le_right))
  have hKC : commonCore d c.L ≤ YC d c.L := inf_le_right.trans ((YC d c.L).pCoreIn_le 2)
  have hKO : commonCore d c.L ≤ c.L.pCoreIn 2 :=
    (le_inf hKL (hKC.trans hfix)).trans (natural_centralizer_le_core m)
  have hYL : YL d c.L ≤ c.L := (ComponentIntersection.intersectionResidual_le _ _).trans inf_le_right
  constructor
  · exact le_antisymm (commutator_mono hKO hYL)
      (hfullL.ge.trans (commutator_mono hQK le_rfl))
  · apply le_antisymm _ (hfullC.ge.trans (commutator_mono hQK le_rfl))
    rw [commutator_comm]
    exact (commutator_mono le_rfl hKL).trans (YC_commutator_le d c)


theorem core_invariant_of_both_moving (d : LocalData G) {I : Subgroup G}
    (c : ComponentWitness d I)
    {e : (c.L ⧸ pCore 2 c.L) ≃* SL}
    (m : LayerModel c.L (⁅commutatorCore c.L,commutatorCore c.L⁆) ⊥ e (NaturalCopies (ZMod 2) 1))
    (hindex : (d.S.subgroupOf (d.T : Subgroup G)).index = 2)
    (hSQ : commutatorCore c.L ≤ d.S)
    (hSYL : d.S ≤ normalizer (YL d c.L : Set G))
    (hfix : YC d c.L ≤ centralizer ((⁅commutatorCore c.L,commutatorCore c.L⁆ : Subgroup G) : Set G))
    (hfullL : ⁅commutatorCore c.L, YL d c.L⁆ = commutatorCore c.L)
    (hfullC : ⁅commutatorCore c.L, YC d c.L⁆ = commutatorCore c.L)
    (t : G) (ht : t ∈ (d.T : Subgroup G))
    (hex : (YL d c.L).conjBy t = YC d c.L) :
    (commutatorCore c.L).conjBy t = commutatorCore c.L := by
  have hh := commonCore_displacement d c m hSQ hSYL
    (S_normalizes_YC d c.L hindex hSYL t ht hex) hfix hfullL hfullC
  calc
    (commutatorCore c.L).conjBy t = (⁅commonCore d c.L, YL d c.L⁆).conjBy t := congrArg (fun H : Subgroup G => H.conjBy t) hh.1.symm
    _ = ⁅(commonCore d c.L).conjBy t, (YL d c.L).conjBy t⁆ := map_commutator _ _ _
    _ = ⁅commonCore d c.L, YC d c.L⁆ := by rw [commonCore_conj_eq d c.L hindex hSYL t ht hex, hex]
    _ = commutatorCore c.L := hh.2


/-- Natural derived fixation and the exact central quotient suffice for the
actual exchanged residual; the full center need not be natural or Frattini. -/
theorem YC_fixes_core (d : LocalData G) {I : Subgroup G}
    (c : ComponentWitness d I)
    {e : (c.L ⧸ pCore 2 c.L) ≃* SL}
    (m : LayerModel c.L ⁅commutatorCore c.L,commutatorCore c.L⁆ ⊥ e (NaturalCopies (ZMod 2) 1))
    (n : LayerModel c.L (commutatorCore c.L) (coreCenter c.L) e (DualCopies (ZMod 2) 2))
    (hQL : ⁅commutatorCore c.L,c.L⁆ = commutatorCore c.L)
    (hZL : ⁅coreCenter c.L,c.L⁆ ≤ ⁅commutatorCore c.L,commutatorCore c.L⁆)
    (hLC : c.L ≤ normalizer (YC d c.L : Set G))
    (hfix : YC d c.L ≤ centralizer ((⁅commutatorCore c.L,commutatorCore c.L⁆ : Subgroup G) : Set G))
    (hi : (d.S.subgroupOf (d.T : Subgroup G)).index = 2)
    (hSQ : commutatorCore c.L ≤ d.S)
    (hSYL : d.S ≤ normalizer (YL d c.L : Set G))
    (hU : ⁅d.V,YL d c.L⁆ ≠ ⊥)
    (hfullL : ⁅commutatorCore c.L,YL d c.L⁆ = commutatorCore c.L)
    (t : G) (ht : t ∈ (d.T : Subgroup G)) (hex : (YL d c.L).conjBy t = YC d c.L) :
    YC d c.L ≤ centralizer (commutatorCore c.L : Set G) := by
  have hCQ := ResidualAlternatives.residual_normalizes c
  have hLQ : c.L ≤ normalizer (commutatorCore c.L : Set G) := normalizer_commutator_ge_right _ _
  have hQ : IsPGroup 2 (commutatorCore c.L) :=
    (c.L.isPGroup_pCoreIn 2).to_le (commutatorCore_le c.L)
  rcases ResidualAlternatives.dual_copies_fixed_or_moving
    (ResidualAlternatives.residualAction c n)
    (ComponentIntersection.centralizerResidual_isPPerfect d.Yplus c.L)
    (ResidualAlternatives.residualAction_commutes c n) with htriv | hfull
  · exact centralizes_of_derived_displacement _ _ hQ
      (ComponentIntersection.centralizerResidual_isPPerfect d.Yplus c.L) hfix
      (commutator_le_derived_of_generated_core _ _ _ _ hQL hLQ hCQ
        (YC_commutator_le d c) hZL
        (ResidualAlternatives.displacement_le_center_of_trivial c n htriv))
  · have hn : c.L ≤ normalizer ((⁅commutatorCore c.L,YC d c.L⁆ : Subgroup G) : Set G) := by
      intro l hl
      rw [mem_normalizer_iff_map_conj_eq,map_commutator,
        mem_normalizer_iff_map_conj_eq.mp (hLQ hl),
        mem_normalizer_iff_map_conj_eq.mp (hLC hl)]
    have he := eq_of_sup_center_of_generated_core _ _ _ _ hQ hQL (map_subtype_le _) hZL
      (le_normalizer_iff_commutator_le_left.mp hCQ) hn
      (ResidualAlternatives.sup_center_of_moving c n hfull)
    exact (core_not_conjugation_invariant d c.L m hU hfix t hex
      (core_invariant_of_both_moving d c m hi hSQ hSYL hfix hfullL he t ht hex)).elim
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearThree.OriginalSource.FullCover.Dynamics
