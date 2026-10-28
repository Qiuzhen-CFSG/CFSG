module

public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.LocalRelations.SylowGeneration
public import Theory.GroupTheory.PCoreImage

/-!
# Consequences of the orthogonal residual calculation

The abelian action image of `Y` makes `N_Y(E)` normal in `Y`;
characteristicity of its two-residual gives `Y_E ⊴ Y T_E`.
Separately, the literal product `Y=Y_E Y_F O₂(Y)` generates `M`
from `Y_F` and `T`: conjugation by `s∈T` supplies `Y_E`, and the
normal two-core of `Y` lies in `T`.

These implications isolate the remaining finite orthogonal calculation:
the abelian image, literal line product and normalizer of `T_E`
still have to be supplied before the local-relations assembly is complete.
All residuals, cores and relative normality use the existing constructions.

Source: Aschbacher–Smith, combined manuscript (1 March 2004),
15.3.7 and the proof of 15.3.68, printed pp.1122 and 1154.
-/

public section

open Subgroup
namespace CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.LocalRelations
variable {G : Type*} [Group G] [Finite G]
/-- The abelian action image of Y makes its line residual normal in Y T_E. -/
theorem lineY_normalized_by_local_product (Y T V E : Subgroup G)
    (hEV : E ≤ V) (hTY : T ≤ normalizer (Y : Set G))
    (hcomm : ⁅Y,Y⁆ ≤ centralizer (V : Set G)) :
    Y ⊔ lineT T E ≤ normalizer (lineY Y E : Set G) := by
  have hN : Y ≤ normalizer (Y ⊓ lineNormalizer E : Set G) := by
    apply (le_normalizer_iff_commutator_le_right (H := Y) (K := Y ⊓ lineNormalizer E)).mpr
    apply le_inf
    · exact le_normalizer_iff_commutator_le_left.mp (inf_le_left.trans Y.le_normalizer)
    · exact (commutator_mono le_rfl inf_le_left).trans
        (hcomm.trans ((centralizer_le hEV).trans (centralizer_le_normalizer (E : Set G))))
  apply sup_le ?_ (lineT_le_normalizer_lineY Y T E hTY)
  intro y hy
  apply mem_normalizer_iff_map_conj_eq.mpr
  exact map_twoResidualAmbient_of_subgroup_image (Y ⊓ lineNormalizer E)
    (MulAut.conj y).toMonoidHom (Y ⊓ lineNormalizer E)
    (mem_normalizer_iff_map_conj_eq.mp (hN hy))

theorem lineY_normal_in_local_product (Y T V E : Subgroup G)
    (hEV : E ≤ V) (hTY : T ≤ normalizer (Y : Set G))
    (hcomm : ⁅Y,Y⁆ ≤ centralizer (V : Set G)) :
    ((lineY Y E).subgroupOf (Y ⊔ lineT T E)).Normal :=
  (normal_subgroupOf_iff_le_normalizer ((lineY_le Y E).trans inf_le_left |>.trans le_sup_left)).mpr
    (lineY_normalized_by_local_product Y T V E hEV hTY hcomm)
end CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.LocalRelations

open Subgroup
open scoped Pointwise
namespace CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.LocalRelations
variable {G : Type*} [Group G] [Finite G]

/-- The literal line product generates M together with the fixed Sylow group. -/
theorem generate_localGroup_from_line_product (T : Sylow 2 G) (M Y E : Subgroup G)
    (hTM : (T : Subgroup G) ≤ M) (hYM : Y ≤ M)
    (hMY : M ≤ normalizer (Y : Set G)) (hM : M = Y ⊔ (T : Subgroup G))
    (s : G) (hs : s ∈ T)
    (hprod : (Y : Set G) = (lineY Y E : Set G) * (lineY Y (otherLine E s) : Set G) *
      (Stellmacher.twoCoreAmbient Y : Set G)) :
    lineY Y (otherLine E s) ⊔ (T : Subgroup G) = M := by
  let H := lineY Y (otherLine E s) ⊔ (T : Subgroup G)
  have hT : (T : Subgroup G) ≤ H := le_sup_right
  have hF : lineY Y (otherLine E s) ≤ H := le_sup_left
  have hE : lineY Y E ≤ H := by
    intro y hy
    have hyF : (MulAut.conj s⁻¹) y ∈ lineY Y (otherLine E s) := by
      rw [lineY_otherLine Y E s (hMY (hTM hs))]
      exact mem_map_of_mem _ hy
    have hh := H.mul_mem (H.mul_mem (hT hs) (hF hyF)) (H.inv_mem (hT hs))
    simpa [MulAut.conj_apply, mul_assoc] using hh
  have hQ : Stellmacher.twoCoreAmbient Y ≤ (T : Subgroup G) := by
    have hQM := pCoreIn_mono_of_normalizes hYM hMY (p := 2)
    have hQT := map_mono (f := M.subtype) (pCore_isPGroup.le_sylow_of_normal (T.subtype hTM))
    rw [Sylow.coe_subtype, map_subgroupOf_eq_of_le hTM] at hQT
    exact hQM.trans hQT
  apply le_antisymm
  · exact sup_le ((lineY_le Y (otherLine E s)).trans inf_le_left |>.trans hYM) hTM
  · rw [hM]
    apply sup_le ?_ hT
    intro y hy
    rw [← SetLike.mem_coe, hprod] at hy
    obtain ⟨a, ⟨e, he, f, hf, rfl⟩, q, hq, rfl⟩ := hy
    exact H.mul_mem (H.mul_mem (hE he) (hF hf)) (hT (hQ hq))
end CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.LocalRelations
