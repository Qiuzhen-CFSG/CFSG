module
public import CFSG.Quasithin.ChapterC.Section01.RankOne.ChiProduct.SelectedRankOne.PairedBlockSteps
public import CFSG.Quasithin.ChapterC.Section01.RankOne.ChiProduct.FixedPairSolvable.Selection

/-!
# The selected paired component escapes the original fixed pair

The full original Sylow subgroup conjugates the selected component through
an orbit generating the two-residual. Thus it escapes every proper Sylow
overgroup, including the control subgroup of a previously chosen pair.
No new characteristic pair or characteristic-normalizer hypothesis is used.

Source: Aschbacher--Smith C.1.26--28, printed pp.132--134.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory Representation
namespace CFSG.Quasithin.ChapterC.RankOne.ChiProduct.FixedPairNonsolvable
open ChapterB GlaubermanNiles SelectedRankOne FixedPairSolvable
universe u
variable {G H : Type u} [Group G] [Finite G] [Group H] [Finite H]

theorem selected_component_outside_sylow_overgroup
    (T : Sylow 2 G) (hP : IsMinimalParabolicOver T ⊤)
    (U : Subgroup G) [U.Normal] [IsElementaryAbelian 2 U] (hU : IsPReduced 2 U)
    (hJ : ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (U : Set G))
    (q : G →* H) (hq : Function.Surjective q) (hk : q.ker = centralizer (U : Set G))
    (Y A : Subgroup H) [Y.Normal]
    (hJA : (elementaryAbelianMaxJ (T : Subgroup G)).map q ≤ Y)
    (hYA : Y ≤ normalizer (A : Set H))
    (L : Subgroup G) (hL : L.IsCComponent)
    (hcan : (solvableResidual (A.comap q)).map (A.comap q).subtype = L)
    (M : Subgroup G) (hTM : (T : Subgroup G) ≤ M)
    (hM : M ≠ ⊤) : ¬ L ≤ M := by
  let Q := Y.comap q
  let := hL.perfect
  let : Nontrivial L := (Subgroup.nontrivial_iff_ne_bot L).mpr hL.ne_bot
  have hn : Q ≤ normalizer (L : Set G) := selected_component_normalized q A L Q hcan
    ((map_comap_le q Y).trans hYA)
  have hres : pResidual 2 G ≤ Q := map_le_iff_le_comap.mp
    (RankOneBaumann.residual_image_le_normal_thompson_layer T hP U hU hJ q hq hk Y hJA)
  have hgen : Q ⊔ (T : Subgroup G) = ⊤ := top_unique
    ((pResidual_sup_sylow_eq_top T).symm.le.trans (sup_le_sup_right hres _))
  have horbit := source_factor_orbit_eq_residual T hP Q L hn hgen
  intro hLM
  have hRM : pResidual 2 G ≤ M := by
    rw [←horbit]
    apply iSup_le
    intro t
    rintro x ⟨l,hl,rfl⟩
    change (t:G)*l*(t:G)⁻¹ ∈ M
    exact M.mul_mem (M.mul_mem (hTM t.property) (hLM hl)) (M.inv_mem (hTM t.property))
  exact hM (top_unique ((pResidual_sup_sylow_eq_top T).symm.le.trans (sup_le hRM hTM)))
end CFSG.Quasithin.ChapterC.RankOne.ChiProduct.FixedPairNonsolvable
