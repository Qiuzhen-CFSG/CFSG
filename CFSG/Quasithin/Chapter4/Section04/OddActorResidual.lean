module
public import CFSG.Quasithin.Chapter4.Section04.PerfectCentralizer
public import CFSG.Quasithin.Chapter4.Section01.Maximality
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.Fundamental
public import Theory.GroupTheory.Commutator.CentralizingFactor
public import Theory.GroupTheory.CharacteristicCentralizerFusion

/-!
# The original odd actor fixes a covering residual containing the chosen module

For the original Section12.2 choice, the residual of C_L(B) covers L modulo
O2(L), contains the same V in its own two-core, and is generated on V by
commutators. Its normalization is proved only inside N(L) intersect N(B).
This supplies the actual covering subgroup for4.2.13 in the proof of4.4.6;
it does not assert the missing pushing-up uniqueness or odd-local catalogue.
Source: Aschbacher--Smith,4.4.5--6, printed p.620, with Remark4.4.2.
-/

public section
open Subgroup
open scoped Pointwise
namespace CFSG.Quasithin.Chapter4.Section04
variable {G:Type*} [Group G] [Finite G]

/-- The source L_B is the terminal derived subgroup of the actual fixed subgroup. -/
def oddActorResidual (L B:Subgroup G):Subgroup G:=
  (solvableResidual (L⊓centralizer (B:Set G):Subgroup G)).map
    (L⊓centralizer (B:Set G)).subtype

omit [Finite G] in
theorem oddActorResidual_le (L B:Subgroup G):oddActorResidual L B≤L⊓centralizer (B:Set G):=
  map_subtype_le _

omit [Finite G] in
theorem normalizes_oddActorResidual (L B:Subgroup G):
    normalizer (L:Set G)⊓normalizer (B:Set G)≤normalizer (oddActorResidual L B:Set G):=by
  have hh:normalizer (L:Set G)⊓normalizer (B:Set G)≤
      normalizer (L⊓centralizer (B:Set G):Set G):=
    (le_inf inf_le_left (inf_le_right.trans (normalizer_le_normalizer_centralizer B))).trans
      inf_normalizer_le_normalizer_inf
  exact hh.trans (normalizer_le_normalizer_characteristic_image
    (L⊓centralizer (B:Set G)) (solvableResidual (L⊓centralizer (B:Set G):Subgroup G)))

/-- The original chosen module survives unchanged in the fixed residual.
In particular this residual is a covering subgroup with nontrivial two-core,
as required at the entry to the genuine pushing-up theorem4.2.13. -/
theorem chosen_oddActorResidual_cover
    {K:GroupClass} {T:Sylow 2 G} {L V:Subgroup G}
    (h:Chapter12.Section02.Hypothesis1221 K T L)
    (D:Chapter12.Section02.ChosenModule T L V)
    (B:Subgroup G) (hBN:B≤normalizer (L:Set G))
    (hcomm:⁅B,L⁆≤L.pCoreIn 2) (hodd:Odd (Nat.card B))
    (hBV:B≤centralizer (V:Set G)) :
    (L:Set G)=(oddActorResidual L B:Set G)*(L.pCoreIn 2:Set G) ∧
    V=⁅V,oddActorResidual L B⁆ ∧ V≤(oddActorResidual L B).pCoreIn 2 ∧
    (oddActorResidual L B).pCoreIn 2≠⊥ := by
  let : Group.IsPerfect L:=Chapter1.mem_L_isPerfect h.maximal_faithful.1.1
  have hsect:B≤sectionCentralizer L:=(le_sectionCentralizer_iff B L).mpr ⟨hBN,hcomm⟩
  have hcover:(L:Set G)=(oddActorResidual L B:Set G)*(L.pCoreIn 2:Set G):=
    perfect_centralizer_cover L B hsect hodd
  have hQLT:L.pCoreIn 2≤(L⊔(T:Subgroup G)).pCoreIn 2:=
    le_pCoreIn_of_normalizes (isPGroup_pCoreIn 2 L)
      ((pCoreIn_le 2 L).trans le_sup_left)
      ((sup_le L.le_normalizer D.sylow_normalizes_component).trans
        (normalizer_le_normalizer_characteristic_image L (pCore 2 L)))
  have hQV:L.pCoreIn 2≤centralizer (V:Set G):=hQLT.trans D.core_centralizes
  have he:V=⁅V,oddActorResidual L B⁆:=D.eq_commutator.trans
    (commutator_eq_of_product_centralizing_factor hcover (le_centralizer_iff.mp hQV))
  have hVC:V≤L⊓centralizer (B:Set G):=le_inf D.le_component (le_centralizer_iff.mp hBV)
  have hVL:V≤normalizer (oddActorResidual L B:Set G):=hVC.trans
    ((L⊓centralizer (B:Set G)).le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image
        (L⊓centralizer (B:Set G)) (solvableResidual (L⊓centralizer (B:Set G):Subgroup G))))
  have hVLB:V≤oddActorResidual L B:=he ▸ le_normalizer_iff_commutator_le_right.mp hVL
  let :=D.elementary
  have hcore:V≤(oddActorResidual L B).pCoreIn 2:=le_pCoreIn_of_normalizes
    (IsElementaryAbelian.isPGroup 2 V) hVLB ((oddActorResidual_le L B).trans inf_le_left |>.trans D.normalizes)
  exact ⟨hcover,he,hcore,fun hb=>D.ne_bot (bot_unique (hb ▸ hcore))⟩
/-- The literal covering input of Notation4.2.11, using O2(LT) rather than
substituting the component's own core for that denominator. -/
theorem chosen_oddActorResidual_pushingUp_input
    {K:GroupClass} {T:Sylow 2 G} {L V:Subgroup G}
    (h:Chapter12.Section02.Hypothesis1221 K T L)
    (D:Chapter12.Section02.ChosenModule T L V)
    (B:Subgroup G) (hBN:B≤normalizer (L:Set G))
    (hcomm:⁅B,L⁆≤L.pCoreIn 2) (hodd:Odd (Nat.card B))
    (hBV:B≤centralizer (V:Set G)) :
    oddActorResidual L B≤normalizer (L:Set G) ∧
    (L:Set G)⊆(oddActorResidual L B:Set G)*((L⊔(T:Subgroup G)).pCoreIn 2:Set G) ∧
    (oddActorResidual L B).pCoreIn 2≠⊥ ∧
    V=⁅V,oddActorResidual L B⁆ ∧ V≤(oddActorResidual L B).pCoreIn 2 := by
  obtain ⟨hc,hV,hcore,hne⟩:=chosen_oddActorResidual_cover h D B hBN hcomm hodd hBV
  have hQLT:L.pCoreIn 2≤(L⊔(T:Subgroup G)).pCoreIn 2:=
    le_pCoreIn_of_normalizes (isPGroup_pCoreIn 2 L)
      ((pCoreIn_le 2 L).trans le_sup_left)
      ((sup_le L.le_normalizer D.sylow_normalizes_component).trans
        (normalizer_le_normalizer_characteristic_image L (pCore 2 L)))
  refine ⟨((oddActorResidual_le L B).trans inf_le_left).trans L.le_normalizer,
    ?_,hne,hV,hcore⟩
  rw [hc]
  exact Set.mul_subset_mul Set.Subset.rfl hQLT

end CFSG.Quasithin.Chapter4.Section04
