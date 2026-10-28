module
public import CFSG.Quasithin.ChapterC.Section01.RankOne.ChiProduct.FixedPairSolvable.NormalBaumann.Marking
public import CFSG.Quasithin.ChapterC.Section01.RankOne.ChiProduct.SelectedRankOne.Support
public import CFSG.Quasithin.ChapterC.Section01.RankOne.Solvable.Source.Transport
public import Theory.GroupTheory.PResidual.NormalSubgroup

/-!
# The same cubic block above the normal Baumann join

A block of a normal subgroup is subnormal in the original group. The actual
Baumann Sylow carries the original Thompson subgroup, so movement transports
through the same inclusion. If its omega-center span lies in U C(O²(G)),
its nonzero commutator with the two-perfect block forces a nonzero original
U-commutator. The normal-module theorem identifies this with the block module.

Source: Aschbacher--Smith C.1.26--28, printed pp.132--134.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory
namespace CFSG.Quasithin.ChapterC.RankOne.ChiProduct.FixedPairSolvable.NormalBaumann
open ChapterB
variable {G : Type*} [Group G] [Finite G]

theorem moving_cubic_from_normal_baumann
    (T : Sylow 2 G) (E : Subgroup G) [E.Normal]
    (S : Sylow 2 E) (hS : (S : Subgroup E).map E.subtype = baumann (T : Subgroup G))
    (U : Subgroup G) [U.Normal] [IsElementaryAbelian 2 U]
    (hW : (normalClosure (omegaOneCenterAmbient (S : Subgroup E) : Set E)).map E.subtype ≤
      U ⊔ centralizer (pResidual 2 G : Set G))
    (K : Subgroup E) (hK : IsBlock K) (ha : IsAlternatingBlock K 3)
    (hm : K = ⁅K,elementaryAbelianMaxJ (S : Subgroup E)⁆)
    (hne : ⁅normalClosure (omegaOneCenterAmbient (S : Subgroup E) : Set E),K⁆ ≠ ⊥) :
    let A := K.map E.subtype
    IsBlock A ∧ IsAlternatingBlock A 3 ∧
      A = ⁅A,elementaryAbelianMaxJ (T : Subgroup G)⁆ ∧
      (blockU A).map A.subtype = ⁅U,A⁆ ∧ ⁅U,A⁆ ≠ ⊥ := by
  let A := K.map E.subtype
  let W := normalClosure (omegaOneCenterAmbient (S : Subgroup E) : Set E)
  let e : K ≃* A := K.equivMapOfInjective E.subtype E.subtype_injective
  have haA : IsAlternatingBlock A 3 := RankOne.Solvable.isAlternatingBlock_of_equiv e ha
  have hbA : IsBlock A := ⟨inferInstance,haA.2.1,
    hK.subnormal.trans' (inferInstance : E.Normal).isSubnormal⟩
  have hmA : A = ⁅A,elementaryAbelianMaxJ (T : Subgroup G)⁆ := by
    have hh := congrArg (Subgroup.map E.subtype) hm
    rwa [map_commutator,thompson_map T E S hS] at hh
  have hAR : A ≤ pResidual 2 G := le_pResidual_of_isPPerfect A hbA.short.twoPerfect
  have hneA : ⁅W.map E.subtype,A⁆ ≠ ⊥ := by
    rw [show A = K.map E.subtype from rfl,←map_commutator]
    exact fun hh => hne ((map_eq_bot_iff_of_injective _ E.subtype_injective).mp hh)
  have hneU : ⁅U,A⁆ ≠ ⊥ := by
    intro he
    apply hneA
    apply commutator_eq_bot_iff_le_centralizer.mpr
    exact hW.trans (sup_le (commutator_eq_bot_iff_le_centralizer.mp he) (centralizer_le hAR))
  exact ⟨hbA,haA,hmA,SelectedRankOne.blockU_eq_nontrivial_normal_module_commutator A U hbA hneU,hneU⟩
end CFSG.Quasithin.ChapterC.RankOne.ChiProduct.FixedPairSolvable.NormalBaumann
