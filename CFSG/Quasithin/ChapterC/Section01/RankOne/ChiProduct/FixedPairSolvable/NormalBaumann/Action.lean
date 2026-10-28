module
public import CFSG.Quasithin.ChapterC.Section01.RankOne.ChiProduct.FixedPairSolvable.Single.LocalClass
public import CFSG.Quasithin.ChapterB.Section01.SolvableStructure.OffenderProducts.AbelianSylow

/-!
# Abelian Sylow action on the normal residual--Baumann join

Even when the original Sylow exchanges two natural factors, the Baumann
image lies in their internal S₃ product and is elementary abelian. On the
normal group E=O²(G)Baum(T), the full original action kernel centralizes the
omega-center closure of this Baumann Sylow. Its action on that closure is
therefore abelian. The global alpha splitting also bounds that closure by
the original module times the centralizer of O²(G).

Source: Aschbacher--Smith B.6.10, E.2.3 and C.1.26--28.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterC.RankOne.ChiProduct.FixedPairSolvable.NormalBaumann
open ChapterB SelectedRankOne
variable {G : Type*} [Group G] [Finite G]

theorem exists_abelian_baumann_action
    (T : Sylow 2 G) (hP : IsMinimalParabolicOver T ⊤)
    (U : Subgroup G) [U.Normal] [IsElementaryAbelian 2 U] (hU : IsPReduced 2 U)
    (hJ : ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (U : Set G))
    (hrank : primeRank 3 G ≤ 2)
    (hsolv : Group.IsSolvable (G ⧸ centralizer (U : Set G))) :
    let E := pResidual 2 G ⊔ baumann (T : Subgroup G)
    ∃ S : Sylow 2 E, (S : Subgroup E).map E.subtype = baumann (T : Subgroup G) ∧
      IsMulCommutative ((S : Subgroup E).map (QuotientGroup.mk' (centralizer
        (normalClosure (omegaOneCenterAmbient (S : Subgroup E) : Set E) : Set E)))) ∧
      (normalClosure (omegaOneCenterAmbient (S : Subgroup E) : Set E)).map E.subtype ≤
        U ⊔ centralizer (pResidual 2 G : Set G) := by
  let E := pResidual 2 G ⊔ baumann (T : Subgroup G)
  let q := QuotientGroup.mk' (centralizer (U : Set G))
  obtain ⟨d,hBY,hB,hker⟩ := solvable_baumann_kernel_and_layer T hP U hU q
    (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _) hU.quotient_pCore_eq_bot hJ hrank hsolv
  obtain ⟨S,hS⟩ := hB
  let W := normalClosure (omegaOneCenterAmbient (S : Subgroup E) : Set E)
  have hkW : (q.comp E.subtype).ker ≤ centralizer (W : Set E) :=
    restricted_kernel_centralizes_omegaClosure T q hker E le_rfl S hS
  have habq : IsMulCommutative ((S : Subgroup E).map (q.comp E.subtype)) := by
    rw [←Subgroup.map_map,hS]
    let : IsElementaryAbelian 2 ((baumann (T : Subgroup G)).map q) :=
      d.toSolvableFFFactors.two_subgroup_elementary _ ((T.isPGroup'.to_le inf_le_left).map q) hBY
    infer_instance
  have habW : IsMulCommutative ((S : Subgroup E).map (QuotientGroup.mk' (centralizer (W : Set E)))) := by
    apply commutator_self_eq_bot_iff.mp
    rw [←map_commutator]
    apply (Subgroup.map_eq_bot_iff _).mpr
    rw [QuotientGroup.ker_mk']
    apply le_trans _ hkW
    apply (Subgroup.map_eq_bot_iff _).mp
    rw [map_commutator]
    exact commutator_self_eq_bot_iff.mpr habq
  refine ⟨S,hS,habW,?_⟩
  rw [Single.omegaClosure_baumann_sylow_map T S hS]
  have ha := (RankOneBaumann.SolvableSource.source_solvable_baumann_sylow_and_alpha
    T hP U hU hJ hrank hsolv).2
  apply normalClosure_le_normal
  change thompsonAlpha (T : Subgroup G) ≤ U ⊔ centralizer (pResidual 2 G : Set G)
  rw [ha]
  exact sup_le (inf_le_right.trans le_sup_right) (inf_le_left.trans le_sup_left)
end CFSG.Quasithin.ChapterC.RankOne.ChiProduct.FixedPairSolvable.NormalBaumann
