module
public import CFSG.Quasithin.ChapterB.Section05.QuotientComponents.ComponentLifting.Source
public import CFSG.Quasithin.ChapterB.Section06To07.FFClassification.ReducedSolvability
public import Theory.Quasithin.Rank
/-!
# Actual component lifts in a nonsolvable minimal parabolic

After removing the original two-core, the action kernel lies in the odd
Frattini subgroup. The solvable radical is then nilpotent, so the proved
B.5 component-lifting theorem applies with genuine A.3.6. Lifting back
through O₂ constructs the actual C-component, its quasisimple intrinsic
two-core quotient, and its equality with the solvable residual of the
original factor preimage. The final consumer uses the given reduced module.

Source: Aschbacher–Smith C.1.26, p.132, and B.6.8, pp.114–115.
-/
public section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.ChapterC.RankOne.ChiProduct.SelectedRankOne
open ChapterB Chapter1.Section02
universe u
variable {G D : Type u} [Group G] [Finite G] [Group D] [Finite D]

omit [Finite D] in
/-- The original two-core quotient retains the action's odd nilpotent kernel. -/
theorem reduced_action_twoCore_lift
    (T : Sylow 2 G) (hP : IsMinimalParabolicOver T ⊤)
    (q : G →* D) (hq : Function.Surjective q)
    (hk : q.ker ≤ minimalParabolicCore T hP) (h2 : pCore 2 D = ⊥) :
    ∃ f : (G ⧸ pCore 2 G) →* D, Function.Surjective f ∧
      f.comp (QuotientGroup.mk' (pCore 2 G)) = q ∧
      f.ker ≤ frattini (G ⧸ pCore 2 G) ∧ Odd (Nat.card f.ker) := by
  let Q := pCore 2 G
  let π := QuotientGroup.mk' Q
  have hQ : Q ≤ q.ker := by
    apply (Subgroup.map_eq_bot_iff Q).mp
    apply le_bot_iff.mp
    rw [←h2]
    exact le_sSup ⟨Normal.map inferInstance q hq, pCore_isPGroup.map q⟩
  let f : G ⧸ Q →* D := QuotientGroup.lift Q q hQ
  have hf : Function.Surjective f := QuotientGroup.lift_surjective_of_surjective _ _ hq _
  have hfk : f.ker ≤ (minimalParabolicCore T hP).map π := by
    intro x hx
    obtain ⟨g,rfl⟩ := QuotientGroup.mk'_surjective Q x
    exact mem_map_of_mem π (hk hx)
  have ho : Odd (Nat.card f.ker) :=
    (minimalParabolic_coreImage_odd T hP).of_dvd_nat (card_dvd_of_le hfk)
  refine ⟨f,hf,rfl,?_,ho⟩
  exact hfk.trans_eq (RankOneBaumann.coreImage_frattini T hP)

/-- A genuine component of the action lifts to a C-component whose intrinsic
 two-core quotient is quasisimple. -/
theorem exists_component_lift_of_reduced_action
    {C : GroupClass.{u}} (h36 : A36Input C) (hG : IsSQTK C G)
    (T : Sylow 2 G) (hP : IsMinimalParabolicOver T ⊤)
    (q : G →* D) (hq : Function.Surjective q)
    (hk : q.ker ≤ minimalParabolicCore T hP)
    (h2 : pCore 2 D = ⊥) (hs : ¬ Group.IsSolvable G)
    (A : Subgroup D) (hA : IsComponent D A) :
    ∃ L : Subgroup G, L.IsCComponent ∧ L.map q = A ∧
      IsQuasisimple (L ⧸ pCore 2 L) ∧
      (solvableResidual (A.comap q)).map (A.comap q).subtype = L := by
  let Q := pCore 2 G
  let π := QuotientGroup.mk' Q
  obtain ⟨f,hf,hcomp,hker,ho⟩ := reduced_action_twoCore_lift T hP q hq hk h2
  let : Group.IsNilpotent (frattini (G ⧸ Q)) := frattini_nilpotent
  let : Group.IsNilpotent f.ker :=
    Subgroup.isNilpotent_of_ker_le_center (inclusion hker)
      (by rw [(MonoidHom.ker_eq_bot_iff _).mpr (inclusion_injective hker)]; exact bot_le)
  let : Group.IsNilpotent Q := pCore_isNilpotent (p := 2)
  let : Group.IsSolvable π.ker := by rw [QuotientGroup.ker_mk']; infer_instance
  have hrad : solvableRadical (G ⧸ Q) = (minimalParabolicCore T hP).map π := by
    rw [minimalParabolic_nonsolvable_core_eq_radical T hP hs,
      ←comap_solvableRadical_eq_of_solvable_ker π (QuotientGroup.mk'_surjective Q),
      map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective Q)]
  let : Group.IsNilpotent (solvableRadical (G ⧸ Q)) :=
    hrad.symm ▸ minimalParabolic_coreImage_nilpotent T hP
  let : Group.IsSolvable ((fittingSubgroup D).comap f) :=
    isSolvable_comap_of_solvable_ker f _
  have hfitrad : (fittingSubgroup D).comap f ≤ solvableRadical (G ⧸ Q) :=
    le_solvableRadical _ inferInstance inferInstance
  let : Group.IsNilpotent ((fittingSubgroup D).comap f) :=
    Subgroup.isNilpotent_of_ker_le_center (inclusion hfitrad)
      (by rw [(MonoidHom.ker_eq_bot_iff _).mpr (inclusion_injective hfitrad)]; exact bot_le)
  have hQG : IsSQTK C (G ⧸ Q) := by
    refine ⟨?_,hG.isKGroup.quotient Q⟩
    intro p hp hpodd
    let : Fact p.Prime := ⟨hp⟩
    exact (primeRank_quotient_le_of_isTwoGroup p hpodd Q pCore_isPGroup).trans
      (hG.stronglyQuasithin p hp hpodd)
  obtain ⟨M,hM,hMf⟩ := ComponentLifting.component_lifts h36 hQG f hf ho A hA
  obtain ⟨hL,hLm⟩ := cComponent_residual_preimage π (QuotientGroup.mk'_surjective Q) hM.isCComponent
  let L := (solvableResidual (M.comap π)).map (M.comap π).subtype
  change L.IsCComponent at hL
  change L.map π = M at hLm
  have hLq : L.map q = A := by rw [←hcomp,←map_map,hLm,hMf]
  have hki : (π.subgroupMap L).ker = pCore 2 L := by
    rw [ker_subgroupMap,QuotientGroup.ker_mk',pCore_subnormal_eq_comap 2 hL.subnormal]
    rfl
  let e : (L ⧸ pCore 2 L) ≃* M :=
    ((QuotientGroup.quotientMulEquivOfEq hki.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective (π.subgroupMap L)
        (π.subgroupMap_surjective L))).trans (MulEquiv.subgroupCongr hLm)
  let := hM.2
  let : Group.IsSolvable (minimalParabolicCore T hP) := minimalParabolic_core_solvable T hP
  let : Group.IsSolvable q.ker := Group.isSolvable_of_isSolvable_injective
    (inclusion_injective hk)
  have hpre : A.comap q = L ⊔ q.ker := by rw [←hLq,comap_map_eq]
  have hcanonical : (solvableResidual (A.comap q)).map (A.comap q).subtype = L := by
    rw [hpre]
    exact hL.solvableResidual_sup_eq q.ker le_normalizer_of_normal
  exact ⟨L,hL,hLq,IsQuasisimple.of_mulEquiv e.symm,hcanonical⟩
/-- Literal consumer on the reduced module and its original action quotient. -/
theorem exists_component_lift_of_reduced_module
    {C : GroupClass.{u}} (h36 : A36Input C) (hG : IsSQTK C G)
    (T : Sylow 2 G) (hP : IsMinimalParabolicOver T ⊤)
    (U : Subgroup G) [U.Normal] (hU : IsPReduced 2 U)
    (hJ : ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (U : Set G))
    (q : G →* D) (hq : Function.Surjective q)
    (hk : q.ker = centralizer (U : Set G)) (hs : ¬ Group.IsSolvable G)
    (A : Subgroup D) (hA : IsComponent D A) :
    ∃ L : Subgroup G, L.IsCComponent ∧ L.map q = A ∧
      IsQuasisimple (L ⧸ pCore 2 L) ∧
      (solvableResidual (A.comap q)).map (A.comap q).subtype = L := by
  have hcore : pCore 2 D = ⊥ := by
    let e := (QuotientGroup.quotientMulEquivOfEq hk.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective q hq)
    rw [← pCore_map_iso 2 e,hU.quotient_pCore_eq_bot,Subgroup.map_bot]
  exact exists_component_lift_of_reduced_action h36 hG T hP q hq
    (hk ▸ RankOneBaumann.reduced_centralizer_le_core T hP U hU hJ) hcore hs A hA
end CFSG.Quasithin.ChapterC.RankOne.ChiProduct.SelectedRankOne
