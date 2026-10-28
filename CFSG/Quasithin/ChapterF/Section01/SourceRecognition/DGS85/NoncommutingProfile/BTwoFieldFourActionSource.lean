module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.NoncommutingProfile.BTwoFieldFourSplittingSource
public import Theory.SpecificGroups.MinusExtraspecial.AlternatingAction
public import Theory.GroupTheory.GeneralizedFitting.SylowOvergroup
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.ExceptionalParabolics.FirstParabolic.RadicalModel

/-!
# The original field-four action and the J₂ central quotient

The order-sixty complement in the original beta enlargement acts faithfully
on its actual minus-extraspecial core. Its five singular central cosets give
an explicit alternating action, retaining the original PSL₂(4) quotient
marking. The resulting semidirect-product equivalence records the literal
core and complement coordinates. The same Cartan and both invariant
four-groups from the splitting construction are retained with this action.

The enlargement's center is the original beta central involution. Its full
conjugation image consists of the minus-core automorphisms inducing even
permutations of the five singular points. The native J₂ first endpoint has
the same conjugation image. This constructs an equivalence of their actual
central quotients, with both the conjugation equation and the original core
inclusion square. Source beta corresponds to the first J₂ endpoint.

This does not lift the central-quotient map to an equivalence of the full
endpoints, construct the full Borel map, or finish the source path arguments.
Those remain the subsequent steps of the field-four recognition exercise.
Source: Delgado--Goldschmidt--Stellmacher, Groups and Graphs (1985),
(5.14)--(5.16), pp.116--117 and (10.9), p.163.
-/

public noncomputable section
open Subgroup
open scoped Pointwise commutatorElement MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.ChapterF.Source.DGS85.NoncommutingProfile.Reduction
open Subgroup.CosetGeometry.RankTwo Theory.GroupTheory.AmalgamGraph Noncommuting DGS85.Reduction
open Theory.GroupTheory
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}
variable {k W : Type*} [Field k] [Finite k] [CharP k 2]
  [AddCommGroup W] [Module (ZMod 2) W]
variable {K : Type*} [Field K] [Finite K] [CharP K 2]
local notation "F₀" => reducedFamily L S
local notation "α" => base F₀ false
local notation "β" => base F₀ true
local instance fieldFourSplitActionAlgebra {k₀ : Type*} [Field k₀] [CharP k₀ 2] : Algebra (ZMod 2) k₀ :=
  ZMod.algebra k₀ 2

/-- The split original enlargement, with its faithful action and actual central quotient. -/
theorem original_bTwo_field_four_split_action
    (h : HypothesisF11 L S) (hb : b F₀ = 2) {u t : Vertex F₀}
    (c : BTwoCenterActionData F₀ α β u k W)
    (hactor : c.actor = graphLocalGroup F₀ α)
    (hcentral : Z F₀ β ≤ centerIn (graphLocalGroup F₀ β))
    (ht : (graph F₀).Adj α t) (hne : t ≠ β)
    (hcomm : ⁅V F₀ β 1,Q F₀ β⁆ = Z F₀ β)
    (hnot : ¬ stabilizer F₀ α ≤ normalizer
      ((Q F₀ β ⊓ Q F₀ α : Subgroup (G₀ L S)) : Set (G₀ L S)))
    (e : (L 1 ⧸ pCore 2 (L 1)) ≃* PSL(2,K))
    (hD : (parabolic L S 1).pCoreIn 2 ⊓ (Q F₀ t).map (G₀ L S).subtype =
      (Z F₀ α).map (G₀ L S).subtype)
    (E : W ≃ₗ[ZMod 2] (Fin 2 → k)) (hK : Nat.card K = 4) :
    let X := enlargedEndpoint L S 1
    let N := pCore 2 X
    Nat.card X = 1920 ∧ Nat.card ((commonBorel L S).pCoreIn 2) = 128 ∧
      Nat.card (X ⊓ commonBorel L S : Subgroup G) = 384 ∧
      ∃ eX : (X ⧸ N) ≃* PSL(2,K),
        (∀ x : L 1, eX (QuotientGroup.mk' N
          (inclusion ((local_le_starredParabolic 1).trans le_sup_left) x)) =
            e (QuotientGroup.mk' (pCore 2 (L 1)) x)) ∧
        ∃ (a : commonBorel L S) (A B : Subgroup G) (C : Subgroup X),
          orderOf a = 3 ∧
          (a : G) ∈ centralizer ((Z F₀ α).map (G₀ L S).subtype : Set G) ∧
          Disjoint ((commonBorel L S).pCoreIn 2) (zpowers (a : G)) ∧
          (commonBorel L S).pCoreIn 2 ⊔ zpowers (a : G) = X ⊓ commonBorel L S ∧
          A ≠ B ∧
          (∀ D ∈ ({A,B} : Set (Subgroup G)),
            D ≤ (parabolic L S 0).pCoreIn 2 ∧ Nat.card D = 4 ∧
            IsElementaryAbelian 2 D ∧ Disjoint ((parabolic L S 1).pCoreIn 2) D ∧
            (parabolic L S 1).pCoreIn 2 ⊔ D = (commonBorel L S).pCoreIn 2 ∧
            (a : G) ∈ normalizer (D : Set G)) ∧
          N.IsComplement' C ∧ Nat.card C = 60 ∧ (a : G) ∈ C.map X.subtype ∧
          ∃ (eC : C ≃* PSL(2,K)) (eN : N ≃* MinusExtraspecial.Model),
            (∀ x : C, eC x = eX (QuotientGroup.mk' N (x : X))) ∧
            (center X).map X.subtype = (Z F₀ β).map (G₀ L S).subtype ∧
            let φ := MinusExtraspecial.AlternatingAction.complementAction N eN C eC
            Function.Injective φ ∧
            ∃ d : PSL(2,K) ≃* alternatingGroup (Fin 5),
              (∀ x : X,
                MinusExtraspecial.FixedFourCalculation.Outside.fivePointAction
                  (MinusExtraspecial.AlternatingAction.coreAction N eN x) =
                    (d (eX (QuotientGroup.mk' N x)) : Equiv.Perm (Fin 5))) ∧
              (∀ x : PSL(2,K),
                MinusExtraspecial.FixedFourCalculation.Outside.fivePointAction (φ x) =
                  (d x : Equiv.Perm (Fin 5))) ∧
              ∃ f : X ≃* MinusExtraspecial.Model ⋊[φ] PSL(2,K),
                (∀ x, f.symm x = (eN.symm x.left : X) * (eC.symm x.right : X)) ∧
                ∃ z : (X ⧸ center X) ≃*
                    MinusExtraspecial.AlternatingAction.evenAutomorphisms,
                  (∀ x : X, (z (QuotientGroup.mk' (center X) x) :
                    MulAut MinusExtraspecial.Model) =
                      MinusExtraspecial.AlternatingAction.coreAction N eN x) ∧
                  ∃ j : (X ⧸ center X) ≃*
                      (Sporadic.LeechRelated.J2.ExceptionalParabolics.Seed.l₁ ⧸
                        center Sporadic.LeechRelated.J2.ExceptionalParabolics.Seed.l₁),
                    (∀ x : X,
                      (Sporadic.LeechRelated.J2.ExceptionalParabolics.FirstParabolic.centralActionEquiv
                        (j (QuotientGroup.mk' (center X) x)) : MulAut MinusExtraspecial.Model) =
                          MinusExtraspecial.AlternatingAction.coreAction N eN x) ∧
                    ∀ n : N, j (QuotientGroup.mk' (center X) (n : X)) =
                      QuotientGroup.mk' _
                        (Sporadic.LeechRelated.J2.ExceptionalParabolics.FirstParabolic.coreModelEquiv.symm
                          (eN n) : Sporadic.LeechRelated.J2.ExceptionalParabolics.Seed.l₁) := by
  let X := enlargedEndpoint L S 1
  let N := pCore 2 X
  let Q₁ := (parabolic L S 1).pCoreIn 2
  let : Finite (parabolic L S 1) := h.finite_parabolic 1
  have hXP : X ≤ parabolic L S 1 := sup_le (starredParabolic_le 1)
    ((pCoreIn_le 2 _).trans (commonBorel_le_parabolic 1))
  let : Finite X := Finite.of_injective (inclusion hXP) (inclusion_injective _)
  obtain ⟨hXcard,hTcard,hBcard,eX,heX,a,A,B,C,ha,hac,hd,hB,hAB,hABs,
    hC,hCcard,haC,eC,heC⟩ := original_bTwo_field_four_split_enlargement
      h hb c hactor hcentral ht hne hcomm hnot e hD E hK
  obtain ⟨_,⟨eQ⟩⟩ := original_bTwo_field_four_beta_recognition
    h hb c hactor hcentral ht hne hcomm hnot e hD E hK
  have hNmap : N.map X.subtype = Q₁ := enlargedEndpoint_core h 1
  let eN : N ≃* MinusExtraspecial.Model :=
    ((N.equivMapOfInjective X.subtype X.subtype_injective).trans
      (MulEquiv.subgroupCongr hNmap)).trans eQ
  have hcP : centralizer (pCore 2 (parabolic L S 1) : Set (parabolic L S 1)) ≤
      pCore 2 (parabolic L S 1) :=
    (ChapterA.generalizedFitting_eq_pCore_iff 2).mp (h.characteristic_two 1)
  have hQP : pCore 2 (parabolic L S 1) ≤ X.subgroupOf (parabolic L S 1) := by
    intro q hq
    have hh : (q : G) ∈ Q₁ := mem_map_of_mem (parabolic L S 1).subtype hq
    rw [←hNmap] at hh
    exact (map_subtype_le N) hh
  have hcX : centralizer (N : Set X) ≤ N := by
    have hh := centralizer_pCore_le_of_pCore_le (X.subgroupOf (parabolic L S 1)) hcP hQP
    exact (Theory.Quasithin.centralizer_pCore_le_iff 2 (subgroupOfEquivOfLe hXP)).mp hh
  have hZ : (center X).map X.subtype = (Z F₀ β).map (G₀ L S).subtype := by
    let : IsExtraspecial 2 N := IsExtraspecial.of_mulEquiv eN.symm inferInstance
    rw [MinusExtraspecial.AlternatingAction.center_eq_center_image N eN hcX,
      ←IsExtraspecial.commutator_eq_center (p := 2),map_subtype_commutator,
      map_commutator,hNmap]
    exact (original_bTwo_beta_core_frattini h hb c hactor hcentral ht hne hcomm).2
  obtain ⟨eA⟩ := Matrix.ProjectiveSpecialLinearGroup.equiv_alternatingGroup_of_card_four hK
  let eXA := eX.trans eA
  obtain ⟨d,hpoint⟩ := MinusExtraspecial.AlternatingAction.exists_quotient_marking N eN hcX eXA
  let dK := eX.symm.trans d
  have hdK (x : X) :
      MinusExtraspecial.FixedFourCalculation.Outside.fivePointAction
        (MinusExtraspecial.AlternatingAction.coreAction N eN x) =
          (dK (eX (QuotientGroup.mk' N x)) : Equiv.Perm (Fin 5)) := by
    simpa only [dK,MulEquiv.trans_apply,eX.symm_apply_apply] using (hpoint x).symm
  let z := MinusExtraspecial.AlternatingAction.centralQuotientEquiv N eN hcX eXA
  let j := z.trans
    Sporadic.LeechRelated.J2.ExceptionalParabolics.FirstParabolic.centralActionEquiv.symm
  have hj (x : X) :
      (Sporadic.LeechRelated.J2.ExceptionalParabolics.FirstParabolic.centralActionEquiv
        (j (QuotientGroup.mk' (center X) x)) : MulAut MinusExtraspecial.Model) =
          MinusExtraspecial.AlternatingAction.coreAction N eN x := by
    simp only [j,MulEquiv.trans_apply,MulEquiv.apply_symm_apply]
    exact MinusExtraspecial.AlternatingAction.centralQuotientEquiv_apply N eN hcX eXA x
  refine ⟨hXcard,hTcard,hBcard,eX,heX,a,A,B,C,ha,hac,hd,hB,hAB,hABs,
    hC,hCcard,haC,eC,eN,heC,hZ,?_,dK,hdK,?_,
    MinusExtraspecial.AlternatingAction.splitEquiv N eN C hC eC,
    MinusExtraspecial.AlternatingAction.splitEquiv_symm_apply N eN C hC eC,
    z,MinusExtraspecial.AlternatingAction.centralQuotientEquiv_apply N eN hcX eXA,
    j,hj,?_⟩
  · exact MinusExtraspecial.AlternatingAction.complementAction_injective N eN hcX C hC eC
  · intro x
    change MinusExtraspecial.FixedFourCalculation.Outside.fivePointAction
      (MinusExtraspecial.AlternatingAction.coreAction N eN (eC.symm x : X)) = _
    rw [hdK,←heC,eC.apply_symm_apply]
  · intro n
    apply Sporadic.LeechRelated.J2.ExceptionalParabolics.FirstParabolic.centralActionEquiv.injective
    apply Subtype.ext
    rw [hj,Sporadic.LeechRelated.J2.ExceptionalParabolics.FirstParabolic.centralActionEquiv_apply,
      MinusExtraspecial.AlternatingAction.coreAction_subtype,
      MinusExtraspecial.AlternatingAction.coreAction_subtype,MulEquiv.apply_symm_apply]


end CFSG.Quasithin.ChapterF.Source.DGS85.NoncommutingProfile.Reduction
