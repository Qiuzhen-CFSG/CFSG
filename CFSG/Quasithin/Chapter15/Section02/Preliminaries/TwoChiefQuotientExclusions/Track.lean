module
public import CFSG.Quasithin.Chapter15.Section02.Preliminaries.TwoChiefQuotientExclusions.FirstParabolic
public import Theory.GroupTheory.SymmetricThreeTwoCoreStructure
public import CFSG.Quasithin.ChapterF.Section07.Track
public import Theory.GroupTheory.ReducedNormal.Equiv
public import CFSG.Quasithin.Chapter15.Section02.SourceChosenOppositeTrack.Action
public import CFSG.Quasithin.Chapter15.Section02.Preliminaries.TwoChiefQuotientExclusions.Quintic

/-!
# The literal Chapter 15 quintic graph and its odd critical track

The vertices are YT and H, with degrees five and three and whole overlap
T. The chosen four-space V is transported through the exact inclusions
into their generated group. Its first-vertex centralizer is O₂(YT), so
it supplies the reduced seed and centralizer equality required by F.7.

The canonical faithful graph action embeds equivariantly into the
original M-action. Thus it is non-FF; the original containment V ≤ O₂(H)
then makes its critical distance odd and at least three. The output
retains the same V, Sylow subgroup and minimizing critical vertex.

These are source inputs to marked recognition, not an enumeration of
the pair. The centered cubic endpoint differs from the Chapter 14 plane
setup. The required recognition and the original 15.2.8 conclusion remain
with qt-e-152-small-parabolic, using qt-e-quintic-recognition for the shared
engine where its literal hypotheses apply.

Source: Aschbacher--Smith, original 15.2.6--8, printed pp.1109--1110;
F.7.6--11, printed pp.312--314.
-/

public section
open Subgroup Representation Representation.BinaryOffender Stellmacher Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section02
open Section01 Section03 ChapterD ChapterD.UniqueFactor ChapterD.CyclicSource
variable {G : Type*} [Group G] [Finite G]

/-- The two original vertices have local degrees five and three, with
both inclusions of the whole edge subgroup mapping to the original T. -/
theorem ChosenSmallSource.marked_five_symmetricThree_graph_indices
    {T : Sylow 2 G} {M Mc V H : Subgroup G} (h : ChosenSmallSource T M Mc V)
    (hd : letI := h.prepared.elementary
      ∃ l : LocalGeneration ((imageRepresentation M V h.prepared.normalized).comp
        (Jhat (imageRepresentation M V h.prepared.normalized)).subtype),
        DihedralMarking l 5 2)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (he : Nonempty ((H ⧸ pCore 2 H) ≃* Equiv.Perm (Fin 3))) :
    let P := h.residual ⊔ (T : Subgroup G)
    let W := P ⊔ H
    let F : Bool → Subgroup W := fun i => if i then H.subgroupOf W else P.subgroupOf W
    ((F true).subgroupOf (F false)).index = 5 ∧
      ((F false).subgroupOf (F true)).index = 3 ∧
      (F false ⊓ F true).map W.subtype = (T : Subgroup G) := by
  let P := h.residual ⊔ (T : Subgroup G)
  let W := P ⊔ H
  let F : Bool → Subgroup W := fun i => if i then H.subgroupOf W else P.subgroupOf W
  have hg := (h.smallResidualWitness_of_marked_five hd).1.symmetricThree_geometry hH he
  have hPH : P ⊓ H = (T : Subgroup G) := hg.2.2.2.2.1
  have hfive : (T : Subgroup G).relIndex P = 5 := (h.marked_five_first_parabolic hd).1
  have hthree : (T : Subgroup G).relIndex H = 3 :=
    SymmetricThreeTwoCore.sylow_index_three he.some (T.subtype hH.1.1.2)
  have hmap : (F false ⊓ F true).map W.subtype = (T : Subgroup G) := by
    rw [map_inf _ _ _ W.subtype_injective]
    change (P.subgroupOf W).map W.subtype ⊓ (H.subgroupOf W).map W.subtype = _
    rw [map_subgroupOf_eq_of_le le_sup_left,map_subgroupOf_eq_of_le le_sup_right,hPH]
  refine ⟨?_,?_,hmap⟩
  · change (H.subgroupOf W).relIndex (P.subgroupOf W) = 5
    rw [relIndex_subgroupOf (show P ≤ W from le_sup_left),←inf_relIndex_left P H,hPH]
    exact hfive
  · change (P.subgroupOf W).relIndex (H.subgroupOf W) = 3
    rw [relIndex_subgroupOf (show H ≤ W from le_sup_right),←inf_relIndex_right P H,hPH]
    exact hthree
end CFSG.Quasithin.Chapter15.Section02

public noncomputable section
open Subgroup Representation Representation.BinaryOffender Stellmacher Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section02
open Section01 Section03 ChapterD ChapterD.UniqueFactor ChapterD.CyclicSource
open ChapterF.Section07.Track ChapterF.Section07.CriticalPairs Subgroup.CosetGeometry.RankTwo
variable {G : Type*} [Group G] [Finite G]

/-- The literal marked-five pair supplies F.7's reduced seed, centralizer,
common Sylow and positive critical track. The seed maps to the chosen V. -/
theorem ChosenSmallSource.marked_five_symmetricThree_source_track
    {T : Sylow 2 G} {M Mc V H : Subgroup G} (h : ChosenSmallSource T M Mc V)
    (hd : letI := h.prepared.elementary
      ∃ l : LocalGeneration ((imageRepresentation M V h.prepared.normalized).comp
        (Jhat (imageRepresentation M V h.prepared.normalized)).subtype),
        DihedralMarking l 5 2)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (he : Nonempty ((H ⧸ pCore 2 H) ≃* Equiv.Perm (Fin 3))) :
    let P := h.residual ⊔ (T : Subgroup G)
    let W := P ⊔ H
    let F : Bool → Subgroup W := fun i => if i then H.subgroupOf W else P.subgroupOf W
    ∃ D : SourceSetup F, ∃ hn : D.V ≠ ⊥,
      D.seed.map W.subtype = V ∧
      (D.sylow false : Subgroup (F false)).map
        (W.subtype.comp (F false).subtype) = (T : Subgroup G) ∧
      D.seed ≤ (F true).pCoreIn 2 ∧
      ¬ SourceAction.IsFF D ∧ Odd (D.track hn) ∧ 3 ≤ D.track hn ∧
      (∃ v : Vertex F, (graph F).dist (base F false) v = D.track hn ∧
        ¬ D.seed ≤ ballKernel F v 1) ∧
      (∀ v : Vertex F, ¬ D.seed ≤ ballKernel F v 1 →
        D.track hn ≤ (graph F).dist (base F false) v) := by
  let := h.prepared.elementary
  let P := h.residual ⊔ (T : Subgroup G)
  let W := P ⊔ H
  let A := P.subgroupOf W
  let B := H.subgroupOf W
  let F : Bool → Subgroup W := fun i => if i then B else A
  obtain ⟨hi,hfit,hVP,hspan,hr,hc,hquot⟩ := h.marked_five_first_parabolic hd
  have hw := (h.smallResidualWitness_of_marked_five hd).1
  have hg := hw.symmetricThree_geometry hH he
  have hcore : pCore 2 W = ⊥ := hg.2.2.2.2.2
  have hTP : (T : Subgroup G) ≤ P := le_sup_right
  have hTH : (T : Subgroup G) ≤ H := hH.1.1.2
  have hTW : (T : Subgroup G) ≤ W := hTP.trans le_sup_left
  let S := T.subtype hTW
  have hSA : (S : Subgroup W) ≤ A := fun x hx => hTP hx
  have hSB : (S : Subgroup W) ≤ B := fun x hx => hTH hx
  let syl : ∀ i, Sylow 2 (F i) := fun i => S.subtype (by
    cases i
    · exact hSA
    · exact hSB)
  let e : A ≃* P := subgroupOfEquivOfLe (show P ≤ W from le_sup_left)
  let U := (V.subgroupOf P).map e.symm.toMonoidHom
  have hred : IsPReduced 2 U := hr.map_equiv e.symm
  have hC : centralizer (U : Set A) = pCore 2 A := by
    have hh := map_centralizer_equiv (V.subgroupOf P : Set P) e.symm
    have hh' : (centralizer (V.subgroupOf P : Set P)).map e.symm.toMonoidHom =
        centralizer (U : Set A) := by
      simpa only [U,coe_map,←MulEquiv.toMonoidHom_eq_coe,MulEquiv.coe_toMonoidHom] using hh
    rw [←hh',hc,pCore_map_iso]
  have hfitA : generalizedFitting A = pCore 2 A := by
    apply map_injective (f := e.toMonoidHom) e.injective
    rw [map_generalizedFitting_equiv,pCore_map_iso,hfit]
  have hgen : F false ⊔ F true = ⊤ := by
    change P.subgroupOf W ⊔ H.subgroupOf W = ⊤
    rw [←subgroupOf_sup (show P ≤ W from le_sup_left) (show H ≤ W from le_sup_right)]
    exact subgroupOf_self W
  let D : SourceSetup F := {
    finite := fun _ => inferInstance
    generates := hgen
    characteristicTwo := hfitA
    core_free := by
      let d : (F false ⊔ F true : Subgroup W) ≃* W :=
        (MulEquiv.subgroupCongr hgen).trans topEquiv
      apply (map_eq_bot_iff_of_injective _ (f := d.toMonoidHom) d.injective).mp
      rw [pCore_map_iso]
      exact hcore
    sylow := syl
    same_sylow := (map_subgroupOf_eq_of_le hSA).trans
      (map_subgroupOf_eq_of_le hSB).symm
    V := U
    reduced := hred
    centralizer_eq := by
      rw [AmalgamLocalCores.reduced_centralizer_core U hred,hC]
      exact inf_eq_right.mpr (pCore_isPGroup.le_sylow_of_normal (syl false)) }
  have hn : D.V ≠ ⊥ := by
    intro hb
    have hu := (map_eq_bot_iff_of_injective (V.subgroupOf P) e.symm.injective).mp hb
    have hm := congrArg (map P.subtype) hu
    rw [map_subgroupOf_eq_of_le hVP,Subgroup.map_bot] at hm
    exact h.prepared.nontrivial hm
  have hseed : D.seed.map W.subtype = V := by
    change (((V.subgroupOf P).map e.symm.toMonoidHom).map A.subtype).map W.subtype = V
    rw [map_map,map_map]
    have hf : (W.subtype.comp A.subtype).comp e.symm.toMonoidHom = P.subtype := by
      ext x
      rfl
    rw [hf,map_subgroupOf_eq_of_le hVP]
  have hAM : (F false).map W.subtype ≤ M := by
    change A.map W.subtype ≤ M
    rw [map_subgroupOf_eq_of_le (show P ≤ W from le_sup_left)]
    exact sup_le (source_caseIIResidual_le T h.maximal.1.2 (map_subtype_le _)) h.maximal.1.2
  have htrue : D.seed ≤ (F true).pCoreIn 2 := by
    apply (map_le_map_iff_of_injective W.subtype_injective).mp
    rw [hseed,←AmalgamLocalCores.pCoreIn_map_of_injective 2 W.subtype W.subtype_injective,
      show (F true).map W.subtype = H from
        map_subgroupOf_eq_of_le (show H ≤ W from le_sup_right)]
    exact h.prepared.inside_core H hH
  have hnf := ChosenOppositeTrack.not_ff_of_ambient_image D W.subtype W.subtype_injective
    M V h.prepared.normalized hAM hseed h.not_ff
  have hodd := Completion.odd_track_of_not_ff F D hn hnf
  have hsmall := Completion.one_lt_track_of_true_core F D hn htrue
  have hthree : 3 ≤ D.track hn := by
    have hh : 1 < D.track hn := hsmall
    obtain ⟨k,hk⟩ := hodd
    omega
  refine ⟨D,hn,hseed,?_,htrue,hnf,hodd,hthree,(D.critical_witness hn).1,
    (D.critical_witness hn).2⟩
  · rw [←map_map]
    change (((S.subtype hSA : Sylow 2 A) : Subgroup A).map A.subtype).map W.subtype = _
    rw [Sylow.coe_subtype,map_subgroupOf_eq_of_le hSA]
    change ((T.subtype hTW : Sylow 2 W) : Subgroup W).map W.subtype = _
    rw [Sylow.coe_subtype,map_subgroupOf_eq_of_le hTW]
end CFSG.Quasithin.Chapter15.Section02