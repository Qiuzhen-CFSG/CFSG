module

public import CFSG.Quasithin.Chapter12.Section07.OriginalTripleSixCentralClosureInnerIntersections
public import CFSG.Quasithin.Chapter3.Section02.LocalCentralizer

/-!
# The original core intersection has at most one dimension above U

The genuine equality C_T(U)=O2(KT) identifies the kernel of the closure's
Klein-four action. The unchanged closure therefore intersects this core in
order four or eight. Its intersection with U is precisely the scalar point,
so its image modulo U has order at most two. Mutual normalization retains
the actual commutator inside that intersection.

Source: Aschbacher--Smith 12.7.16, printed p.844.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section07
open Section02 ChapterE ChapterB.QuasisimpleSource
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {K U : Subgroup G}

/-- The literal original O2(KT)-intersection supplies the index-two
bound for every subsequent chief section, without a block assumption. -/
theorem original_tripleSix_central_closure_inner_core_index
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T K)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (D : ChosenModule T K U) (a : ActionEquiv D.quotientAction Hexacode.evenAction)
    (z : U) (hz : z ≠ 1)
    (hzT : (T : Subgroup G) ≤ centralizer ({(z:G)} : Set G))
    (hnot : ¬ U ≤ (centralizer ({(z:G)} : Set G)).pCoreIn 2)
    (hinner : inducedAutomizer U (conjugateSpanBy (tripleSixPoint D a z)
      (conjugateSpanBy U (centralizer ({(z:G)} : Set G)))) ≤ inducedAutomizer U K) :
    let W := conjugateSpanBy (tripleSixPoint D a z)
      (conjugateSpanBy U (centralizer ({(z:G)} : Set G)))
    let Q := (K ⊔ (T : Subgroup G)).pCoreIn 2
    (Nat.card (Q ⊓ W : Subgroup G)=4 ∨ Nat.card (Q ⊓ W : Subgroup G)=8) ∧
      U.relIndex (Q ⊓ W)≤2 ∧ ⁅Q,W⁆≤Q ⊓ W := by
  let C := centralizer ({(z:G)} : Set G)
  let R := conjugateSpanBy U C
  let V1 := tripleSixPoint D a z
  let W := conjugateSpanBy V1 R
  let J := tripleSixWeightFourResidual K z
  let H := R ⊔ J ⊔ (T : Subgroup G)
  let Q := (K ⊔ (T : Subgroup G)).pCoreIn 2
  obtain ⟨_,hmeet,hfour,hcard⟩ := original_tripleSix_central_closure_inner_intersections
    h structural D a z hz hzT hnot hinner
  change U ⊓ W=V1 at hmeet
  change Nat.card (inducedAutomizer U W)=4 at hfour
  change Nat.card W=16 ∨ Nat.card W=32 at hcard
  have hp := tripleSixPoint_properties D a z hz
  have hTU := ((structural K h).2.2 U D).1
  have hu := Chapter1.Section02.nonsolvable_uniqueness_of_theoremsAC
    (fun X _ _ => ChapterA.Section02.theoremA_knownSimple (G:=X))
    (fun X _ _ => ChapterA.Section02.theoremC_knownSimple (G:=X))
    h.simpleQTKE T h.maximal_faithful.1
  have ho : componentOrbit U (T : Subgroup G)=U :=
    le_antisymm (iSup_conjugates_le_of_le_normalizer U T U le_rfl hTU) (le_componentOrbit U T)
  have hcQ : (T : Subgroup G) ⊓ centralizer (U : Set G)=Q := by
    have he := (D.fundamentalSetup h.toHypothesis1221).sylow_centralizer_module hu
    rw [D.fundamentalSetup_module,ho] at he
    simpa only [Chapter3.Section02.localJoin,D.localOrbit_eq] using he
  have hWT : W≤(T : Subgroup G) :=
    (original_tripleSix_central_closure_automizer h structural D a z hz hzT hnot).1
  have hWN : W≤normalizer (U : Set G) := hWT.trans hTU
  have hQI : Q ⊓ W=W ⊓ centralizer (U : Set G) := by
    rw [←hcQ]
    calc
      ((T : Subgroup G) ⊓ centralizer (U : Set G)) ⊓ W =
          ((T : Subgroup G) ⊓ W) ⊓ centralizer (U : Set G) := by ac_rfl
      _ = W ⊓ centralizer (U : Set G) := by rw [inf_of_le_right hWT]
  have hsize : Nat.card (inducedAutomizer U W)=(centralizer (U : Set G)).relIndex W := by
    rw [inducedAutomizer,←relIndex_ker,MonoidHom.ker_rangeRestrict,
      normalizerMonoidHom_ker,relIndex_subgroupOf hWN]
  have hi : (Q ⊓ W).relIndex W=4 := by
    rw [hQI,inf_comm,inf_relIndex_right,←hsize,hfour]
  have hm := relIndex_mul_relIndex (⊥ : Subgroup G) (Q ⊓ W) W bot_le inf_le_right
  rw [relIndex_bot_left,relIndex_bot_left,hi] at hm
  have hcardI : Nat.card (Q ⊓ W : Subgroup G)=4 ∨ Nat.card (Q ⊓ W : Subgroup G)=8 := by omega
  have hUQ : U≤Q := D.le_componentCore.trans (pCoreIn_mono_of_normalizes le_sup_left
    (sup_le K.le_normalizer D.sylow_normalizes_component))
  have hUI : U ⊓ (Q ⊓ W)=V1 := by
    calc
      U ⊓ (Q ⊓ W)=(U ⊓ Q) ⊓ W := by ac_rfl
      _ = V1 := by rw [inf_of_le_left hUQ,hmeet]
  have hratio := relIndex_mul_relIndex (⊥ : Subgroup G) (U ⊓ (Q ⊓ W)) (Q ⊓ W)
    bot_le inf_le_right
  rw [relIndex_bot_left,relIndex_bot_left,inf_relIndex_right,hUI,hp.2.2.1] at hratio
  have hc := original_tripleSix_central_closure_configuration h structural D a z hz hzT hnot
  have hWH : W=conjugateSpanBy V1 H := hc.2.1
  have hHW : H≤normalizer (W : Set G) := by
    rw [hWH]
    exact le_normalizer_conjugateSpanBy V1 H
  have hQW : Q≤normalizer (W : Set G) :=
    (show Q≤(T : Subgroup G) from hcQ.symm ▸ inf_le_left).trans
      (le_sup_right.trans hHW)
  have hWQ : W≤normalizer (Q : Set G) := (hWT.trans le_sup_right).trans
    ((K ⊔ (T : Subgroup G)).le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image _ (pCore 2 _)))
  have hindex : U.relIndex (Q ⊓ W)≤2 := by omega
  exact ⟨hcardI,hindex,le_inf (le_normalizer_iff_commutator_le_left.mp hWQ)
    (le_normalizer_iff_commutator_le_right.mp hQW)⟩

end CFSG.Quasithin.Chapter12.Section07
