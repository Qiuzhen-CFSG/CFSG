module
public import CFSG.Quasithin.ChapterE.Section02.Structure.OriginalNormal
public import CFSG.Quasithin.ChapterE.Section02.Structure.ComponentModels.OriginalImage
public import Theory.SpecificGroups.PSL3.OrdinaryCenterRecognition
/-!
# The original maximal core in the PSL₃(3) source row

The original component map descends through its two-core to a covering
of the marked simple PSL₃(3) image in H/J. Its kernel is the component
center. The proved ordinary scalar-cover bound makes that center have
order dividing gcd(3,3−1)=1. The source normal-component center identity
therefore makes J/O₂(H) trivial, giving J = O₂(H) in the original group.

This identifies the actual kernel used when pulling the affine order-nine
subgroup back from the component model. No odd-kernel splitting or separate
Schur-multiplier premise is required.

Source: Aschbacher–Smith E.2.2(2), E.2.17 and I.1.3(2), printed
pp.215–216,230 and407; the scalar-cover theorem is proved in the imported
ordinary-center recognition module.
-/

public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterE.Structure.LinearThree
variable {H : Type*} [Group H] [Finite H]
/-- The original normal PSL₃(3) source has no maximal-core kernel above O₂(H). -/
theorem source_ternary_core_eq_twoCore
    (T : Sylow 2 H) (hP : ChapterB.IsMinimalParabolicOver T ⊤)
    (hs : ¬ Group.IsSolvable H) (K : Subgroup H) (hK : K.IsCComponent) [K.Normal]
    (hqK : IsQuasisimple (K ⧸ pCore 2 K))
    (hgen : K ⊔ (T : Subgroup H) = ⊤)
    (hm : ClassicalGroup.IsPSL
      (K.map (QuotientGroup.mk' (ChapterB.minimalParabolicCore T hP))) 3 3) :
    ChapterB.minimalParabolicCore T hP = pCore 2 H := by
  let q := QuotientGroup.mk' (ChapterB.minimalParabolicCore T hP)
  have hk : pCore 2 K ≤ (q.subgroupMap K).ker := by
    intro x hx
    apply Subtype.ext
    exact (QuotientGroup.eq_one_iff (x : H)).mpr
      (ChapterB.minimalParabolicTwoCore_le_core T hP
        (pCoreIn_le_of_subnormal 2 hK.subnormal (mem_map_of_mem K.subtype hx)))
  let f := QuotientGroup.lift (pCore 2 K) (q.subgroupMap K) hk
  let := hqK
  have hi := source_component_simple_image T hP hs K hK hgen
  let : IsSimpleGroup (K.map q) := hi.1
  let : IsQuasisimple (K.map q) := hi.2.1.2
  let c : Covering (K ⧸ pCore 2 K) (K.map q) :=
    ⟨f,QuotientGroup.lift_surjective_of_surjective _ _ (q.subgroupMap_surjective K) _⟩
  have he := c.ker_eq_center_of_isSimple
  obtain ⟨F,hF,hfin,hcard,⟨e⟩⟩ := hm
  let eZ : ((K ⧸ pCore 2 K) ⧸ center (K ⧸ pCore 2 K)) ≃* PSL(3,F) :=
    (QuotientGroup.quotientMulEquivOfEq he.symm).trans
      ((QuotientGroup.quotientKerEquivOfSurjective c.toMonoidHom c.surjective).trans e)
  have hc := Matrix.PSL3.OrdinaryCenterRecognition.center_card_dvd
    (F:=F) (by omega) (by omega) eZ
  have hz : center (K ⧸ pCore 2 K) = ⊥ := by
    rw [hcard] at hc
    norm_num at hc
    exact hc
  have hza : center (K.map (QuotientGroup.mk' (pCore 2 H))) = ⊥ := by
    apply Subgroup.card_eq_one.mp
    rw [← Nat.card_congr (centerCongr (cComponentTwoCoreQuotientEquiv hK)).toEquiv,hz]
    simp
  have hcenter := (source_original_normal_clauses T hP hs K hK hqK hgen).2
  rw [hza,Subgroup.map_bot] at hcenter
  exact le_antisymm (by
    simpa only [Subgroup.map_eq_bot_iff,QuotientGroup.ker_mk'] using hcenter)
    (ChapterB.minimalParabolicTwoCore_le_core T hP)
end CFSG.Quasithin.ChapterE.Structure.LinearThree
