module
public import CFSG.Quasithin.ChapterB.Section06To07.Structure.CoreOdd.StarFactors
public import CFSG.Quasithin.ChapterB.Section06To07.Structure.CoreOdd.FactorNormalizers
public import CFSG.Quasithin.ChapterA.Section03.SQTKStructure.NoncentralFitting
public import Theory.GroupTheory.CComponent.QuasisimpleFactors
public import Theory.GroupTheory.CComponent.FittingCentralizer
public import Theory.GroupTheory.SolvableRadical.Transport
import all CFSG.Quasithin.ChapterB.Section06To07.Structure

/-!
# The actual component generating a nonsolvable minimal parabolic

Lift a simple factor of the original H/J residual through the solvable
normal core. Its C-component lift and the prescribed Sylow generate H:
otherwise both lie in the unique maximal overgroup, contradicting the
factor orbit's generation downstairs. When O₂(H)=1, the normal core is
nilpotent. Every component radical is then nilpotent; the genuine
noncentral A.3.6 branch would give radical index two over its Fitting
subgroup, an impossibility. Thus the lifted C-component is quasisimple.

Source: the opening reduction in Aschbacher–Smith E.2.2, printed pp.215–216.
The later list of simple models and their maximal subgroups is separate.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterE.Structure
universe u
variable {H : Type u} [Group H] [Finite H]

/-- The noncentral A.3.6 alternatives cannot have nilpotent radical. -/
theorem quasisimple_of_nilpotent_radical {κ : GroupClass.{u}}
    (hH : IsSQTK κ H) (hO : pCore 2 H = ⊥)
    (L : Subgroup H) (hL : L.IsCComponent)
    [Group.IsNilpotent (solvableRadical L)] : IsQuasisimple L := by
  have hr : solvableRadical L = fittingSubgroup L := le_antisymm
    (le_sSup ⟨inferInstance,inferInstance⟩) (le_solvableRadical _ inferInstance inferInstance)
  have hf : fittingSubgroup L ≤ center L := by
    by_contra hn
    have hc := (ChapterA.Section03.NoncentralFitting.structure_of_noncentral hH hO hL hn).2
    rcases hc.2.2.1 with hc | hc
    · have hh := hc.2.2
      rw [hr,relIndex_self] at hh
      omega
    · exact hn hc.1.le
  have hcenter : solvableRadical L = center L := le_antisymm
    (solvableRadical_le_center_of_fitting_le_center hf)
    (le_solvableRadical (center L) inferInstance
      (Group.isSolvable_of_comm (fun a b => Subtype.ext
        (mem_center_iff.mp a.property b).symm)))
  let := hL.perfect
  let := hL.isSimpleGroup_quotient_solvableRadical
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hcenter).symm.isSimpleGroup⟩

/-- The solvable radical of the original core-free minimal parabolic is nilpotent. -/
theorem radical_nilpotent_of_twoCore_eq_bot (T : Sylow 2 H)
    (hP : ChapterB.IsMinimalParabolicOver T ⊤) (hs : ¬ Group.IsSolvable H)
    (hO : pCore 2 H = ⊥) : Group.IsNilpotent (solvableRadical H) := by
  let J := ChapterB.minimalParabolicCore T hP
  let q := QuotientGroup.mk' (pCore 2 H)
  have hq : Function.Injective q := (MonoidHom.ker_eq_bot_iff q).mp (by
    rw [QuotientGroup.ker_mk',hO])
  let : Group.IsNilpotent (J.map q) := ChapterB.minimalParabolic_coreImage_nilpotent T hP
  have hJ : Group.IsNilpotent J := Group.nilpotent_of_mulEquiv (J.equivMapOfInjective q hq).symm
  rw [← ChapterB.minimalParabolic_nonsolvable_core_eq_radical T hP hs]
  exact hJ

/-- The prescribed Sylow and one actual C-component generate the whole group. -/
theorem exists_generating_cComponent (T : Sylow 2 H)
    (hP : ChapterB.IsMinimalParabolicOver T ⊤) (hs : ¬ Group.IsSolvable H) :
    ∃ K : Subgroup H, K.IsCComponent ∧ K ⊔ (T : Subgroup H) = ⊤ := by
  let J := ChapterB.minimalParabolicCore T hP
  let q := QuotientGroup.mk' J
  let : Group.IsSolvable J := ChapterB.minimalParabolic_core_solvable T hP
  obtain ⟨L,_,_,_,hL,ho⟩ := ChapterB.minimalParabolic_nonsolvable_star_factor T hP hs
  obtain ⟨K,hK,he⟩ := hL.isCComponent.exists_map_quotient_eq J
  refine ⟨K,hK,?_⟩
  by_contra hne
  have hM : K ⊔ (T : Subgroup H) ≤ ChapterB.minimalParabolicMax T hP :=
    hP.1.le_maximal ⟨(ChapterB.minimalParabolicMax_spec T hP).2,
      (ChapterB.minimalParabolicMax_spec T hP).1.covBy_top⟩ le_sup_right
      (lt_top_iff_ne_top.mpr hne)
  apply ChapterB.FactorNormalizers.factor_not_le_starMax T hP L ho
  rw [← he]
  exact map_mono (le_sup_left.trans hM)

/-- Opening E.2.2 in the literal O₂-free group, with no model or component premise. -/
theorem exists_generating_quasisimple_component {κ : GroupClass.{u}}
    (hH : IsSQTK κ H) (T : Sylow 2 H)
    (hP : ChapterB.IsMinimalParabolicOver T ⊤) (hs : ¬ Group.IsSolvable H)
    (hO : pCore 2 H = ⊥) :
    ∃ K : Subgroup H, IsComponent H K ∧ K.IsCComponent ∧
      K ⊔ (T : Subgroup H) = ⊤ := by
  obtain ⟨K,hK,hgen⟩ := exists_generating_cComponent T hP hs
  let : Group.IsNilpotent (solvableRadical H) := radical_nilpotent_of_twoCore_eq_bot T hP hs hO
  have hl := map_solvableRadical_subtype_le_of_isSubnormal hK.subnormal
  let j : solvableRadical K →* solvableRadical H :=
    (K.subtype.comp (solvableRadical K).subtype).codRestrict _
      (fun x => hl (mem_map_of_mem K.subtype x.property))
  have hj : Function.Injective j := by
    intro x y hxy
    have hh := congrArg (fun z : solvableRadical H => (z : H)) hxy
    exact Subtype.ext (Subtype.ext hh)
  let : Group.IsNilpotent (solvableRadical K) := Subgroup.isNilpotent_of_ker_le_center j
    (by rw [(MonoidHom.ker_eq_bot_iff j).mpr hj]; exact bot_le)
  exact ⟨K,⟨hK.subnormal,quasisimple_of_nilpotent_radical hH hO K hK⟩,hK,hgen⟩
end CFSG.Quasithin.ChapterE.Structure
