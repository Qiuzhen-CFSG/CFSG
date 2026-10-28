module
public import CFSG.Quasithin.ChapterE.Section02.Structure.Components
public import Theory.GroupTheory.GeneralizedFitting.ComponentLayerStructure
public import Theory.GroupTheory.PResidual.NormalSubgroup
public import Theory.GroupTheory.Commutator.PerfectLocalReduction

/-!
# The normal core and component layer in E.2.2

The prescribed Sylow and the actual generating component make the layer quotient
a two-group. The odd normal core therefore lies in the layer and centralizes it;
conversely the layer center lies in the solvable radical, which equals the core.
Perfectness identifies this layer with the two-residual. For a normal generating
component this gives the literal source identity J = Z(K).

Source: Aschbacher–Smith E.2.2, printed pp.215–216.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterE.Structure
variable {H : Type*} [Group H] [Finite H]

theorem core_odd_of_twoCore_eq_bot (T : Sylow 2 H)
    (hP : ChapterB.IsMinimalParabolicOver T ⊤) (hO : pCore 2 H = ⊥) :
    Odd (Nat.card (ChapterB.minimalParabolicCore T hP)) := by
  let q := QuotientGroup.mk' (pCore 2 H)
  have hq : Function.Injective q := (MonoidHom.ker_eq_bot_iff q).mp (by
    rw [QuotientGroup.ker_mk',hO])
  have hh := ChapterB.minimalParabolic_coreImage_odd T hP
  have he : Nat.card (ChapterB.minimalParabolicCoreImage T hP) = Nat.card (ChapterB.minimalParabolicCore T hP) :=
    Nat.card_congr (Subgroup.equivMapOfInjective (ChapterB.minimalParabolicCore T hP) q hq).toEquiv.symm
  rw [← he]
  exact hh

theorem core_eq_layer_center (T : Sylow 2 H)
    (hP : ChapterB.IsMinimalParabolicOver T ⊤) (hs : ¬ Group.IsSolvable H)
    (hO : pCore 2 H = ⊥) {K : Subgroup H} (hK : IsComponent H K)
    (hgen : K ⊔ (T : Subgroup H) = ⊤) :
    ChapterB.minimalParabolicCore T hP =
      (center (componentLayer H)).map (componentLayer H).subtype := by
  let J := ChapterB.minimalParabolicCore T hP
  let E := componentLayer H
  have hET : E ⊔ (T : Subgroup H) = ⊤ := top_unique (by
    rw [← hgen]; exact sup_le_sup (le_sSup hK) le_rfl)
  have hp := isPGroup_quotient_of_sup_eq_top E (T : Subgroup H) T.isPGroup' hET
  have hJE : J ≤ E := by
    let q := QuotientGroup.mk' E
    have ho : Odd (Nat.card (J.map q)) :=
      (core_odd_of_twoCore_eq_bot T hP hO).of_dvd_nat (card_map_dvd J q)
    have he : J.map q = ⊥ := by
      rcases (hp.to_subgroup (J.map q)).card_eq_or_dvd with he | he
      · exact Subgroup.card_eq_one.mp he
      · exact (ho.not_two_dvd_nat he).elim
    simpa only [Subgroup.map_eq_bot_iff, q, QuotientGroup.ker_mk'] using he
  have hCJ : E ≤ centralizer (J : Set H) := by
    apply sSup_le
    intro L hL
    rcases hL.normal_dichotomy J with hl | hc
    · let := hL.2
      let : IsSimpleGroup (L ⧸ center L) := IsQuasisimple.simple
      let : Nontrivial L := (QuotientGroup.mk'_surjective (center L)).nontrivial
      let : Group.IsSolvable J := ChapterB.minimalParabolic_core_solvable T hP
      exact (Group.IsPerfect.not_isSolvable L
        (Group.isSolvable_of_isSolvable_injective (inclusion_injective hl))).elim
    · exact commutator_eq_bot_iff_le_centralizer.mp hc
  apply le_antisymm
  · intro x hx
    refine ⟨⟨x,hJE hx⟩,mem_center_iff.mpr (fun e => ?_),rfl⟩
    exact Subtype.ext ((le_centralizer_iff.mp hCJ hx) e e.property)
  · let Z := (center E).map E.subtype
    let : Z.Normal := ConjAct.normal_of_characteristic_of_normal
    let : CommGroup (center E) := IsMulCommutative.instCommGroup
    have hsolv : Group.IsSolvable Z := Group.isSolvable_of_surjective
      ((E.subtype).subgroupMap_surjective (center E))
    rw [ChapterB.minimalParabolic_nonsolvable_core_eq_radical T hP hs]
    exact le_solvableRadical Z inferInstance hsolv

theorem residual_eq_layer (T : Sylow 2 H)
    {K : Subgroup H} (hK : IsComponent H K)
    (hgen : K ⊔ (T : Subgroup H) = ⊤) :
    pResidual 2 H = componentLayer H := by
  let E := componentLayer H
  let : Group.IsPerfect E := componentLayer_isPerfect
  have hET : E ⊔ (T : Subgroup H) = ⊤ := top_unique (by
    rw [← hgen]; exact sup_le_sup (le_sSup hK) le_rfl)
  apply le_antisymm
  · exact sInf_le ⟨inferInstance,
      isPGroup_quotient_of_sup_eq_top E (T : Subgroup H) T.isPGroup' hET⟩
  · let : Group.IsNilpotent (H ⧸ pResidual 2 H) := (isPGroup_quotient_pResidual 2).isNilpotent
    exact le_of_isPerfect_of_solvable_quotient E (pResidual 2 H)
/-- If the generating component is normal, it is the entire layer. -/
theorem layer_eq_normal_component (T : Sylow 2 H)
    {K : Subgroup H} (hK : IsComponent H K) [K.Normal]
    (hgen : K ⊔ (T : Subgroup H) = ⊤) : componentLayer H = K := by
  let : Group.IsPerfect (componentLayer H) := componentLayer_isPerfect
  let : Group.IsNilpotent (H ⧸ K) :=
    (isPGroup_quotient_of_sup_eq_top K (T : Subgroup H) T.isPGroup' hgen).isNilpotent
  exact le_antisymm (le_of_isPerfect_of_solvable_quotient (componentLayer H) K)
    (le_sSup hK)

/-- The literal normal-component central identity in E.2.2(2). -/
theorem core_eq_normal_component_center (T : Sylow 2 H)
    (hP : ChapterB.IsMinimalParabolicOver T ⊤) (hs : ¬ Group.IsSolvable H)
    (hO : pCore 2 H = ⊥) {K : Subgroup H} (hK : IsComponent H K) [K.Normal]
    (hgen : K ⊔ (T : Subgroup H) = ⊤) :
    ChapterB.minimalParabolicCore T hP = (center K).map K.subtype := by
  exact (core_eq_layer_center T hP hs hO hK hgen).trans
    (congrArg (fun U : Subgroup H => (center U).map U.subtype)
      (layer_eq_normal_component T hK hgen))

/-- The complete structural opening of E.2.2 before the source model list. -/
theorem source_component_reduction {κ : GroupClass}
    (hH : IsSQTK κ H) (T : Sylow 2 H)
    (hP : ChapterB.IsMinimalParabolicOver T ⊤) (hs : ¬ Group.IsSolvable H)
    (hO : pCore 2 H = ⊥) :
    ∃ K : Subgroup H, IsComponent H K ∧ K.IsCComponent ∧
      K ⊔ (T : Subgroup H) = ⊤ ∧
      pResidual 2 H = componentLayer H ∧
      ChapterB.minimalParabolicCore T hP =
        (center (componentLayer H)).map (componentLayer H).subtype ∧
      (K.Normal → ChapterB.minimalParabolicCore T hP = (center K).map K.subtype) := by
  obtain ⟨K,hK,hC,hgen⟩ := exists_generating_quasisimple_component hH T hP hs hO
  exact ⟨K,hK,hC,hgen,residual_eq_layer T hK hgen,
    core_eq_layer_center T hP hs hO hK hgen,fun hn =>
      @core_eq_normal_component_center H _ _ T hP hs hO K hK hn hgen⟩
end CFSG.Quasithin.ChapterE.Structure
