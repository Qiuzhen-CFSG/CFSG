module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearFourFive.NaturalDualParabolic.Realization.DistanceFourExclusion
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCenter.DistanceEightSmallDisplacement
public import Theory.Representation.BinaryNaturalDual.VectorStabilizers.Pure.Fixed
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearThree.Core

/-!
# Excluding the actual natural-dual residual at large distance

The original natural four-space lies in the residual commutator core K,
and its commutators with K lie in the marked point line. That line is
canonically the fixed subgroup of the residual on U_L. Normalization of
L and of its conjugate span therefore makes the line normal in the
original residual overgroup; its order two makes it central there.

The MS93 large-core small-displacement theorem then puts the entire
natural four-space in Z(K), contradicting its intersection with Z(K),
which is precisely the point line. The fixed supplement of W_L is kept:
all calculations take place in U_L = [W_L,L], never in an assumed whole
four-dimensional core or a quotient by an unproved central layer.

The final consumer uses the literal BinaryMS input. It retains only the
earlier large-distance source layers, with no original two-core action
premise on the replacement's fixed four-group.

Source: Aschbacher–Smith 15.3.24, printed pp.1129–1130; the large-core
small-displacement argument in MS93, (4.5.4), printed pp.898–899.
-/

public section
open Subgroup BinaryLinear.OuterCyclic
open scoped commutatorElement
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearFourFive.NaturalDualParabolic.Realization
open ChiefLayers ChapterC BinaryMS.MS93
variable {G : Type*} [Group G] [Finite G] {d : LocalData G} {L : Subgroup G}

/-- The original moved module has precisely the marked point line fixed by the residual. -/
theorem residual_fixed_eq_line (h : NaturalDual d L) {x : Space 4} (hx : x ≠ 0) :
    spanCommutator d L ⊓ centralizer
      (Stellmacher.twoResidualAmbient (point h x) : Set G) = lineSubgroup h x := by
  apply le_antisymm
  · intro u hu
    let v := h.coordinates ⟨u,hu.1⟩
    have hv : embed h v = u := by
      change (h.coordinates.symm (h.coordinates ⟨u,hu.1⟩) : G) = u
      rw [h.coordinates.symm_apply_apply]
    have hfix : ∀ g : BinaryNaturalDual.VectorStabilizers.Pure.pointStabilizer x,
        BinaryLinear.NaturalDualFlag.action g.val v.toAdd = v.toAdd := by
      intro g
      have hg : g ∈ (pResidual 2 (point h x)).map (pointActor h x) := by
        rw [pointActor_residual_image h hx]
        exact mem_top _
      obtain ⟨p,hp,hpg⟩ := hg
      have hpD : (p:G) ∈ Stellmacher.twoResidualAmbient (point h x) := by
        rw [ComponentIntersection.twoResidualAmbient_eq_map_pResidual]
        exact mem_map.mpr ⟨p,hp,rfl⟩
      have hc := embed_conj h (⟨p,point_le h x p.property⟩ : L) v.toAdd
      have he := hu.2 p hpD
      rw [ofAdd_toAdd,hv,he,mul_inv_cancel_right] at hc
      have hactor : linearAction (by decide) h.model ⟨p,point_le h x p.property⟩ = g.val :=
        congrArg Subtype.val hpg
      rw [hactor,←hv] at hc
      exact (congrArg Multiplicative.toAdd (embed_injective h hc)).symm
    have hcoord := (BinaryNaturalDual.VectorStabilizers.Pure.point_fixed_iff
      (by simp [Space]) hx v.toAdd).mp hfix
    rw [←hv]
    exact (embed_mem_coordinateSubgroup h (lineSpace x) v.toAdd).mpr hcoord
  · intro u hu
    obtain ⟨v,hv,rfl⟩ := hu
    refine ⟨embed_mem h v.toAdd,?_⟩
    intro p hp
    have hpP : p ∈ point h x := (map_subtype_le _) hp
    let pP : point h x := ⟨p,hpP⟩
    have hf := (BinaryNaturalDual.VectorStabilizers.Pure.point_fixed_iff
      (by simp [Space]) hx v.toAdd).mpr hv (pointActor h x pP)
    have hc := embed_conj h (⟨p,point_le h x hpP⟩ : L) v.toAdd
    change BinaryLinear.NaturalDualFlag.action
      (linearAction (by decide) h.model ⟨p,point_le h x hpP⟩) v.toAdd = v.toAdd at hf
    rw [hf,ofAdd_toAdd] at hc
    exact mul_inv_eq_iff_eq_mul.mp hc

/-- The canonical line is invariant under the original residual overgroup. -/
theorem binaryInput_line_normalized {κ : GroupClass}
    (h : NaturalDual d L) {x : Space 4} (hx : x ≠ 0)
    (hnL : d.S ≤ normalizer (L : Set G))
    (input : ChapterC.BinaryMS.Input κ (residualComponent h x) (sylowPart h x)) :
    residualOvergroup h x ≤ normalizer (lineSubgroup h x : Set G) := by
  let J := residualOvergroup h x
  let D := Stellmacher.twoResidualAmbient (point h x)
  have hDL : D ≤ L := (map_subtype_le _).trans (point_le h x)
  have hJL : J ≤ L ⊔ d.S := sup_le_sup hDL le_rfl
  have hJU : J ≤ normalizer (spanCommutator d L : Set G) := by
    intro j hj
    apply mem_normalizer_iff_map_conj_eq.mpr
    rw [spanCommutator,map_commutator,
      mem_normalizer_iff_map_conj_eq.mp
        (LinearThree.component_sylow_normalizes_span d L hnL (hJL hj)),
      mem_normalizer_iff_map_conj_eq.mp ((sup_le L.le_normalizer hnL) (hJL hj))]
  have hJD : J ≤ normalizer (D : Set G) := by
    apply (normal_subgroupOf_iff_le_normalizer (show D ≤ J from le_sup_left)).mp
    exact input.component_normal
  rw [←residual_fixed_eq_line h hx]
  exact (le_inf hJU (hJD.trans (normalizer_le_normalizer_centralizer D))).trans
    inf_normalizer_le_normalizer_inf

/-- The original natural summand has displacement of order at most two. -/
theorem natural_core_displacement (h : NaturalDual d L) {x : Space 4} (hx : x ≠ 0) :
    ⁅naturalSubgroup h,residualCore h x⁆ ≤ lineSubgroup h x := by
  rw [commutator_comm]
  apply commutator_le.mpr
  intro q hq a ha
  let qP : point h x := ⟨q,residualCore_le_point h hx hq⟩
  let aN : naturalSubgroup h := ⟨a,ha⟩
  have hqC : qP ∈ pCore 2 (point h x) := by
    have hh := residualCore_le_pointCore h hx hq
    obtain ⟨z,hz,hzq⟩ := hh
    exact (Subtype.ext hzq : z = qP) ▸ hz
  have hqA : quotientActor h x qP = 1 := by
    apply MonoidHom.mem_ker.mp
    rw [quotientActor_ker]
    exact hqC
  have hp := naturalProjection_conj h x qP aN
  rw [hqA] at hp
  have he : naturalProjection h x (conjugate _ _ (naturalSubgroup_normalized h x) qP aN * aN⁻¹) = 1 := by
    rw [map_mul,map_inv]
    have he' := congrArg Multiplicative.ofAdd hp
    change naturalProjection h x (conjugate _ _ (naturalSubgroup_normalized h x) qP aN) =
      naturalProjection h x aN at he'
    rw [he',mul_inv_cancel]
  have hker : conjugate _ _ (naturalSubgroup_normalized h x) qP aN * aN⁻¹ ∈
      (lineSubgroup h x).subgroupOf (naturalSubgroup h) := by
    rw [←naturalProjection_ker]
    exact he
  exact hker


private theorem binaryInput_false_of_large_and_line_normalized
    {κ : GroupClass} (h : NaturalDual d L) {x : Space 4} (hx : x ≠ 0)
    (hU : spanCommutator d L ≤ (point h x).pCoreIn 2)
    (input : ChapterC.BinaryMS.Input κ (residualComponent h x) (sylowPart h x))
    (t : InputSetup input)
    (common : CommonFacts t.reduction.radical t.source t.geometry)
    (earlier : DistanceEight.CoreFactors.Earlier t.reduction.radical t.geometry)
    (hn : residualOvergroup h x ≤ normalizer (lineSubgroup h x : Set G)) : False := by
  let J := residualOvergroup h x
  let Q := ChapterC.BinaryMS.commutatorCore (residualComponent h x)
  let A := naturalSubgroup h
  let N := lineSubgroup h x
  have hQmap : Q.map J.subtype = residualCore h x := mapped_commutatorCore h x input
  have hQJ : residualCore h x ≤ J := hQmap ▸ map_subtype_le _
  have hAJ : A ≤ J := (naturalSubgroup_le_residualCore h hx hU).trans hQJ
  have hNJ : N ≤ J := (lineSubgroup_le_natural h x).trans hAJ
  have hQ : (residualCore h x).subgroupOf J = Q := by
    rw [←hQmap]
    exact comap_map_eq_self_of_injective J.subtype_injective _
  have hA0 : A.subgroupOf J ≤ Q := by
    rw [←hQ]
    exact comap_mono (naturalSubgroup_le_residualCore h hx hU)
  have hN0 : N.subgroupOf J ≤ Q :=
    (comap_mono (lineSubgroup_le_natural h x)).trans hA0
  have hcentral : N.subgroupOf J ≤ center J := by
    intro a ha
    apply mem_center_iff.mpr
    intro b
    apply Subtype.ext
    exact (normalizer_le_centralizer_of_card_two N (lineSubgroup_card h hx) (hn b.property)
      (a:G) ha).symm
  have hcard : Nat.card (N.subgroupOf J) ≤ 2 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hNJ).toEquiv,lineSubgroup_card h hx]
  have hdisp : ⁅A.subgroupOf J,Q⁆ ≤ N.subgroupOf J := by
    intro q hq
    have hh := mem_map_of_mem J.subtype hq
    rw [map_commutator,map_subgroupOf_eq_of_le hAJ,hQmap] at hh
    exact natural_core_displacement h hx hh
  have hc := t.large_core_small_displacement common earlier hA0 hN0 hcentral hcard hdisp
  have hAc : A ≤ centralizer (residualCore h x : Set G) := by
    intro a ha q hq
    have hq0 : (⟨q,hQJ hq⟩ : J) ∈ Q := by rw [←hQ]; exact hq
    exact congrArg Subtype.val (hc (show (⟨a,hAJ ha⟩ : J) ∈ A.subgroupOf J from ha)
      ⟨q,hQJ hq⟩ hq0)
  have hAZ : A ≤ (center (residualCore h x)).map (residualCore h x).subtype := by
    intro a ha
    refine ⟨⟨a,naturalSubgroup_le_residualCore h hx hU ha⟩,?_,rfl⟩
    apply mem_center_iff.mpr
    intro q
    exact Subtype.ext (hAc ha q q.property)
  have hAN : A ≤ N := by
    change A ≤ lineSubgroup h x
    rw [←residualCore_center_inf_natural h hx hU]
    exact le_inf hAZ le_rfl
  have hc := card_le_of_le hAN
  rw [naturalSubgroup_card h,lineSubgroup_card h hx] at hc
  omega

/-- Actual source24 application: the residual is impossible from the earlier large-core layers. -/
theorem binaryInput_false_of_large {κ : GroupClass}
    (h : NaturalDual d L) {x : Space 4} (hx : x ≠ 0)
    (hU : spanCommutator d L ≤ (point h x).pCoreIn 2)
    (hnL : d.S ≤ normalizer (L : Set G))
    (input : ChapterC.BinaryMS.Input κ (residualComponent h x) (sylowPart h x))
    (t : InputSetup input)
    (common : CommonFacts t.reduction.radical t.source t.geometry)
    (earlier : DistanceEight.CoreFactors.Earlier t.reduction.radical t.geometry) : False :=
  binaryInput_false_of_large_and_line_normalized h hx hU input t common earlier
    (binaryInput_line_normalized h hx hnL input)

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearFourFive.NaturalDualParabolic.Realization
