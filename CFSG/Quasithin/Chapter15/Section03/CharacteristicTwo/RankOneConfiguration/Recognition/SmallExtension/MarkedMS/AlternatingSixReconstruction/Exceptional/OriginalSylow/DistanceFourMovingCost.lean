module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.OriginalSylow.DistanceFourBaumann
/-!
# The opposite span on the full moving central quotient

The moving radius lies in the selected span joined with the starting seed.
That seed lies in Baumann, so the moving image modulo Baumann lies in the
selected-span image. Monotonicity transfers the opposed-span fixed index
bound to this image. Baumann intersects the moving radius in its intrinsic
center; hence the same index controls the literal moving central quotient.
The whole opposite span therefore has fixed codimension at most two.

Source: Meierfrankenfeld--Stellmacher (1993), (5.12)(2), printed p.926;
Aschbacher--Smith C.1.31--32, printed pp.135--136.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender BinaryPermutation
open Theory.SpecificGroups.SymmetricSix Theory.SpecificGroups.SymmetricSix.BinaryFlags
open CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.NaturalStructure.Exclusion
open scoped IsMulCommutative commutatorElement Pointwise
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Exceptional.OriginalSylow
open Exhaustion Exhaustion.LargeDistance Exhaustion.LargeDistance.CubicFull
universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  (h : SmallMSPair KnownSimple.IsKnownSimple L R) (e : CentralMarking L)
  (hz : Nat.card (center (L ⧸ pCore 2 L)) = 3)
  (hk : layerKernel L R = extensionKernel h)
local notation "Rg" => edge L R
local notation "π" => CubicAction.projection h e hz hk

include h e hz hk in
/-- The whole opposite span has fixed index at most four on the full moving
radius modulo the literal original Baumann subgroup. -/
theorem borel_four_opposed_span_moving_baumann_fixed_index
    (u : S) (hR : (Rg).map π = borel.map (MulAut.conj u).toMonoidHom)
    {z : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) (alpha Rg) z) :
    let a := alpha Rg
    let c := p.walk.getVert 2
    let W := (Vcirc Rg a).comap (embedM Rg)
    let A := (localZSpan Rg a c).comap (embedM Rg)
    let D := (B Rg a ((sourceGeometry h).Z_normal _)).comap (embedM Rg)
    let := baumann_preimage_normal h (distance_gt_two h e hz hk)
    (centralizerModulo W A D).relIndex W ≤ 4 := by
  let a := alpha Rg
  let c := p.walk.getVert 2
  let f := embedM Rg
  let W := (Vcirc Rg a).comap f
  let P := (localZSpan Rg c a).comap f
  let Z₀ := (Z Rg a).comap f
  let A := (localZSpan Rg a c).comap f
  let D := (B Rg a ((sourceGeometry h).Z_normal _)).comap f
  let := baumann_preimage_normal h (distance_gt_two h e hz hk)
  let q := QuotientGroup.mk' D
  have hb := distance_gt_two h e hz hk
  have hl : p.walk.length = 4 := p.length_eq_b.trans (borel_distance_eq_four h e hz hk u hR)
  have hWV : Vcirc Rg a ≤ V Rg a := le_normalizer_iff_commutator_le_left.mp
    ((Ltilde_le_stabilizer a).trans (V_normalized a))
  have hWm : W.map f = Vcirc Rg a :=
    map_comap_eq_self ((hWV.trans ((sourceGeometry h).V_local a rfl hb)).trans_eq
      (stabilizer_m_base Rg))
  have hPm : P.map f = localZSpan Rg c a :=
    map_comap_eq_self (((localZSpan_le_V Rg (by
      rw [SimpleGraph.dist_comm,p.dist_start (by omega)])).trans
      ((sourceGeometry h).V_local a rfl hb)).trans_eq (stabilizer_m_base Rg))
  have hZm : Z₀.map f = Z Rg a :=
    map_comap_eq_self ((Z_le_stabilizer Rg _).trans_eq (stabilizer_m_base Rg))
  have hWP : W ≤ P ⊔ Z₀ := by
    apply (map_le_map_iff_of_injective (embedM_injective Rg)).mp
    rw [Subgroup.map_sup,hWm,hPm,hZm]
    exact borel_four_moving_radius_le_span_seed h e hz hk u hR p
  have hZD : Z₀ ≤ D := by
    apply comap_mono
    intro x hx
    apply (mem_B_iff Rg a _ ((sourceGeometry h).V_local a rfl hb) x).mpr
    refine ⟨Z_le_VBall Rg a 2 hx,?_⟩
    intro l hl
    apply le_normalizer_iff_commutator_le_left.mp
      ((Ltilde_le_stabilizer a).trans (Z_normalized Rg a))
    rw [commutator_comm]
    exact commutator_mem_commutator hl hx
  have hZq : Z₀.map q = ⊥ := (Subgroup.map_eq_bot_iff _).mpr (by
    simpa only [q,QuotientGroup.ker_mk'] using hZD)
  have hWq : W.map q ≤ P.map q := by
    simpa only [Subgroup.map_sup,hZq,sup_bot_eq] using (map_mono (f := q) hWP)
  have hi := borel_four_opposed_span_baumann_fixed_index h e hz hk u hR p
  change (centralizerModulo P A D).relIndex P ≤ 4 at hi
  change (centralizerModulo W A D).relIndex W ≤ 4
  rw [NoncentralChiefRefinement.SymmetricSixBudget.centralizerModulo_relIndex_eq] at hi ⊢
  exact (relIndex_le_of_le_right hWq Subgroup.index_ne_zero_of_finite).trans hi

private theorem moving_fixedSpace_subgroup_index {G D : Type*} [Group G] [Group D]
    [IsElementaryAbelian 2 D] [Finite D] (action : G →* MulAut D) (A : Subgroup G) :
    (Subgroup.toAddSubgroup.symm
      (fixedSpace (Offenders.linearize action) A).toAddSubgroup).index =
      2 ^ fixedCodim (Offenders.linearize action) A := by
  let ρ := Offenders.linearize action
  let C := Subgroup.toAddSubgroup.symm (fixedSpace ρ A).toAddSubgroup
  let e : fixedSpace ρ A ≃ C := {
    toFun := fun v => ⟨v.val.toMul, v.property⟩
    invFun := fun x => ⟨Additive.ofMul x.val, x.property⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }
  have hC : Nat.card C = 2 ^ Module.finrank (ZMod 2) (fixedSpace ρ A) := by
    have hf := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := fixedSpace ρ A)
    rw [Nat.card_zmod] at hf
    exact (Nat.card_congr e).symm.trans hf
  have hT : Nat.card D = 2 ^ Module.finrank (ZMod 2) (Additive D) :=
    (Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive D)).trans (by rw [Nat.card_zmod])
  have hdim := fixedCodim_add_finrank ρ A
  have hmul := C.card_mul_index
  rw [hC, hT, ← hdim, pow_add, Nat.mul_comm (2 ^ fixedCodim ρ A)] at hmul
  exact Nat.eq_of_mul_eq_mul_left (by positivity) hmul

include h e hz hk in
/-- The whole opposite span moves at most two dimensions on the actual central
quotient of the full moving radius, with the original vertex action retained. -/
theorem borel_four_opposed_span_moving_fixed_codim_le_two
    (u : S) (hR : (Rg).map π = borel.map (MulAut.conj u).toMonoidHom)
    {z : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) (alpha Rg) z) :
    letI := moving_central_quotient_elementary (sourceGeometry h) (sourceDistance_pos h)
      (alpha Rg) rfl (borel_four_radius_derived_fixed_base h e hz hk u hR)
    fixedCodim (Offenders.linearize (movingQuotientAction (alpha Rg)))
      ((localZSpan Rg (alpha Rg) (p.walk.getVert 2)).subgroupOf
        (stabilizer Rg (alpha Rg))) ≤ 2 := by
  let a := alpha Rg
  let E := localZSpan Rg a (p.walk.getVert 2)
  let M := Vcirc Rg a
  let f := embedM Rg
  let W := M.comap f
  let A := E.comap f
  let D := (B Rg a ((sourceGeometry h).Z_normal _)).comap f
  let := baumann_preimage_normal h (distance_gt_two h e hz hk)
  let K := centralizerModulo W A D
  let K₁ := K.map f
  let := moving_central_quotient_elementary (sourceGeometry h) (sourceDistance_pos h)
    a rfl (borel_four_radius_derived_fixed_base h e hz hk u hR)
  let := finite_moving (sourceGeometry h) (distance_gt_two h e hz hk) a rfl
  let q := QuotientGroup.mk' (center M)
  let ρ := Offenders.linearize (movingQuotientAction a)
  let C := Subgroup.toAddSubgroup.symm
    (fixedSpace ρ (E.subgroupOf (stabilizer Rg a))).toAddSubgroup
  have hWV : M ≤ V Rg a := le_normalizer_iff_commutator_le_left.mp
    ((Ltilde_le_stabilizer a).trans (V_normalized a))
  have hWm : W.map f = M :=
    map_comap_eq_self ((hWV.trans ((sourceGeometry h).V_local a rfl
      (distance_gt_two h e hz hk))).trans_eq (stabilizer_m_base Rg))
  have hi : K₁.relIndex M ≤ 4 := by
    rw [←hWm,relIndex_map_map_of_injective _ _ (embedM_injective Rg)]
    exact borel_four_opposed_span_moving_baumann_fixed_index h e hz hk u hR p
  have hKC : K₁.subgroupOf M ≤ C.comap q := by
    intro v hv actor
    obtain ⟨x,hx,hxeq⟩ := hv
    have haG : (actor.val : FreeAmalgam Rg) ∈ stabilizer Rg a := actor.val.property
    obtain ⟨m,hm⟩ := (show stabilizer Rg a ≤ f.range from
      (stabilizer_m_base Rg).le) haG
    have hma : m ∈ A := by
      change f m ∈ E
      rw [hm]
      exact actor.property
    let d : M := movingAction a actor.val v * v⁻¹
    have hd : (d : FreeAmalgam Rg) ∈ B Rg a ((sourceGeometry h).Z_normal _) := by
      have hh := (mem_centralizerModulo_iff.mp hx).2 m hma
      change f ⁅m,x⁆ ∈ B Rg a ((sourceGeometry h).Z_normal _) at hh
      rw [map_commutatorElement,hm,hxeq] at hh
      exact hh
    have hdC : d ∈ center M := by
      rw [←borel_four_moving_baumann_eq_center h e hz hk u hR]
      exact hd
    change Additive.ofMul (movingQuotientAction a actor.val (q v)) = Additive.ofMul (q v)
    apply congrArg Additive.ofMul
    rw [movingQuotientAction_apply]
    apply QuotientGroup.eq_iff_div_mem.mpr
    simpa only [div_eq_mul_inv] using hdC
  have hindex : C.index ≤ K₁.relIndex M := by
    rw [←C.index_comap_of_surjective (QuotientGroup.mk'_surjective (center M))]
    exact Nat.le_of_dvd (Nat.pos_of_ne_zero (K₁.subgroupOf M).index_ne_zero_of_finite)
      (index_dvd_of_le hKC)
  rw [moving_fixedSpace_subgroup_index] at hindex
  exact (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp (hindex.trans hi)

end AlternatingSixReconstruction.Exceptional.OriginalSylow
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
