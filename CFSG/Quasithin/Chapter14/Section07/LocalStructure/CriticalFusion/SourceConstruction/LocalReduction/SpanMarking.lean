module

public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceSetup
public import CFSG.Quasithin.Chapter12.Section08.Setup.NaturalActions
public import Theory.Representation.PSL3Two.SmallModules
public import Theory.GroupTheory.SylowNormalIntersection
public import Theory.SpecificGroups.PSL3Two.Parabolics.CompatibleMarking
public import Theory.SpecificGroups.PSL3Two.Parabolics.Actions
public import Theory.Representation.PSL3Two.AutomorphismAction.NaturalDual

/-!
# A compatible original SL₃(2) marking before local recognition

The given natural action marks L/O₂(L) as the actual binary matrix group.
Its coordinates identify H ∩ L with the stabilizer of the original point.
Sylow conjugacy and flag duality simultaneously send T ∩ L to the standard
Borel and H ∩ L to the line parabolic. The inverse marking twists the natural
module to its dual, fixing the orientation used in 14.7.22.

The marking proofs adapt the checked SourceEndgame parabolic-seed marking
using only the original HigherRankHypothesis and invariant flag, without Data.
Source: Aschbacher–Smith 12.8.1 and 14.7.22, printed pp.849,1050,
refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Representation
open scoped IsMulCommutative Pointwise
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.SpanMarking
open Chapter12.Section08 Matrix.PSL3Two
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
  {F : InvariantFlag T V 3}

noncomputable def qL : L →* BinaryLinearThree.Group := by
  let := h.chosen.elementary
  exact (BinaryLinear.OuterCyclic.slEquivLinear 3).symm.toMonoidHom.comp
    (h.naturalMarking.quotientEquiv.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L)))

theorem qL_surjective : Function.Surjective (qL h) := by
  let := h.chosen.elementary
  exact (BinaryLinear.OuterCyclic.slEquivLinear 3).symm.surjective.comp
    (h.naturalMarking.quotientEquiv.surjective.comp (QuotientGroup.mk'_surjective _))

theorem qL_ker : (qL h).ker = (L.pCoreIn 2).subgroupOf L := by
  let := h.chosen.elementary
  ext l
  change (BinaryLinear.OuterCyclic.slEquivLinear 3).symm
    (h.naturalMarking.quotientEquiv (QuotientGroup.mk' (pCore 2 L) l)) = 1 ↔ _
  rw [← (BinaryLinear.OuterCyclic.slEquivLinear 3).symm.map_one,
    (BinaryLinear.OuterCyclic.slEquivLinear 3).symm.injective.eq_iff,
    ← h.naturalMarking.quotientEquiv.map_one,
    h.naturalMarking.quotientEquiv.injective.eq_iff,
    QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  exact (mem_map_iff_mem L.subtype_injective).symm

/-- The original natural coordinates, without a containment assumption on V. -/
noncomputable def naturalCoordinates : V →* Multiplicative BinaryLinearThree.Vector := by
  let := h.chosen.elementary
  let c := h.naturalMarking.coordinates
  exact {
    toFun := fun v => Multiplicative.ofAdd (c (Additive.ofMul v))
    map_one' := c.map_zero
    map_mul' x y := c.map_add (Additive.ofMul x) (Additive.ofMul y) }

theorem naturalCoordinates_bijective : Function.Bijective (naturalCoordinates h) := by
  let := h.chosen.elementary
  exact h.naturalMarking.coordinates.bijective

theorem naturalCoordinates_equivariant (l : L) (v : V) :
    (naturalCoordinates h ⟨l * v * (l : G)⁻¹,
      (mem_normalizer_iff.mp (h.chosen.normalizes l.property) v).mp v.property⟩).toAdd =
      BinaryLinearThree.W (qL h l) (naturalCoordinates h v).toAdd := by
  let := h.chosen.elementary
  let c := h.naturalMarking.coordinates
  have hh := h.naturalMarking.equivariant l (Additive.ofMul v)
  change c _ = BinaryLinearThree.W (qL h l) (c (Additive.ofMul v))
  change c _ = _ at hh
  exact hh.trans (by
    change _ = ((qL h l).val.mulVec (c (Additive.ofMul v)))
    rw [← BinaryLinear.OuterCyclic.slEquivLinear_apply]
    simp only [qL, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply]
    rfl)

/-- The image of the original T ∩ L is a Sylow subgroup of the marked quotient. -/
theorem source_sylow_image (hTL : (T : Subgroup G) ≤ normalizer L) :
    ∃ P : Sylow 2 BinaryLinearThree.Group,
      ((qL h).comp (Subgroup.inclusion
        (inf_le_right : (T : Subgroup G) ⊓ L ≤ L))).range = (P : Subgroup _) := by
  let N := normalizer (L : Set G)
  let LN := L.subgroupOf N
  let : LN.Normal := normal_subgroupOf_of_le_normalizer le_rfl
  obtain ⟨S,hS⟩ := (T.subtype hTL).exists_subgroupOf_eq_of_normal LN
  let e : LN ≃* L := subgroupOfEquivOfLe L.le_normalizer
  let S' : Sylow 2 L := S.mapSurjective (f := e.toMonoidHom) e.surjective
  have hS' : (S' : Subgroup L) = (T : Subgroup G).subgroupOf L := by
    ext l
    constructor
    · rintro ⟨x,hx,rfl⟩
      rw [hS] at hx
      exact hx
    · intro hl
      refine ⟨e.symm l,?_,e.apply_symm_apply l⟩
      rw [hS]
      exact hl
  refine ⟨S'.mapSurjective (qL_surjective h), ?_⟩
  rw [Sylow.coe_mapSurjective, hS']
  ext g
  constructor
  · rintro ⟨x,hx⟩
    exact ⟨⟨x,x.property.2⟩,x.property.1,hx⟩
  · rintro ⟨l,hl,he⟩
    exact ⟨⟨l,hl,l.property⟩,he⟩
private theorem source_point_stabilizer (F : InvariantFlag T V 3) :
    ∃ p : Fano.Point, (F.H.subgroupOf L).map (qL h) = MulAction.stabilizer SL p := by
  obtain ⟨z,hz1,hz⟩ := SetupFlagGeometry.exists_point_generator F (by decide)
  have hcent := F.H_eq_centralizer (by decide) z hz
  have hzV : z ∈ V := F.le_seed 1 (by rw [hz]; exact mem_zpowers z)
  let zV : V := ⟨z, hzV⟩
  let v : BinaryLinearThree.Vector := (naturalCoordinates h zV).toAdd
  have hv : v ≠ 0 := by
    intro hh
    have he : naturalCoordinates h zV = naturalCoordinates h 1 := by
      rw [map_one]
      exact hh
    exact hz1 (congrArg Subtype.val ((naturalCoordinates_bijective h).1 he))
  let p : Fano.Point := ⟨v, hv⟩
  have hmem (l : L) : (qL h) l ∈ MulAction.stabilizer SL p ↔ l ∈ F.H.subgroupOf L := by
    change (qL h) l • p = p ↔ (l : G) ∈ F.H
    rw [hcent, mem_centralizer_singleton_iff]
    have he := naturalCoordinates_equivariant h l zV
    constructor
    · intro hh
      have hcoord :
          (naturalCoordinates h ⟨(l : G) * z * (l : G)⁻¹,
            (mem_normalizer_iff.mp (h.chosen.normalizes l.property) zV).mp zV.property⟩).toAdd =
            (naturalCoordinates h zV).toAdd :=
        he.trans (congrArg Subtype.val hh)
      have hz' :
          (⟨(l : G) * z * (l : G)⁻¹,
            (mem_normalizer_iff.mp (h.chosen.normalizes l.property) zV).mp zV.property⟩ : V) = zV :=
        (naturalCoordinates_bijective h).1 (Multiplicative.toAdd.injective hcoord)
      have hc : (l : G) * z * (l : G)⁻¹ = z := congrArg Subtype.val hz'
      exact mul_inv_eq_iff_eq_mul.mp hc
    · intro hh
      apply Subtype.ext
      change BinaryLinearThree.W ((qL h) l) v = v
      rw [← he]
      congr 2
      apply Subtype.ext
      exact mul_inv_eq_iff_eq_mul.mpr hh
  refine ⟨p, ?_⟩
  ext g
  obtain ⟨l, rfl⟩ := qL_surjective h g
  constructor
  · rintro ⟨k, hk, he⟩
    rw [← he]
    exact (hmem k).mpr hk
  · intro hh
    exact ⟨l, (hmem l).mp hh, rfl⟩

private theorem borel_fixed_point (p : Fano.Point)
    (h : ∀ g ∈ borelSL, g • p = p) : p = Matrix.PSL3Two.flagPoint := by
  have hc : ∀ p : Fano.Point,
      Bruhat.upper 1 • p = p → Bruhat.upper 4 • p = p → p = Matrix.PSL3Two.flagPoint := by
    decide +kernel
  exact hc p (h _ (Bruhat.upper_mem 1)) (h _ (Bruhat.upper_mem 4))

private theorem inner_sylow_marking (P : Sylow 2 SL) :
    ∃ g : SL, (P : Subgroup SL).map (MulAut.conj g).toMonoidHom = borelSL := by
  let B : Sylow 2 SL := Sylow.ofCard borelSL (by
    rw [card_borelSL, card_SL]
    decide +kernel)
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq SL P B
  refine ⟨g, ?_⟩
  have he := congrArg (fun Q : Sylow 2 SL => (Q : Subgroup SL)) hg
  rw [Sylow.coe_subgroup_smul] at he
  exact he

private theorem flag_duality_outer : flagDuality ∉ MulAut.innerSubgroup SL := by
  have he : BinaryLinear.OuterCyclic.graphSL 3 = BinaryLinearThree.AutomorphismAction.graph := by
    ext g : 1
    apply Subtype.ext
    exact (Matrix.adjugate_transpose g.val).symm
  have hf : flagDuality = MulAut.conj (Bruhat.perm 5) *
      BinaryLinearThree.AutomorphismAction.graph := by
    rw [← he]
    rfl
  rw [hf]
  intro h
  exact BinaryLinearThree.AutomorphismAction.graph_not_inner
    ((MulAut.innerSubgroup SL).mul_mem_cancel_left (show MulAut.conj (Bruhat.perm 5) ∈
      MulAut.innerSubgroup SL from ⟨_, rfl⟩) |>.mp h)


/-- A compatible matrix marking, constructed before the later source Data.
The natural action becomes dual under the same point/line switch. -/
theorem exists_marking (F : InvariantFlag T V 3)
    (hTL : (T : Subgroup G) ≤ normalizer L) :
    ∃ e : MulAut BinaryLinearThree.Group,
      ((T : Subgroup G).subgroupOf L).map (e.symm.toMonoidHom.comp (qL h)) = borelSL ∧
      (F.H.subgroupOf L).map (e.symm.toMonoidHom.comp (qL h)) = lineParabolicSL ∧
      Nonempty (Representation.Equiv (BinaryLinearThree.W.comp e.symm.toMonoidHom) BinaryLinearThree.W.dual) := by
  obtain ⟨p, hp⟩ := source_point_stabilizer h F
  obtain ⟨P, hP⟩ := source_sylow_image h hTL
  have hmap : ((T : Subgroup G).subgroupOf L).map (qL h) = (P : Subgroup SL) := by
    rw [← hP]
    ext g
    constructor
    · rintro ⟨l, hl, he⟩
      exact ⟨⟨l, hl, l.property⟩, he⟩
    · rintro ⟨l, he⟩
      exact ⟨⟨l, l.property.2⟩, l.property.1, he⟩
  have hPH : (P : Subgroup SL) ≤ MulAction.stabilizer SL p := by
    rw [← hp, ← hmap]
    exact map_mono (fun l hl => F.invariant 1 hl)
  obtain ⟨g, hg⟩ := inner_sylow_marking P
  have hp' : g • p = Matrix.PSL3Two.flagPoint := by
    apply borel_fixed_point
    intro a ha
    have ha' : a ∈ (MulAction.stabilizer SL p).map (MulAut.conj g).toMonoidHom :=
      map_mono hPH (hg.symm ▸ ha)
    rw [← MulAction.stabilizer_smul_eq_stabilizer_map_conj] at ha'
    exact ha'
  have hpar : ((F.H.subgroupOf L).map (qL h)).map (MulAut.conj g).toMonoidHom =
      pointParabolicSL := by
    rw [hp, ← MulAction.stabilizer_smul_eq_stabilizer_map_conj, hp', Fano.stabilizer_flagPoint_SL]
  let e : MulAut BinaryLinearThree.Group := (MulAut.conj g).trans flagDuality
  have he : e.symm ∉ MulAut.innerSubgroup BinaryLinearThree.Group := by
    intro h
    have hi : e ∈ MulAut.innerSubgroup SL := (MulAut.innerSubgroup SL).inv_mem h
    change flagDuality * MulAut.conj g ∈ MulAut.innerSubgroup SL at hi
    have hg' : MulAut.conj g ∈ MulAut.innerSubgroup SL := ⟨g, rfl⟩
    have hcancel : flagDuality * MulAut.conj g ∈ MulAut.innerSubgroup SL ↔
        flagDuality ∈ MulAut.innerSubgroup SL :=
      (MulAut.innerSubgroup SL).mul_mem_cancel_right hg'
    exact flag_duality_outer (hcancel.mp hi)
  have he_to : e.toMonoidHom =
      flagDuality.toMonoidHom.comp (MulAut.conj g).toMonoidHom := by rfl
  have hsylow : ((T : Subgroup G).subgroupOf L).map (e.toMonoidHom.comp (qL h)) =
      borelSL := by
    rw [he_to, ← map_map, ← map_map, hmap, hg, flagDuality_map_borel]
  have hline : (F.H.subgroupOf L).map (e.toMonoidHom.comp (qL h)) =
      lineParabolicSL := by
    rw [he_to, ← map_map, ← map_map, hpar, flagDuality_map_point]
  exact ⟨e.symm,by simpa only [MulEquiv.symm_symm] using hsylow,
    by simpa only [MulEquiv.symm_symm] using hline,
    ⟨BinaryLinearThree.AutomorphismAction.naturalOuterEquiv e
      (fun hi => he ((MulAut.innerSubgroup _).inv_mem hi))⟩⟩
end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.SpanMarking
