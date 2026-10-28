module

public import CFSG.Quasithin.ChapterI.Section04To05.HigmanSims.Construction.OverlapCores
public import CFSG.Quasithin.ChapterI.Section04To05.HigmanSims.Construction.PointCoreLifts
public import Theory.SpecificGroups.PSL3Two.Parabolics.NaturalPoint
public import Theory.SpecificGroups.PSL3Two.Parabolics.MarkedAutomorphisms.NaturalFlag.Model

/-!
# Actual transvection lifts from the original HS point core

The full seed action maps the original point-centralizer overlap onto the
point stabilizer. Its two-core is the join of the two local cores, and the
normalizer core is precisely the action kernel. Hence the point core maps
onto the point radical. The natural binary matrix action identifies the
involutions with a specified nonzero displacement inside this radical.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.HigmanSims
variable {G : Type*} [Group G] [Finite G] {z : G} {V : Subgroup G}

/-- The image of the original point core is exactly the radical of the
stabilizer of the marked point in the full seed automorphism group. -/
theorem TypeAt.point_core_action_image (h : TypeAt z V) :
    let I := involutionCentralizer z ⊓ normalizer (V : Set G)
    let Q := (involutionCentralizer z).pCoreIn 2
    let f := V.normalizerMonoidHom.comp (inclusion (show I ≤ normalizer (V : Set G) from inf_le_right))
    (Q.subgroupOf I).map f =
      (MulAction.stabilizer (MulAut V) (⟨z, h.involution_mem_seed⟩ : V)).pCoreIn 2 := by
  let H := involutionCentralizer z
  let M := normalizer (V : Set G)
  let I := H ⊓ M
  let Q := H.pCoreIn 2
  let P := M.pCoreIn 2
  let j : I →* M := inclusion inf_le_right
  let f := V.normalizerMonoidHom.comp j
  let S := MulAction.stabilizer (MulAut V) (⟨z, h.involution_mem_seed⟩ : V)
  let QI := Q.subgroupOf I
  let PI := P.subgroupOf I
  have hQI : Q ≤ I := h.local_cores_le_intersection.1
  have hPI : P ≤ I := h.local_cores_le_intersection.2
  have hfrange : f.range = S := by
    ext a
    constructor
    · rintro ⟨g, rfl⟩
      change f g ⟨z, h.involution_mem_seed⟩ = ⟨z, h.involution_mem_seed⟩
      apply Subtype.ext
      change (g : G) * z * (g : G)⁻¹ = z
      rw [mem_centralizer_singleton_iff.mp g.property.1, mul_inv_cancel_right]
    · intro ha
      obtain ⟨g, hg⟩ := h.seed_action_surjective a
      have hgH : (g : G) ∈ H := by
        apply mem_centralizer_singleton_iff.mpr
        have hh := congrArg Subtype.val (show a ⟨z, h.involution_mem_seed⟩ =
          ⟨z, h.involution_mem_seed⟩ from ha)
        rw [← hg] at hh
        exact mul_inv_eq_iff_eq_mul.mp hh
      exact ⟨⟨g, hgH, g.property⟩, hg⟩
  have hk : f.ker = PI := by
    change (V.normalizerMonoidHom.comp j).ker = PI
    rw [← MonoidHom.comap_ker, normalizerMonoidHom_ker, h.seed_centralizer]
    ext g
    rfl
  have hkp : IsPGroup 2 f.ker := by
    rw [hk]
    exact (isPGroup_pCoreIn 2 M).comap_subtype
  have hjoin : QI ⊔ PI = pCore 2 I := by
    apply map_injective I.subtype_injective
    rw [← subgroupOf_sup hQI hPI, subgroupOf_map_subtype,
      inf_eq_left.mpr (sup_le hQI hPI)]
    exact h.local_cores_structure.2.2.1.symm
  let r := f.rangeRestrict
  have hrker : IsPGroup 2 r.ker := by
    have he : r.ker = f.ker := by ext g; exact Subtype.ext_iff
    rw [he]
    exact hkp
  have hr : (pCore 2 I).map r = pCore 2 f.range := by
    rw [← r.comap_pCore_of_ker_isPGroup f.rangeRestrict_surjective hrker,
      map_comap_eq_self_of_surjective f.rangeRestrict_surjective]
  have hfcore : (pCore 2 I).map f = f.range.pCoreIn 2 := by
    rw [pCoreIn, ← hr, map_map]
    rfl
  have hpbot : PI.map f = ⊥ := (map_eq_bot_iff PI).mpr (hk ▸ le_rfl)
  rw [← hjoin, Subgroup.map_sup, hpbot, sup_bot_eq, hfrange] at hfcore
  exact hfcore

omit [Finite G] in
private theorem displacement_mem_point_core
    (e : V ≃* Multiplicative (Fin 3 → ZMod 2))
    (a : MulAut V) (ha : orderOf a = 2) (u w : V) (hu : u ≠ 1)
    (hw : a w * w⁻¹ = u) :
    a ∈ (MulAction.stabilizer (MulAut V) u).pCoreIn 2 := by
  let s := Matrix.PSL3Two.MarkedAutomorphisms.NaturalFlag.slAut
  let k : MulAut V ≃* Matrix.PSL3Two.SL := (MulAut.congr e).trans s.symm
  have hk (b : MulAut V) (v : V) :
      BinaryLinearThree.W (k b) (e v).toAdd = (e (b v)).toAdd := by
    change (k b).val.mulVec (e v).toAdd = (e (b v)).toAdd
    rw [← Matrix.PSL3Two.MarkedAutomorphisms.NaturalFlag.slAut_apply]
    change (s (s.symm ((MulAut.congr e) b)) (e v)).toAdd = _
    rw [s.apply_symm_apply]
    simp only [MulAut.congr_apply, MulEquiv.trans_apply, e.symm_apply_apply]
  have hpoint : (MulAction.stabilizer (MulAut V) u).map k.toMonoidHom =
      BinaryLinearThree.naturalPoint (e u).toAdd := by
    have hc : (BinaryLinearThree.naturalPoint (e u).toAdd).comap k.toMonoidHom =
        MulAction.stabilizer (MulAut V) u := by
      ext b
      change BinaryLinearThree.W (k b) (e u).toAdd = (e u).toAdd ↔ b u = u
      rw [hk]
      exact e.injective.eq_iff
    rw [← hc, map_comap_eq_self_of_surjective k.surjective]
  have hu0 : (e u).toAdd ≠ 0 := by
    intro hh
    exact hu (e.injective (hh.trans e.map_one.symm))
  have hd : BinaryLinearThree.W (k a) (e w).toAdd - (e w).toAdd = (e u).toAdd := by
    rw [hk]
    have hh := congrArg (fun v : V => (e v).toAdd) hw
    rw [map_mul, map_inv] at hh
    simpa only [toAdd_mul, toAdd_inv, sub_eq_add_neg] using hh
  have hm := BinaryLinearThree.involution_mem_naturalPoint_core (k a)
    ((k.orderOf_eq a).trans ha) (e u).toAdd hu0 (e w).toAdd hd
  rw [← hpoint, ← map_pCoreIn_of_injective 2 _ k.toMonoidHom k.injective] at hm
  exact (mem_map_iff_mem k.injective).mp hm

/-- Every seed transvection with marked displacement has an actual involutory
lift in the original point core, with its full action on the seed retained. -/
theorem TypeAt.exists_point_core_involution_of_displacement (h : TypeAt z V)
    (e : V ≃* Multiplicative (Fin 3 → ZMod 2))
    (a : MulAut V) (ha : orderOf a = 2) (w : V)
    (hw : a w * w⁻¹ = (⟨z, h.involution_mem_seed⟩ : V)) :
    ∃ t : normalizer (V : Set G),
      (t : G) ∈ (involutionCentralizer z).pCoreIn 2 ∧ t ^ 2 = 1 ∧
        V.normalizerMonoidHom t = a := by
  let M := normalizer (V : Set G)
  let I := involutionCentralizer z ⊓ M
  let Q := (involutionCentralizer z).pCoreIn 2
  let j : I →* M := inclusion inf_le_right
  let f := V.normalizerMonoidHom.comp j
  have hz1 : (⟨z, h.involution_mem_seed⟩ : V) ≠ 1 := by
    intro hz
    have hh := h.involution
    rw [show z = 1 from congrArg Subtype.val hz, orderOf_one] at hh
    contradiction
  have hm := displacement_mem_point_core e a ha ⟨z, h.involution_mem_seed⟩ w hz1 hw
  rw [← h.point_core_action_image] at hm
  obtain ⟨q, hq, hqa⟩ := hm
  obtain ⟨t, ht, ht2, hdiff⟩ := h.centralizer_core_involutory_representative q hq
  let tM : M := ⟨t, (h.local_cores_le_intersection.1 ht).2⟩
  have hk : tM * (j q)⁻¹ ∈ V.normalizerMonoidHom.ker := by
    rw [normalizerMonoidHom_ker, h.seed_centralizer]
    exact hdiff
  have he : V.normalizerMonoidHom tM = a := by
    have hh : V.normalizerMonoidHom (tM * (j q)⁻¹) = 1 := hk
    rw [map_mul, map_inv] at hh
    exact (mul_inv_eq_one.mp hh).trans hqa
  exact ⟨tM, ht, Subtype.ext ht2, he⟩

end CFSG.Quasithin.HigmanSims
