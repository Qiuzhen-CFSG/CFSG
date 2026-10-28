module
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.SylowGeometry.SourceWitnesses.MarkedProduct.Action
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.SylowGeometry.SourceWitnesses.MarkedProduct.Concrete

/-!
# Independent Baumann action on the two cubic factors

If every Baumann element has equal signs on the definite planes, each maximum
order elementary subgroup has trivial image: any nontrivial equal-sign image
violates the replacement fixed-space/order inequality. The Thompson image then
vanishes, contradicting the original family commutator identity. Thus an actual
Baumann element has unequal signs. This supplies joint product surjectivity.

Source: Aschbacher–Smith, 15.4.12(6), printed pp.1160–1161.
-/

@[expose] public section
open Subgroup Stellmacher
open OrthogonalFourBinary OrthogonalFourBinary.TerminalLines OrthogonalFourBinary.SylowGeometry
namespace CFSG.Quasithin.Chapter15.Section04.LocalSetup.SourceWitnesses.MarkedProduct
open FamilySource FamilySource.ModuleStructure
open FamilySource.ModuleStructure.BinaryNormalizer FamilySource.ModuleStructure.BaumannPair
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
private theorem action_kernel {W : Subgroup G} (d : Action W) :
    d.actor.ker = centralizer (W : Set G) := by
  ext g
  constructor
  · intro hg w hw
    have hh := d.intertwines g ⟨w,hw⟩
    rw [show d.actor g = 1 from hg, map_one] at hh
    change (d.coordinates.symm (d.coordinates ⟨w,hw⟩) : G) = g*w*g⁻¹ at hh
    rw [d.coordinates.symm_apply_apply] at hh
    exact (mul_inv_eq_iff_eq_mul.mp hh.symm).symm
  · intro hg
    apply vectorAction_injective
    apply MulEquiv.ext
    intro v
    let w := d.coordinates.symm v
    have hh := d.intertwines g w
    rw [d.coordinates.apply_symm_apply] at hh
    have he : g * (w : G) * g⁻¹ = w := mul_inv_eq_iff_eq_mul.mpr (hg w w.property).symm
    have hcv : d.coordinates.symm (vectorAction (d.actor g) v) = d.coordinates.symm v :=
      Subtype.ext (hh.trans he)
    exact d.coordinates.symm.injective hcv

omit [Finite G] in
private theorem fixed_card_bound {W : Subgroup G} (d : Action W) (A : Subgroup G) :
    Nat.card (W ⊓ centralizer (A : Set G) : Subgroup G) ≤
      Nat.card (FixedVectors (A.map d.actor)) := by
  let f : (W ⊓ centralizer (A : Set G) : Subgroup G) → FixedVectors (A.map d.actor) :=
    fun w => ⟨(d.coordinates ⟨w,w.property.1⟩).toAdd, by
      rintro _ ⟨a,ha,rfl⟩
      change vectorAction (d.actor a) (d.coordinates ⟨w,w.property.1⟩) =
        d.coordinates ⟨w,w.property.1⟩
      apply d.coordinates.symm.injective
      apply Subtype.ext
      rw [d.coordinates.symm_apply_apply]
      exact (d.intertwines a ⟨w,w.property.1⟩).trans
        (mul_inv_eq_iff_eq_mul.mpr (w.property.2 a ha))⟩
  apply Nat.card_le_card_of_injective f
  intro a b h
  exact Subtype.ext (congrArg (fun w : W => (w : G)) (d.coordinates.injective
    (congrArg (fun z : FixedVectors (A.map d.actor) => z.val) h)))

theorem thompson_killed_of_equal_parity {W : Subgroup G} [W.Normal]
    [IsElementaryAbelian 2 W] (d : Action W)
    (hpar : ∀ j ∈ elementaryAbelianMaxJ (⊤ : Subgroup G),
      (codeEquiv.symm (d.actor j)).1.2 = (codeEquiv.symm (d.actor j)).2.1.2) :
    elementaryAbelianMaxJ (⊤ : Subgroup G) ≤ d.actor.ker := by
  apply sSup_le
  intro A hA
  have hAJ : A ≤ elementaryAbelianMaxJ (⊤ : Subgroup G) := le_sSup hA
  have hmap : A.map d.actor = ⊥ := by
    by_contra hn
    let : IsElementaryAbelian 2 A := hA.2.1
    let : IsElementaryAbelian 2 (A.map d.actor) := hA.2.1.map d.actor
    have hcard : Nat.card W = 16 := by
      rw [Nat.card_congr d.coordinates.toEquiv, Nat.card_eq_fintype_card]
      decide +kernel
    have hlo := maxElementary_card_le_fixed_mul_image ⊤ W A le_top hA d.actor (action_kernel d)
    rw [hcard] at hlo
    have hlow : 16 ≤ Nat.card (FixedVectors (A.map d.actor)) * Nat.card (A.map d.actor) :=
      hlo.trans (Nat.mul_le_mul_right _ (fixed_card_bound d A))
    have hbase : A.map d.actor ≤ base := by
      rintro _ ⟨a,ha,rfl⟩
      exact d.maximum_family_base A hA ha
    have hp : ∀ b ∈ A.map d.actor, (codeEquiv.symm b).1.2 = (codeEquiv.symm b).2.1.2 := by
      rintro _ ⟨a,ha,rfl⟩
      exact hpar a (hAJ ha)
    exact Nat.not_lt_of_ge hlow
      (Concrete.equal_parity_elementary_strict_fixed_bound (A.map d.actor) hbase hp hn)
  exact (Subgroup.map_eq_bot_iff _).mp hmap

theorem SourceAction.exists_independent_parity
    {K : GroupClass} {T : Sylow 2 G} {M X : Subgroup G}
    (d : SourceAction T M X) (h : Input K T M X 2) :
    ∃ b : (ChapterB.baumann (T : Subgroup G)).subgroupOf M,
      (codeEquiv.symm (d.actor b)).1.2 ≠ (codeEquiv.symm (d.actor b)).2.1.2 := by
  by_contra! hp
  let W := movedModule (T : Subgroup G) M X
  let : IsElementaryAbelian 2 W := h.moved_elementary
  have hWT : W ≤ (T : Subgroup G) := h.moved_le.trans
    (localV_le_sylow T M h.sylow_le (h.ambient.evenCharacteristic T M h.maximal h.sylow_le))
  let W' := W.subgroupOf (T : Subgroup G)
  let e : W' ≃* W := subgroupOfEquivOfLe hWT
  let : W'.Normal := normal_subgroupOf_of_le_normalizer (h.sylow_le.trans h.moved_normalized)
  let : IsElementaryAbelian 2 W' := IsElementaryAbelian.subgroupOf hWT
  let a : Action W' :=
    { coordinates := e.trans d.coordinates
      actor := d.actor.comp (inclusion h.sylow_le)
      intertwines := by
        intro g w
        apply Subtype.ext
        exact d.intertwines (inclusion h.sylow_le g) (e w) }
  have hJmap : (elementaryAbelianMaxJ (⊤ : Subgroup (T : Subgroup G))).map (T : Subgroup G).subtype =
      elementaryAbelianMaxJ (T : Subgroup G) := by
    have he := elementaryAbelianMaxJ_map_injective (T : Subgroup G).subtype (T : Subgroup G).subtype_injective (⊤ : Subgroup (T : Subgroup G))
    simpa only [←MonoidHom.range_eq_map, range_subtype] using he.symm
  have hJS : elementaryAbelianMaxJ (T : Subgroup G) ≤ ChapterB.baumann (T : Subgroup G) := by
    refine le_inf (sSup_le fun A hA => hA.1) ?_
    intro j hj z hz
    exact ((mem_omegaOneCenterAmbient_iff _ _).mp hz).2.2 j hj |>.symm
  have hkill := thompson_killed_of_equal_parity a (fun j hj => by
    have hh : (j : G) ∈ elementaryAbelianMaxJ (T : Subgroup G) :=
      hJmap ▸ (mem_map.mpr ⟨j,hj,rfl⟩)
    exact hp ⟨inclusion h.sylow_le j,hJS hh⟩)
  apply d.thompson_image_ne_bot h
  apply (Subgroup.map_eq_bot_iff _).mpr
  intro m hm
  obtain ⟨j,hj,hjm⟩ := hJmap.symm.le hm
  have he : inclusion h.sylow_le j = m := Subtype.ext hjm
  change d.actor m = 1
  rw [←he]
  exact hkill hj

end CFSG.Quasithin.Chapter15.Section04.LocalSetup.SourceWitnesses.MarkedProduct
