module

public import CFSG.Quasithin.ChapterI.Section04To05.HigmanSims.Construction.NonseedEightCentralizer

/-!
# The actual normalizer action on a nonseed elementary eight

The order768 normalizer inside the original involution centralizer has
kernel the full order32 centralizer of the eight. Its actual conjugation
image consequently fills the order24 stabilizer of the marked involution
in the automorphism group of that same elementary eight.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped Pointwise
namespace CFSG.Quasithin.HigmanSims
variable {G : Type*} [Group G] [Finite G] {z : G} {V : Subgroup G}

/-- Conjugation on the literal elementary eight by its normalizer inside
the original marked involution centralizer. -/
@[expose] def pointCoreEightNormalizerAction (E : pointCoreEights z) :
    (involutionCentralizer z ⊓ normalizer (E.val : Set G) : Subgroup G) →*
      MulAut E.val :=
  E.val.normalizerMonoidHom.comp (inclusion inf_le_right)

omit [Finite G] in
private theorem action_fixes_point (E : pointCoreEights z)
    (g : (involutionCentralizer z ⊓ normalizer (E.val : Set G) : Subgroup G)) :
    pointCoreEightNormalizerAction E g ∈
      MulAction.stabilizer (MulAut E.val) (⟨z, E.property.2.1⟩ : E.val) := by
  change pointCoreEightNormalizerAction E g ⟨z, E.property.2.1⟩ = ⟨z, E.property.2.1⟩
  apply Subtype.ext
  change (g : G) * z * (g : G)⁻¹ = z
  rw [mem_centralizer_singleton_iff.mp g.property.1, mul_inv_cancel_right]

/-- The same actual conjugation action, with its codomain restricted to
the automorphisms fixing the marked involution. -/
@[expose] def pointCoreEightPointAction (E : pointCoreEights z) :
    (involutionCentralizer z ⊓ normalizer (E.val : Set G) : Subgroup G) →*
      MulAction.stabilizer (MulAut E.val) (⟨z, E.property.2.1⟩ : E.val) :=
  (pointCoreEightNormalizerAction E).codRestrict _ (by exact action_fixes_point E)

omit [Finite G] in
private theorem centralizer_le_normalizer_point (E : pointCoreEights z) :
    centralizer (E.val : Set G) ≤
      involutionCentralizer z ⊓ normalizer (E.val : Set G) := by
  refine le_inf ?_ (centralizer_le_normalizer _)
  intro g hg
  exact mem_centralizer_singleton_iff.mpr (hg z E.property.2.1).symm

omit [Finite G] in
private theorem action_kernel (E : pointCoreEights z) :
    (pointCoreEightNormalizerAction E).ker =
      (centralizer (E.val : Set G)).subgroupOf
        (involutionCentralizer z ⊓ normalizer (E.val : Set G)) := by
  ext g
  change E.val.normalizerMonoidHom (inclusion inf_le_right g) = 1 ↔
    (g : G) ∈ centralizer (E.val : Set G)
  change inclusion inf_le_right g ∈ E.val.normalizerMonoidHom.ker ↔ _
  rw [normalizerMonoidHom_ker]
  rfl

private theorem action_range_card (h : TypeAt z V) (E : pointCoreEights z)
    (hEn : E.val ∉ pointCoreSeedOrbit z V) :
    Nat.card (pointCoreEightNormalizerAction E).range = 24 := by
  have hprod := (pointCoreEightNormalizerAction E).ker.card_mul_index
  rw [index_ker, action_kernel,
    Nat.card_congr (subgroupOfEquivOfLe (centralizer_le_normalizer_point E)).toEquiv,
    h.point_core_nonseed_eight_centralizer_card E hEn,
    h.point_core_nonseed_eight_normalizer_card E hEn] at hprod
  omega

/-- Every automorphism of a nonseed elementary eight fixing the marked
involution is induced by its actual normalizer in the original centralizer. -/
theorem TypeAt.point_core_nonseed_eight_action_range (h : TypeAt z V)
    (E : pointCoreEights z) (hEn : E.val ∉ pointCoreSeedOrbit z V) :
    (pointCoreEightNormalizerAction E).range =
      MulAction.stabilizer (MulAut E.val) (⟨z, E.property.2.1⟩ : E.val) := by
  let S := MulAction.stabilizer (MulAut E.val) (⟨z, E.property.2.1⟩ : E.val)
  let : IsElementaryAbelian 2 E.val := E.property.2.2.1
  have hz : (⟨z, E.property.2.1⟩ : E.val) ≠ 1 := by
    intro he
    have hz1 : z = 1 := congrArg Subtype.val he
    have hi := h.involution
    simp [hz1] at hi
  have hS : Nat.card S ≤ 24 := Nat.le_of_dvd (by decide)
    (elementaryEight_fixed_point_image_card_dvd_twentyfour E.property.2.2.2
      ⟨z, E.property.2.1⟩ hz S (fun a => a.property))
  apply eq_of_le_of_card_ge ?_ ?_
  · rintro _ ⟨g, rfl⟩
    exact action_fixes_point E g
  · rw [action_range_card h E hEn]
    exact hS

/-- The canonical actual normalizer action onto the point stabilizer is
surjective; no replacement model for the elementary eight is chosen. -/
theorem TypeAt.point_core_nonseed_eight_point_action_surjective (h : TypeAt z V)
    (E : pointCoreEights z) (hEn : E.val ∉ pointCoreSeedOrbit z V) :
    Function.Surjective (pointCoreEightPointAction E) := by
  intro a
  have ha : a.val ∈ (pointCoreEightNormalizerAction E).range := by
    rw [h.point_core_nonseed_eight_action_range E hEn]
    exact a.property
  obtain ⟨g, hg⟩ := ha
  exact ⟨g, Subtype.ext hg⟩

private theorem core_le_eight_normalizer (h : TypeAt z V) (E : pointCoreEights z)
    (hEn : E.val ∉ pointCoreSeedOrbit z V) :
    (involutionCentralizer z).pCoreIn 2 ≤
      involutionCentralizer z ⊓ normalizer (E.val : Set G) := by
  obtain ⟨f, _, T, _, hk, _, _, _, _, _, hN, _⟩ :=
    h.point_core_nonseed_eight_marking E hEn
  rintro _ ⟨q, hq, rfl⟩
  refine ⟨q.property, ?_⟩
  change q ∈ (normalizer (E.val : Set G)).subgroupOf (involutionCentralizer z)
  rw [hN]
  change f q ∈ MulAction.stabilizer (Equiv.Perm (Fin 5)) (T : Set (Fin 5))
  have hqf : f q = 1 := by
    change q ∈ f.ker
    rwa [hk]
  rw [hqf]
  exact one_mem _

/-- The original point core induces exactly the normal Klein four of
the full point stabilizer acting on the literal nonseed elementary eight. -/
theorem TypeAt.point_core_nonseed_eight_core_image (h : TypeAt z V)
    (E : pointCoreEights z) (hEn : E.val ∉ pointCoreSeedOrbit z V) :
    (((involutionCentralizer z).pCoreIn 2).subgroupOf
      (involutionCentralizer z ⊓ normalizer (E.val : Set G))).map
        (pointCoreEightPointAction E) =
      pCore 2 (MulAction.stabilizer (MulAut E.val) (⟨z, E.property.2.1⟩ : E.val)) := by
  let H := involutionCentralizer z
  let N := H ⊓ normalizer (E.val : Set G)
  let Q := H.pCoreIn 2
  let R := Q.subgroupOf N
  let S := MulAction.stabilizer (MulAut E.val) (⟨z, E.property.2.1⟩ : E.val)
  let f := pointCoreEightPointAction E
  let j : N →* H := inclusion inf_le_left
  have hQN : Q ≤ N := core_le_eight_normalizer h E hEn
  have hR : R = (pCore 2 H).comap j := by
    ext q
    change H.subtype (j q) ∈ (pCore 2 H).map H.subtype ↔ j q ∈ pCore 2 H
    exact mem_map_iff_mem H.subtype_injective
  let : R.Normal := hR ▸ inferInstanceAs ((pCore 2 H).comap j).Normal
  have hf : Function.Surjective f := h.point_core_nonseed_eight_point_action_surjective E hEn
  let : (R.map f).Normal := (inferInstance : R.Normal).map f hf
  have hp : IsPGroup 2 R := (isPGroup_pCoreIn 2 H).comap_subtype
  have hle : R.map f ≤ pCore 2 S := le_sSup ⟨inferInstance, hp.map f⟩
  have hRc : Nat.card R = 64 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hQN).toEquiv]
    change Nat.card ((pCore 2 H).map H.subtype) = 64
    rw [card_map_of_injective H.subtype_injective, ← h.centralizer_fitting]
    exact h.centralizer_core_card
  have hk : f.ker = (centralizer (E.val : Set G)).subgroupOf N := by
    rw [← action_kernel]
    ext g
    exact Subtype.ext_iff
  have hkc : Nat.card (R ⊓ f.ker : Subgroup N) = 16 := by
    rw [hk, ← card_subtype N (R ⊓ (centralizer (E.val : Set G)).subgroupOf N),
      map_inf _ _ _ N.subtype_injective, subgroupOf_map_subtype,
      subgroupOf_map_subtype, inf_eq_left.mpr hQN,
      inf_eq_left.mpr (centralizer_le_normalizer_point E)]
    exact h.point_core_eight_centralizer_card E
  have himage : Nat.card (R.map f) = 4 := by
    have hh := IsElementaryAbelian.card_inf_ker_mul_card_map R f
    rw [hkc, hRc] at hh
    omega
  have hS : Nat.card S = 24 := by
    change Nat.card (MulAction.stabilizer (MulAut E.val) (⟨z, E.property.2.1⟩ : E.val)) = 24
    rw [← h.point_core_nonseed_eight_action_range E hEn]
    exact action_range_card h E hEn
  let : IsElementaryAbelian 2 E.val := E.property.2.2.1
  have hz : (⟨z, E.property.2.1⟩ : E.val) ≠ 1 := by
    intro he
    have hz1 : z = 1 := congrArg Subtype.val he
    have hi := h.involution
    simp [hz1] at hi
  obtain ⟨e⟩ := elementaryEight_fixed_point_order24_equiv_S4 E.property.2.2.2
    ⟨z, E.property.2.1⟩ hz S hS (fun a => a.property)
  have hcore : Nat.card (pCore 2 S) = 4 := by
    rw [← Theory.SpecificGroups.SymmetricSix.DuadCalculation.core_card,
      Theory.SpecificGroups.SymmetricSix.DuadCalculation.core_eq,
      ← pCore_map_iso 2 e, card_map_of_injective e.injective]
  exact eq_of_le_of_card_ge hle (by rw [hcore, himage])

end CFSG.Quasithin.HigmanSims
