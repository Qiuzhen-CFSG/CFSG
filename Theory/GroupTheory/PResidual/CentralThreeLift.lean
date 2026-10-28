module
public import Theory.GroupTheory.PGroup.SupercriticalCubic
public import Theory.GroupTheory.PCoreImage

/-!
# Central three-group lifts and intersection residuals

A subgroup lying strictly above the intrinsic two-core in a three-group
extension has nontrivial two-residual. Centrality modulo that core makes
the central lift normalize the intersection residual. For any nontrivial
normal three-group image, the center has a nontrivial normal two-perfect
lift within the prescribed subgroup; its restricted quotient map has
exactly the intrinsic two-core as kernel.

These facts supply the central-lift step of Aschbacher–Smith 14.5.20,
assertion (*), printed p.1019, used in 14.7.9 on p.1045.
The original-group application is LocalReduction.ThreeCoreIntersection.
-/

public noncomputable section
open Subgroup
namespace Subgroup
variable {G : Type*} [Group G] [Finite G]

/-- A strict intersection above the two-core of a three-core extension has
nontrivial two-residual. -/
theorem intersection_twoResidual_ne_bot (Y M : Subgroup G)
    (h3 : IsPGroup 3 (Y ⧸ pCore 2 Y)) (hi : Y.pCoreIn 2 < Y ⊓ M) :
    (pResidual 2 (Y ⊓ M : Subgroup G)).map (Y ⊓ M).subtype ≠ ⊥ := by
  intro hz
  let I := Y ⊓ M
  have hr : pResidual 2 I = ⊥ :=
    (map_eq_bot_iff_of_injective _ I.subtype_injective).mp hz
  have hI : IsPGroup 2 I := by
    have hh := isPGroup_quotient_pResidual (G := I) 2
    exact (hh.of_equiv (QuotientGroup.quotientMulEquivOfEq hr)).of_equiv
      QuotientGroup.quotientBot
  let f : I →* Y ⧸ pCore 2 Y := (QuotientGroup.mk' (pCore 2 Y)).comp
    (inclusion (show I ≤ Y from inf_le_left))
  have hf : f.range = ⊥ := by
    have hd := (hI.of_surjective f.rangeRestrict f.rangeRestrict_surjective).disjoint_of_coprime (h3.to_subgroup ⊤)
      (by decide : Nat.Coprime 2 3)
    simpa only [disjoint_top] using hd
  have hle : I ≤ Y.pCoreIn 2 := by
    intro x hx
    have he : f ⟨x,hx⟩ = 1 := mem_bot.mp (hf ▸ (show f ⟨x,hx⟩ ∈ f.range from ⟨⟨x,hx⟩,rfl⟩))
    exact mem_map_of_mem Y.subtype ((QuotientGroup.eq_one_iff _).mp he)
  exact hi.not_ge hle

omit [Finite G] in
/-- A subgroup central modulo the two-core normalizes every intersection
containing that core, and hence its two-residual. -/
theorem normalizes_intersection_twoResidual (Y M Z : Subgroup G)
    (hQM : Y.pCoreIn 2 ≤ M) (hc : ⁅Z,Y⁆ ≤ Y.pCoreIn 2) :
    Z ≤ normalizer ((pResidual 2 (Y ⊓ M : Subgroup G)).map (Y ⊓ M).subtype : Set G) := by
  have hn : Z ≤ normalizer (Y ⊓ M : Set G) :=
    le_normalizer_iff_commutator_le_right.mpr
      (((commutator_mono le_rfl inf_le_left).trans hc).trans
        (le_inf (pCoreIn_le 2 Y) hQM))
  exact hn.trans (normalizer_le_normalizer_characteristic_image (Y ⊓ M) (pResidual 2 (Y ⊓ M : Subgroup G)))

omit [Finite G] in
/-- Centrality in a star quotient lifts with the intrinsic core of Y,
not just the ambient quotient kernel. -/
theorem commutator_le_core_of_quotient_centralizes (Y Z : Subgroup G) [Y.Normal]
    (hc : ⁅Z.map (QuotientGroup.mk' (pCore 2 G)),
      Y.map (QuotientGroup.mk' (pCore 2 G))⁆ = ⊥) : ⁅Z,Y⁆ ≤ Y.pCoreIn 2 := by
  have hk : ⁅Z,Y⁆ ≤ pCore 2 G := by
    rw [←QuotientGroup.ker_mk' (pCore 2 G),←map_eq_bot_iff,map_commutator]
    exact hc
  have hn : ((pCore 2 G).subgroupOf Y).Normal := inferInstance
  have hp : IsPGroup 2 ((pCore 2 G).subgroupOf Y) := pCore_isPGroup.comap_subtype
  have hle : (pCore 2 G).subgroupOf Y ≤ pCore 2 Y := le_sSup ⟨hn,hp⟩
  intro x hx
  exact mem_map_of_mem Y.subtype (hle (show (⟨x,commutator_le_right Z Y hx⟩ : Y) ∈
    (pCore 2 G).subgroupOf Y from hk hx))

/-- Lift the nontrivial center of any normal three-group image within the
same original subgroup, retaining the full restricted two-core kernel. -/
theorem exists_normal_central_three_lift
    {D E : Type*} [Group D] [Finite D] [Group E] [Finite E]
    (q : D →* E) (hq : Function.Surjective q) (hk : IsPGroup 2 q.ker)
    (Y : Subgroup D) [Y.Normal] (h3 : IsPGroup 3 (Y.map q)) (hne : Y.map q ≠ ⊥) :
    ∃ Z : Subgroup D, Z ≤ Y ∧ Z.Normal ∧ IsPPerfect 2 Z ∧ Z ≠ ⊥ ∧
      Z.map q = (center (Y.map q)).map (Y.map q).subtype ∧
      (q.comp Z.subtype).ker = pCore 2 Z ∧
      Nonempty ((Z ⧸ pCore 2 Z) ≃* center (Y.map q)) ∧
      ⁅Z.map q,Y.map q⁆ = ⊥ := by
  let A := Y.map q
  let : A.Normal := Normal.map inferInstance q hq
  let C := (center A).map A.subtype
  let : C.Normal := inferInstance
  let : Nontrivial A := (nontrivial_iff_ne_bot A).mpr hne
  let : Nontrivial (center A) := h3.center_nontrivial
  have hCne : C ≠ ⊥ := by
    intro hz
    exact (nontrivial_iff_ne_bot (center A)).mp inferInstance
      ((map_eq_bot_iff_of_injective _ A.subtype_injective).mp hz)
  obtain ⟨Z,hZY,hZp,hm,hZN,_,hkZ,⟨eZ⟩⟩ := exists_three_lift_within_normal q hk Y C ⊤
    (map_subtype_le _) le_normalizer_of_normal ((h3.to_subgroup (center A)).map A.subtype)
  have hn : Z.Normal := normalizer_eq_top_iff.mp (top_unique (by simpa using hZN))
  have hZn : Z ≠ ⊥ := by
    intro he
    apply hCne
    rw [←hm,he,map_bot]
  refine ⟨Z,hZY,hn,hZp,hZn,hm,hkZ,
    ⟨eZ.trans (equivMapOfInjective (center A) A.subtype A.subtype_injective).symm⟩,?_⟩
  rw [hm]
  apply commutator_eq_bot_iff_le_centralizer.mpr
  rintro x ⟨z,hz,rfl⟩ y hy
  exact congrArg Subtype.val (mem_center_iff.mp hz (⟨y,hy⟩ : A))

end Subgroup
