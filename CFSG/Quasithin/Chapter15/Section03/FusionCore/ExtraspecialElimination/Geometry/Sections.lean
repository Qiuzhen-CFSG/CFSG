module

public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.Actions
public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.RankComparison
public import Theory.ElementaryAbelian.BinaryQuotientRank

/-!
# Subgroup images in the actual sections of 15.3.49

The subspace associated to D is its actual image under U → U/Z, converted
from a subgroup of an elementary abelian group to a binary submodule.
Its quotient dimension is log₂ |U:D| when Z ≤ D. Cross-centralization is
therefore a fixed-space containment in the representation used by the rank
squeeze, with no freely chosen submodule or dimension identification.

The representative formula and faithfulness of SectionAction identify each
section-centralizer kernel with the intersection with Q_H. The same formula
turns [U,A] ≤ A and abelianness of A into quadratic action on U/Z.
All quotients are relative to their numerator; Z need not be normal in G.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), F.9.12–16,
printed pp.322–324, and 15.3.49(f)–(h), printed p.1143.
-/

@[expose] public section

open Subgroup Representation.BinaryOffender
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.Geometry
variable {G : Type*} [Group G]

/-- The literal image of D in U/Z, as a binary submodule. -/
noncomputable def sectionImage (U Z D : Subgroup G) [IsElementaryAbelian 2 U] :
    Submodule (ZMod 2) (Additive (U ⧸ Z.subgroupOf U)) :=
  AddSubgroup.toZModSubmodule 2
    (Subgroup.toAddSubgroup ((D.subgroupOf U).map (QuotientGroup.mk' (Z.subgroupOf U))))

/-- Passing modulo a subgroup already contained in D does not change membership. -/
theorem mem_sectionImage_iff (U Z D : Subgroup G) [IsElementaryAbelian 2 U]
    (hZD : Z ≤ D) (u : U) :
    Additive.ofMul (QuotientGroup.mk' (Z.subgroupOf U) u) ∈ sectionImage U Z D ↔
      (u : G) ∈ D := by
  change u ∈ ((D.subgroupOf U).map (QuotientGroup.mk' (Z.subgroupOf U))).comap
    (QuotientGroup.mk' (Z.subgroupOf U)) ↔ _
  rw [QuotientGroup.comap_map_mk', sup_eq_right.mpr (show Z.subgroupOf U ≤ D.subgroupOf U from
    fun _ hx => hZD hx)]
  rfl

/-- The fixed-space condition is exactly the ambient commutator containment. -/
theorem sectionImage_le_fixedSpace_iff
    (H U Z D A : Subgroup G) [IsElementaryAbelian 2 U]
    (action : SectionAction H U Z) (hDU : D ≤ U) (hAH : A ≤ H) :
    sectionImage U Z D ≤ fixedSpace action.representation (starImage H A) ↔ ⁅D, A⁆ ≤ Z := by
  constructor
  · intro h
    rw [commutator_comm]
    apply commutator_le.mpr
    intro a ha d hd
    have hv : Additive.ofMul (QuotientGroup.mk' (Z.subgroupOf U) ⟨d, hDU hd⟩) ∈
        sectionImage U Z D := by
      change QuotientGroup.mk' (Z.subgroupOf U) ⟨d, hDU hd⟩ ∈ (D.subgroupOf U).map _
      exact mem_map_of_mem _ hd
    have hf := h hv ⟨QuotientGroup.mk' (pCore 2 H) ⟨a, hAH ha⟩, mem_map_of_mem _ ha⟩
    change action.representation (QuotientGroup.mk' (pCore 2 H) ⟨a, hAH ha⟩)
      (Additive.ofMul (QuotientGroup.mk' (Z.subgroupOf U) ⟨d, hDU hd⟩)) = _ at hf
    rw [action.on_representatives] at hf
    have he := QuotientGroup.eq_iff_div_mem.mp (Additive.ofMul.injective hf)
    simpa only [mem_subgroupOf, div_eq_mul_inv, Subgroup.coe_mul, Subgroup.coe_inv,
      commutatorElement_def] using he
  · intro h v hv a
    obtain ⟨d, hd, he⟩ := (show ∃ d ∈ D.subgroupOf U,
      QuotientGroup.mk' (Z.subgroupOf U) d = v.toMul from hv)
    have hvEq : v = Additive.ofMul (QuotientGroup.mk' (Z.subgroupOf U) d) :=
      (congrArg Additive.ofMul he).symm
    subst v
    obtain ⟨x, hx, hxa⟩ := a.property
    change action.representation (a : H ⧸ pCore 2 H) _ = _
    rw [← hxa, action.on_representatives]
    apply congrArg Additive.ofMul
    apply QuotientGroup.eq_iff_div_mem.mpr
    have hc := (commutator_comm D A ▸ h) (commutator_mem_commutator hx hd)
    simpa [mem_subgroupOf, div_eq_mul_inv, commutatorElement_def] using hc

/-- Quotienting first by Z and then by the image of D gives the correct corank. -/
theorem sectionImage_quotient_finrank [Finite G]
    (U Z D : Subgroup G) [IsElementaryAbelian 2 U] (hZD : Z ≤ D) :
    Module.finrank (ZMod 2) (Additive (U ⧸ Z.subgroupOf U) ⧸ sectionImage U Z D) =
      Nat.log 2 (D.relIndex U) := by
  let q := QuotientGroup.mk' (Z.subgroupOf U)
  have hi : ((D.subgroupOf U).map q).index = D.relIndex U := by
    rw [← Subgroup.index_comap_of_surjective _ (QuotientGroup.mk'_surjective _),
      QuotientGroup.comap_map_mk', sup_eq_right.mpr (show Z.subgroupOf U ≤ D.subgroupOf U from
        fun _ hx => hZD hx)]
    rfl
  have hc : Nat.card (Additive (U ⧸ Z.subgroupOf U) ⧸ sectionImage U Z D) =
      D.relIndex U := by
    change (sectionImage U Z D).toAddSubgroup.index = _
    rw [sectionImage, AddSubgroup.toZModSubmodule_toAddSubgroup, Subgroup.index_toAddSubgroup]
    exact hi
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod] at hc
  rw [← hc, Nat.log_pow (by decide)]

/-- The first isomorphism theorem for the actual star image. -/
theorem starImage_card (H A : Subgroup G) (hAH : A ≤ H) :
    Nat.card (starImage H A) = (localTwoCore H).relIndex A := by
  rw [starImage, ← Subgroup.relIndex_ker, QuotientGroup.ker_mk']
  have he : (localTwoCore H).subgroupOf H = pCore 2 H := by
    exact Subgroup.comap_map_eq_self_of_injective H.subtype_injective _
  rw [← he, Subgroup.relIndex_subgroupOf hAH]

/-- The star rank when its kernel in A is identified with D. -/
theorem starImage_rank [Finite G]
    (H A D : Subgroup G) (hAH : A ≤ H) (hD : D = A ⊓ localTwoCore H) :
    rank (starImage H A) = Nat.log 2 (D.relIndex A) := by
  rw [rank, starImage_card H A hAH, hD, inf_comm, inf_relIndex_right]


/-- Faithfulness on U/Z identifies the exact F.9.12 kernel, without F.9.15 as an extra premise. -/
theorem sectionCentralizer_eq_core_intersection
    (H U Z A : Subgroup G) [IsElementaryAbelian 2 U]
    (action : SectionAction H U Z) (hAH : A ≤ H) :
    sectionCentralizer A U Z = A ⊓ localTwoCore H := by
  have hAZ : A ≤ normalizer (Z : Set G) := hAH.trans action.normalizes_layer
  apply le_antisymm
  · refine le_inf (commutatorPreimage_le _ _ _) ?_
    intro a ha
    have haA := commutatorPreimage_le A U Z ha
    have haH := hAH haA
    have hc := commutator_commutatorPreimage_le A U Z hAZ
    have he : action.representation (QuotientGroup.mk' (pCore 2 H) ⟨a, haH⟩) = 1 := by
      apply LinearMap.ext
      intro v
      obtain ⟨u, hu⟩ := QuotientGroup.mk'_surjective (Z.subgroupOf U) v.toMul
      have hv : v = Additive.ofMul (QuotientGroup.mk' (Z.subgroupOf U) u) :=
        (congrArg Additive.ofMul hu).symm
      subst v
      rw [action.on_representatives]
      apply congrArg Additive.ofMul
      apply QuotientGroup.eq_iff_div_mem.mpr
      simpa [mem_subgroupOf, commutatorElement_def, div_eq_mul_inv] using
        hc (commutator_mem_commutator ha u.property)
    have hq : QuotientGroup.mk' (pCore 2 H) ⟨a, haH⟩ = 1 :=
      action.faithful (he.trans (map_one action.representation).symm)
    exact mem_map_of_mem H.subtype ((QuotientGroup.eq_one_iff _).mp hq)
  · apply le_commutatorPreimage inf_le_left
    apply commutator_le.mpr
    intro a ha u hu
    obtain ⟨aH, haQ, haEq⟩ := ha.2
    have hq : QuotientGroup.mk' (pCore 2 H) aH = 1 :=
      (QuotientGroup.eq_one_iff _).mpr haQ
    have he := action.on_representatives aH ⟨u, hu⟩
    rw [hq, map_one] at he
    have hc := QuotientGroup.eq_iff_div_mem.mp (Additive.ofMul.injective he.symm)
    change (aH : G) = a at haEq
    simpa [mem_subgroupOf, commutatorElement_def, div_eq_mul_inv, haEq] using hc

/-- F.9.13(3) and abelianness of the actor imply quadratic action on the actual section. -/
theorem quadratic_of_commutator_le
    (H U Z A : Subgroup G) [IsElementaryAbelian 2 U] [IsMulCommutative A]
    (action : SectionAction H U Z) (hAH : A ≤ H) (hcomm : ⁅U, A⁆ ≤ A) :
    IsQuadratic action.representation (starImage H A) := by
  have hCU : ⁅U, A⁆ ≤ U :=
    le_normalizer_iff_commutator_le_left.mp (hAH.trans action.normalizes)
  have hCA : ⁅⁅U, A⁆, A⁆ ≤ Z :=
    ((commutator_mono hcomm le_rfl).trans_eq
      (commutator_self_eq_bot_iff.mpr inferInstance)).trans bot_le
  have hf := (sectionImage_le_fixedSpace_iff H U Z ⁅U, A⁆ A action hCU hAH).mpr hCA
  intro a ha b hb v
  obtain ⟨x, hx, rfl⟩ := hb
  obtain ⟨u, hu⟩ := QuotientGroup.mk'_surjective (Z.subgroupOf U) v.toMul
  have hv : v = Additive.ofMul (QuotientGroup.mk' (Z.subgroupOf U) u) :=
    (congrArg Additive.ofMul hu).symm
  subst v
  have hc : ⁅(x : G), (u : G)⁆ ∈ ⁅U, A⁆ := by
    rw [commutator_comm]
    exact commutator_mem_commutator hx u.property
  let c : U := ⟨⁅(x : G), (u : G)⁆, hCU hc⟩
  have him : Additive.ofMul (QuotientGroup.mk' (Z.subgroupOf U) c) ∈
      sectionImage U Z ⁅U, A⁆ := by
    change QuotientGroup.mk' (Z.subgroupOf U) c ∈ (⁅U, A⁆.subgroupOf U).map _
    exact mem_map_of_mem _ hc
  have hd : action.representation (QuotientGroup.mk' (pCore 2 H) x)
      (Additive.ofMul (QuotientGroup.mk' (Z.subgroupOf U) u)) -
      Additive.ofMul (QuotientGroup.mk' (Z.subgroupOf U) u) =
      Additive.ofMul (QuotientGroup.mk' (Z.subgroupOf U) c) := by
    rw [action.on_representatives]
    apply Additive.toMul.injective
    change QuotientGroup.mk' (Z.subgroupOf U)
      ⟨(x : G) * (u : G) * (x : G)⁻¹, _⟩ /
      QuotientGroup.mk' (Z.subgroupOf U) u = QuotientGroup.mk' (Z.subgroupOf U) c
    rw [← map_div]
    apply congrArg _
    apply Subtype.ext
    simp [c, div_eq_mul_inv, commutatorElement_def]
  rw [hd]
  exact hf him ⟨a, ha⟩

end CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.Geometry
