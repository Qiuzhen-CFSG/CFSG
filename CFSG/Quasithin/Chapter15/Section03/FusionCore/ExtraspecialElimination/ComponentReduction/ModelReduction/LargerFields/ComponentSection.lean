module

public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.LocalTransfer

/-!
# The actual component section in U_H/Z

Define the binary subspace D as the image of [U_H,⟨L^T⟩] under the
literal quotient map U_H → U_H/Z. The component closure is normal in the
replacement H = ⟨L^T⟩Y₀T, so its commutator image is H*-invariant.

A generation identity with the preimage of C_{U_H/Z}(H) gives
D + C_{U_H/Z}(H) = U_H/Z. This is a transport lemma: the legitimate
B.2.14 application establishing that identity is still required.
No direct-sum condition is imposed.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), proof of
15.3.49, printed p.1144, the definition of U₀ and its tilde decomposition.
-/

public section

open Subgroup Representation.BinaryOffender
open scoped IsMulCommutative
open CFSG.Quasithin.Chapter15.Section03
open CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination
open CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction

namespace CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.ModelReduction.LargerFields
variable {G : Type*} [Group G]

variable (U Z : Subgroup G) [IsElementaryAbelian 2 U]

private noncomputable def sectionSubmodule (A : Subgroup G) :
    Submodule (ZMod 2) (Additive (U ⧸ Z.subgroupOf U)) :=
  AddSubgroup.toZModSubmodule 2 (Subgroup.toAddSubgroup
    ((A.subgroupOf U).map (QuotientGroup.mk' (Z.subgroupOf U))))

private theorem sectionSubmodule_invariant (H A : Subgroup G) (action : SectionAction H U Z)
    (hA : H ≤ normalizer (A : Set G))
    (g : H ⧸ pCore 2 H) (v : sectionSubmodule U Z A) :
    action.representation g v ∈ sectionSubmodule U Z A := by
  obtain ⟨h, rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 H) g
  obtain ⟨u, hu, he⟩ := v.property
  have hv : (v : Additive (U ⧸ Z.subgroupOf U)) =
      Additive.ofMul (QuotientGroup.mk' (Z.subgroupOf U) u) := congrArg Additive.ofMul he.symm
  rw [hv, action.on_representatives]
  exact ⟨⟨(h : G) * u * (h : G)⁻¹,
    le_normalizer_iff.mp action.normalizes h h.property u u.property⟩,
    le_normalizer_iff.mp hA h h.property u hu, rfl⟩

/-- The literal image of U₀ = [U_H,⟨L^T⟩] in the binary section U_H/Z. -/
noncomputable def componentSection (H ZS L T : Subgroup G)
    [IsElementaryAbelian 2 (localSpan ZS H)] :
    Submodule (ZMod 2) (Additive (localSpan ZS H ⧸ Z.subgroupOf (localSpan ZS H))) :=
  sectionSubmodule (localSpan ZS H) Z ⁅localSpan ZS H, localSpan L T⁆

/-- Relative normality makes the actual component subspace invariant under H*. -/
theorem componentSection_invariant (H ZS L Y0 T : Subgroup G)
    [IsElementaryAbelian 2 (localSpan ZS H)]
    (action : SectionAction H (localSpan ZS H) Z)
    (hgen : H = reducedOvergroup L Y0 T)
    (hcomm : L = ⁅L, Y0⁆) (hTY : T ≤ normalizer (Y0 : Set G))
    (g : H ⧸ pCore 2 H) (v : componentSection Z H ZS L T) :
    action.representation g v ∈ componentSection Z H ZS L T := by
  have hn := componentClosure_normal_in_replacement L Y0 T
    (le_normalizer_iff_commutator_le_left.mpr hcomm.ge) hTY
  rw [← hgen] at hn
  have hLH : localSpan L T ≤ H := hgen ▸ le_sup_left
  have hnorm := (normal_subgroupOf_iff_le_normalizer hLH).mp hn
  apply sectionSubmodule_invariant _ _ _ _ action _ g v
  intro h hh
  rw [mem_normalizer_iff_map_conj_eq, map_commutator,
    mem_normalizer_iff_map_conj_eq.mp (action.normalizes hh),
    mem_normalizer_iff_map_conj_eq.mp (hnorm hh)]

private theorem sectionSubmodule_sup (A B : Subgroup G) (hAU : A ≤ U) (hBU : B ≤ U) :
    sectionSubmodule U Z (A ⊔ B) = sectionSubmodule U Z A ⊔ sectionSubmodule U Z B := by
  have hs : (A ⊔ B).subgroupOf U = A.subgroupOf U ⊔ B.subgroupOf U := by
    apply map_injective U.subtype_injective
    rw [Subgroup.map_sup, map_subgroupOf_eq_of_le (sup_le hAU hBU),
      map_subgroupOf_eq_of_le hAU, map_subgroupOf_eq_of_le hBU]
  simp only [sectionSubmodule, hs, Subgroup.map_sup, SupHomClass.map_sup]

private theorem sectionSubmodule_self : sectionSubmodule U Z U = ⊤ := by
  apply top_unique
  intro v _
  obtain ⟨u, hu⟩ := QuotientGroup.mk'_surjective (Z.subgroupOf U) v.toMul
  exact ⟨u, u.property, hu⟩

private theorem sectionSubmodule_le_fixedSpace (H A : Subgroup G) (action : SectionAction H U Z)
    (hc : ⁅H, A⁆ ≤ Z) : sectionSubmodule U Z A ≤ fixedSpace action.representation ⊤ := by
  intro v hv ⟨g, _⟩
  obtain ⟨h, rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 H) g
  obtain ⟨u, hu, he⟩ := hv
  have hv : v = Additive.ofMul (QuotientGroup.mk' (Z.subgroupOf U) u) :=
    congrArg Additive.ofMul he.symm
  change action.representation (QuotientGroup.mk' (pCore 2 H) h) v = v
  rw [hv, action.on_representatives]
  apply congrArg Additive.ofMul
  apply QuotientGroup.eq_iff_div_mem.mpr
  change ((h : G) * (u : G) * (h : G)⁻¹) / (u : G) ∈ Z
  have hm := hc (commutator_mem_commutator h.property (show (u : G) ∈ A from hu))
  change (h : G) * (u : G) * (h : G)⁻¹ * (u : G)⁻¹ ∈ Z at hm
  simpa only [div_eq_mul_inv] using hm

/-- Transport a quotient-centralizer generation identity to the sum needed by the natural-section argument. This lemma does not supply the B.2.14 application. -/
theorem componentSection_split_of_commutatorPreimage (H ZS L T : Subgroup G)
    [IsElementaryAbelian 2 (localSpan ZS H)]
    (action : SectionAction H (localSpan ZS H) Z)
    (hUH : localSpan ZS H ≤ H) (hL0H : localSpan L T ≤ H)
    (hsplit : localSpan ZS H = ⁅localSpan ZS H, localSpan L T⁆ ⊔
      commutatorPreimage (localSpan ZS H) H Z) :
    componentSection Z H ZS L T ⊔ fixedSpace action.representation ⊤ = ⊤ := by
  have hcommU : ⁅localSpan ZS H, localSpan L T⁆ ≤ localSpan ZS H :=
    le_normalizer_iff_commutator_le_left.mp (hL0H.trans action.normalizes)
  have he := congrArg (sectionSubmodule (localSpan ZS H) Z) hsplit
  rw [sectionSubmodule_self, sectionSubmodule_sup _ _ _ _ hcommU
    (commutatorPreimage_le _ _ _)] at he
  apply top_unique
  rw [he]
  apply sup_le_sup_left
  apply sectionSubmodule_le_fixedSpace _ _ _ _ action
  rw [commutator_comm]
  exact commutator_commutatorPreimage_le _ _ _ (hUH.trans action.normalizes_layer)

/-- Membership in the component subspace is represented by an actual component commutator. -/
theorem mem_componentSection (H ZS L T : Subgroup G)
    [IsElementaryAbelian 2 (localSpan ZS H)]
    (v : Additive (localSpan ZS H ⧸ Z.subgroupOf (localSpan ZS H))) :
    v ∈ componentSection Z H ZS L T ↔
      ∃ u : localSpan ZS H, (u : G) ∈ ⁅localSpan ZS H, localSpan L T⁆ ∧
        Additive.ofMul (QuotientGroup.mk' (Z.subgroupOf (localSpan ZS H)) u) = v := by
  rfl

end CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.ModelReduction.LargerFields
