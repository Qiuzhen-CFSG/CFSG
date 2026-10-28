module

public import Theory.SpecificGroups.PSL3Two.SplitBlockActions.SplitParabolic.NaturalIdentification
public import Theory.SpecificGroups.PSL3Two.Parabolics.MarkedProduct
public import Theory.GroupTheory.PResidual.NormalizerCore

/-!
# Intrinsic cores and residual actors in the split natural block

The projection has an elementary abelian kernel of order eight. Core lifting
therefore identifies the point parabolic's intrinsic two-core with the
preimage of the SL₃(2) translation four-group, and the inverse coordinates
identify this preimage with k(U). Five small cubic commutator identities
show that the core lies in the two-residual. Thus this is also the literal
embedded O₂(L₁), where L₁ = O² of the point preimage.

The standard sixty-four group is Sylow in the whole block. The finite-group
residual/Sylow supplement theorem identifies O² of the line preimage joined
with this Sylow group with the full line preimage, the source actor L₂T_L.
No ambient normality of either parabolic is asserted or used.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, Notation
12.8.2 and proof of 14.4.4, printed p.1007.
-/

@[expose] public section

namespace Matrix.PSL3Two.SplitParabolic
open Subgroup Unitriangular

instance : Finite Block := Finite.of_equiv (E3 × SL) SemidirectProduct.equivProd.symm

theorem card_E3 : Nat.card E3 = 8 := by
 rw [Nat.card_eq_fintype_card]
 decide

/-- The preimage retains its literal right coordinate. -/
def preimageEquiv (P : Subgroup SL) : P.comap projection ≃ E3 × P where
 toFun x := (x.val.left, ⟨x.val.right,x.property⟩)
 invFun x := ⟨⟨x.1,x.2⟩,x.2.property⟩
 left_inv _ := rfl
 right_inv _ := rfl

theorem card_preimage (P : Subgroup SL) : Nat.card (P.comap projection) = 8 * Nat.card P := by
 rw [Nat.card_congr (preimageEquiv P),Nat.card_prod,card_E3]

theorem card_standardSylow : Nat.card standardSylow = 64 :=
 (Nat.card_congr sylowEquiv.toEquiv).symm.trans card_T

/-- The displayed sixty-four group is a Sylow subgroup of the whole block. -/
noncomputable def naturalSylow : Sylow 2 Block := Sylow.ofCard standardSylow (by
 rw [card_standardSylow,SemidirectProduct.card,card_E3,card_SL]
 decide +kernel)

theorem naturalSylow_coe : (naturalSylow : Subgroup Block) = standardSylow := rfl

theorem card_linePreimage : Nat.card linePreimage = 192 := by
 rw [linePreimage,card_preimage,card_lineParabolicSL]

theorem card_pointPreimage : Nat.card pointPreimage = 192 := by
 rw [pointPreimage,card_preimage,card_pointParabolicSL]

/-- The source's second actor is the residual joined with T_L. -/
theorem line_residual_sup_sylow :
 (pResidual 2 linePreimage).map linePreimage.subtype ⊔ standardSylow = linePreimage := by
 let S : Sylow 2 linePreimage := Sylow.ofCard (standardSylow.subgroupOf linePreimage) (by
  rw [Nat.card_congr (subgroupOfEquivOfLe standardSylow_le_line).toEquiv,
   card_standardSylow,card_linePreimage]
  decide +kernel)
 have he := congrArg (fun B : Subgroup linePreimage => B.map linePreimage.subtype)
  (pResidual_sup_sylow_eq_top S)
 rw [Subgroup.map_sup,← MonoidHom.range_eq_map,range_subtype] at he
 change _ ⊔ (standardSylow.subgroupOf linePreimage).map linePreimage.subtype = _ at he
 rwa [map_subgroupOf_eq_of_le standardSylow_le_line] at he

theorem projection_kernel_isPGroup : IsPGroup 2 projection.ker := by
 change IsPGroup 2 SemidirectProduct.rightHom.ker
 rw [← SemidirectProduct.range_inl_eq_ker_rightHom,MonoidHom.range_eq_map]
 exact ((IsPGroup.of_card (n := 3) card_E3).to_subgroup ⊤).map _

/-- O₂ of the point parabolic is the full preimage of its translation four-group. -/
theorem pointPreimage_core : pointPreimage.pCoreIn 2 = MarkedAutomorphisms.pointV.comap projection := by
 have hk : projection.ker ≤ pointPreimage := by
  intro x hx
  change projection x ∈ pointParabolicSL
  rw [MonoidHom.mem_ker.mp hx]
  exact pointParabolicSL.one_mem
 have hkcore : projection.ker ≤ pointPreimage.pCoreIn 2 :=
  le_pCoreIn_of_normalizes projection_kernel_isPGroup hk le_normalizer_of_normal
 have hm := map_pCoreIn_of_ker_isPGroup projection projection_kernel_isPGroup pointPreimage
 have hp : pointPreimage.map projection = pointParabolicSL :=
  map_comap_eq_self_of_surjective SemidirectProduct.rightHom_surjective _
 rw [hp,MarkedProduct.pointParabolic_core] at hm
 rw [← hm,comap_map_eq,sup_eq_left.mpr hkcore]

/-- U is identified with the actual embedded core, not just a subgroup of the right order. -/
theorem U_image : U.map sylowMap = pointPreimage.pCoreIn 2 := by
 rw [pointPreimage_core]
 ext g
 constructor
 · rintro ⟨x,hx,rfl⟩
   change MarkedAutomorphisms.pointCorePred (sylowElement x).right
   exact ⟨rfl,rfl,rfl,rfl,hx,rfl,rfl⟩
 · intro hg
   change MarkedAutomorphisms.pointCorePred g.right at hg
   have hs : g ∈ standardSylow := (mem_borelSL_iff _).mpr ⟨hg.2.1,hg.2.2.1,hg.2.2.2.2.2.1⟩
   exact ⟨recover g,hg.2.2.2.2.1,sylowMap_recover g hs⟩

open scoped commutatorElement

private def pointCubic : Block := SemidirectProduct.inr MarkedAutomorphisms.cubic

private theorem pointCubic_comm_row : ⁅pointCubic,rowLift⁆ = sylowMap (bit 0) := by
 apply SemidirectProduct.ext
 · apply Multiplicative.toAdd.injective; decide +kernel
 · apply Subtype.ext; decide +kernel

private theorem pointCubic_comm_bit0 : ⁅pointCubic,sylowMap (bit 0)⁆ = rowLift * sylowMap (bit 0) := by
 apply SemidirectProduct.ext
 · apply Multiplicative.toAdd.injective; decide +kernel
 · apply Subtype.ext; decide +kernel

private theorem pointCubic_comm_column : ⁅pointCubic,columnLift⁆ = sylowMap (bit 3) := by
 apply SemidirectProduct.ext
 · apply Multiplicative.toAdd.injective; decide +kernel
 · apply Subtype.ext; decide +kernel

private theorem pointCubic_comm_bit3 : ⁅pointCubic,sylowMap (bit 3)⁆ = columnLift * sylowMap (bit 3) := by
 apply SemidirectProduct.ext
 · apply Multiplicative.toAdd.injective; decide +kernel
 · apply Subtype.ext; decide +kernel

private theorem column_comm_bit0 : ⁅columnLift,sylowMap (bit 0)⁆ = sylowMap (bit 1) := by
 apply SemidirectProduct.ext
 · apply Multiplicative.toAdd.injective; decide +kernel
 · apply Subtype.ext; decide +kernel

/-- The source L₁ is the two-residual of the point stabilizer. Its core
absorption follows from actual cubic commutators on the five root coordinates. -/
theorem point_core_le_residual :
 pointPreimage.pCoreIn 2 ≤ (pResidual 2 pointPreimage).map pointPreimage.subtype := by
 let R := (pResidual 2 pointPreimage).map pointPreimage.subtype
 have hcP : pointCubic ∈ pointPreimage :=
  MarkedAutomorphisms.pointA_le MarkedAutomorphisms.cubic_mem
 have hc3 : pointCubic^3=1 := by
  change (SemidirectProduct.inr MarkedAutomorphisms.cubic : Block)^3=1
  rw [← map_pow,MarkedAutomorphisms.cubic_cube,map_one]
 have hc : pointCubic ∈ R := by
  let c : pointPreimage := ⟨pointCubic,hcP⟩
  have h3 : c^3=1 := Subtype.ext hc3
  exact ⟨c,mem_pResidual_of_orderOf_coprime
   (Nat.Coprime.of_dvd_right (orderOf_dvd_of_pow_eq_one h3) (by decide)),rfl⟩
 have hcomm (g : Block) (hg : g ∈ pointPreimage) : ⁅pointCubic,g⁆ ∈ R := by
  have hn := le_normalizer_iff.mp (le_normalizer_embedded_pResidual 2 pointPreimage)
   g hg pointCubic⁻¹ (R.inv_mem hc)
  simpa only [commutatorElement_def,mul_assoc] using R.mul_mem hc hn
 have hs : standardSylow ≤ pointPreimage := comap_mono inf_le_left
 have hrP : rowLift ∈ pointPreimage := hs (sylowMap_row ▸ sylowMap_mem r)
 have hqP : columnLift ∈ pointPreimage := hs (sylowMap_column ▸ sylowMap_mem q)
 have hb0 : sylowMap (bit 0) ∈ R := pointCubic_comm_row ▸ hcomm _ hrP
 have hb3 : sylowMap (bit 3) ∈ R := pointCubic_comm_column ▸ hcomm _ hqP
 have hr : rowLift ∈ R := by
  have hh := hcomm (sylowMap (bit 0)) (hs (sylowMap_mem _))
  rw [pointCubic_comm_bit0] at hh
  simpa only [mul_inv_cancel_right] using R.mul_mem hh (R.inv_mem hb0)
 have hq : columnLift ∈ R := by
  have hh := hcomm (sylowMap (bit 3)) (hs (sylowMap_mem _))
  rw [pointCubic_comm_bit3] at hh
  simpa only [mul_inv_cancel_right] using R.mul_mem hh (R.inv_mem hb3)
 have hb1 : sylowMap (bit 1) ∈ R := by
  rw [← column_comm_bit0,commutatorElement_def]
  exact R.mul_mem (R.mul_mem (R.mul_mem hq hb0) (R.inv_mem hq)) (R.inv_mem hb0)
 rw [← U_image]
 rintro _ ⟨x,hx,rfl⟩
 have hmx : sylowMap (middle (Multiplicative.ofAdd
    ![x.x13,x.x14+x.x13*x.x34,x.x23,x.x24+x.x23*x.x34])) ∈ R := by
  rw [middle_eq_bits]
  simp only [map_mul,map_pow]
  change sylowMap (bit 0)^x.x13.val * sylowMap (bit 1)^(x.x14+x.x13*x.x34).val *
   sylowMap (bit 2)^x.x23.val * sylowMap (bit 3)^(x.x24+x.x23*x.x34).val ∈ R
  change x.x23=0 at hx
  rw [hx]
  simp only [ZMod.val_zero,pow_zero,mul_one]
  exact R.mul_mem (R.mul_mem (R.pow_mem hb0 _) (R.pow_mem hb1 _)) (R.pow_mem hb3 _)
 rw [normal_form x,map_mul,map_mul,map_pow,map_pow,sylowMap_row,sylowMap_column]
 exact R.mul_mem (R.mul_mem hmx (R.pow_mem hr _)) (R.pow_mem hq _)

/-- In particular the intrinsic O₂(L₁), embedded in the block, is precisely k(U). -/
theorem U_image_residual_core :
 U.map sylowMap = ((pResidual 2 pointPreimage).map pointPreimage.subtype).pCoreIn 2 := by
 rw [pCoreIn_embedded_pResidual_eq_of_core_le 2 pointPreimage point_core_le_residual,U_image]

end Matrix.PSL3Two.SplitParabolic
