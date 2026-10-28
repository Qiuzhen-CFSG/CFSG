module
public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Recognition.NormalReduction.LocalRestrictions
public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Core.ResidualGeneration.Action.Centralizer
public import Theory.Representation.CyclicFixedRank

/-!
# The actual commutator image is the source linear displacement

Conjugation on U/Z identifies the image of the ambient commutator [U,A]
with the binary span of displacements by A*. For cyclic A*, this span is
the image of its generator minus the identity. Thus the order-four
commutator image in source 53 gives precisely the rank-two input of source57.

Source: Aschbacher–Smith, 15.3.53 and 15.3.57, printed pp.1146,1148.
-/

public section
open Subgroup Representation Representation.BinaryOffender
open scoped commutatorElement IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Source50
open Recognition Core.ResidualGeneration
variable {G : Type*} [Group G] (Z ZS : Subgroup G)
  [(Z.subgroupOf (closureU Z ZS)).Normal]
  [IsElementaryAbelian 2 (VectorQuotient Z ZS)]
  (hk : (quotientAction Z ZS).ker = pCore 2 (centralizerH Z))

private theorem linear_displacement_mk (a : centralizerH Z) (u : closureU Z ZS) :
    actorRepresentation Z ZS hk (QuotientGroup.mk' _ a)
        (Additive.ofMul (QuotientGroup.mk' _ u)) -
      Additive.ofMul (QuotientGroup.mk' (Z.subgroupOf (closureU Z ZS)) u) =
      Additive.ofMul (QuotientGroup.mk' _ (closureCommutator a u)) := by
  apply Additive.toMul.injective
  rw [toMul_sub,actorRepresentation_mk]
  simpa only [div_eq_mul_inv,toMul_ofMul] using (quotient_closureCommutator a u).symm

 theorem commutator_subspace_eq (A : Subgroup G) (hAH : A ≤ centralizerH Z) :
    subspaceCommutator (actorRepresentation Z ZS hk) ⊤ (Recognition.actorImage Z A) =
      LocalRestrictions.vectorSubspace Z ZS ⁅closureU Z ZS,A⁆ := by
  let U := closureU Z ZS
  let q := QuotientGroup.mk' (Z.subgroupOf U)
  let W := subspaceCommutator (actorRepresentation Z ZS hk) ⊤ (Recognition.actorImage Z A)
  let D : Subgroup (VectorQuotient Z ZS) := W.toAddSubgroup.toSubgroup'
  let C : Subgroup G := (D.comap q).map U.subtype
  have hcU : ⁅A,U⁆ ≤ U :=
    le_normalizer_iff_commutator_le_right.mp (hAH.trans (H_normalizes_closureU Z ZS))
  have hcomm : ⁅A,U⁆ ≤ C := by
    apply commutator_le.mpr
    intro a ha u hu
    let aH : centralizerH Z := ⟨a,hAH ha⟩
    let uU : U := ⟨u,hu⟩
    refine ⟨closureCommutator aH uU,?_,rfl⟩
    change Additive.ofMul (q (closureCommutator aH uU)) ∈ W
    rw [← linear_displacement_mk Z ZS hk aH uU]
    exact Submodule.subset_span ⟨QuotientGroup.mk' _ aH,
      mem_map_of_mem _ ha,Additive.ofMul (q uU),Submodule.mem_top,rfl⟩
  rw [commutator_comm] at hcomm
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨b,⟨a,ha,rfl⟩,w,_,rfl⟩
    obtain ⟨u,hu⟩ := QuotientGroup.mk'_surjective (Z.subgroupOf U) w.toMul
    have hw : w=Additive.ofMul (q u) := congrArg Additive.ofMul hu.symm
    rw [hw,linear_displacement_mk Z ZS hk]
    change q (closureCommutator a u) ∈ vectorImage Z ZS ⁅U,A⁆
    refine mem_map_of_mem _ ?_
    change ⁅(a:G),(u:G)⁆ ∈ ⁅U,A⁆
    rw [commutator_comm]
    exact commutator_mem_commutator ha u.property
  · intro w hw
    change w.toMul ∈ vectorImage Z ZS ⁅U,A⁆ at hw
    obtain ⟨u,hu,he⟩ := hw
    obtain ⟨c,hc,hec⟩ := hcomm hu
    have he' : c=u := Subtype.ext hec
    have hq : q u ∈ D := he' ▸ hc
    change Additive.ofMul (q u) ∈ W at hq
    change q u=w.toMul at he
    rw [he,ofMul_toMul] at hq
    exact hq

 theorem displacement_eq_vectorSubspace (A : Subgroup G) (hAH : A ≤ centralizerH Z)
    (v : ActorQuotient Z) (hv : zpowers v=Recognition.actorImage Z A) :
    LinearMap.range (actorRepresentation Z ZS hk v-LinearMap.id) =
      LocalRestrictions.vectorSubspace Z ZS ⁅closureU Z ZS,A⁆ := by
  rw [← Representation.CyclicFixedRank.commutator_eq_range, hv]
  exact commutator_subspace_eq Z ZS hk A hAH

 theorem vectorSubspace_card (A : Subgroup G) :
    Nat.card (LocalRestrictions.vectorSubspace Z ZS A) = Nat.card (vectorImage Z ZS A) := by
  exact Nat.card_congr {
    toFun := fun x => ⟨x.val.toMul,x.property⟩
    invFun := fun x => ⟨Additive.ofMul x.val,x.property⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }

 theorem displacement_rank_of_card [Finite G] (A : Subgroup G)
    (hAH : A ≤ centralizerH Z) (v : ActorQuotient Z)
    (hv : zpowers v=Recognition.actorImage Z A)
    (hc : Nat.card (vectorImage Z ZS ⁅closureU Z ZS,A⁆)=4) :
    Module.finrank (ZMod 2)
      (LinearMap.range (actorRepresentation Z ZS hk v-LinearMap.id))=2 := by
  rw [displacement_eq_vectorSubspace Z ZS hk A hAH v hv]
  have hp := Module.natCard_eq_pow_finrank (K := ZMod 2)
    (V := LocalRestrictions.vectorSubspace Z ZS ⁅closureU Z ZS,A⁆)
  rw [Nat.card_zmod,vectorSubspace_card,hc] at hp
  exact Nat.pow_right_injective (by decide : 1 < 2) hp.symm

end CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Source50
