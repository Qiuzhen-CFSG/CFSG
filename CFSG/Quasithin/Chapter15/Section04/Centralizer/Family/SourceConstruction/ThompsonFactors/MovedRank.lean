module
public import CFSG.Quasithin.Chapter15.Section04.Centralizer.Family.SourceConstruction.ThompsonFactors.ModuleRank
public import Theory.ElementaryAbelian.GeneratorRank
public import Theory.ElementaryAbelian.AbelianNormalClosure
public import Mathlib.GroupTheory.Schreier

/-!
# Generator rank of the original moved subgroup

The binary span of the actual conjugation displacements is the original
subgroup commutator, viewed additively. Its order is therefore the binary
dimension power. The elementary abelian generator bounds turn this into
Group.rank [V,X] = 2s whenever the literal star image of X is the selected
cubic product. The final theorem preserves this equality under the actual
ambient subgroup inclusion.

Source: Aschbacher–Smith 15.4.12(3), printed pp.1160–1161.
-/

@[expose] public noncomputable section
open Subgroup Stellmacher Representation Representation.BinaryOffender
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter15.Section04.FamilySource.ThompsonFactors
open Chapter1.RadicalNormalizers.ThompsonSource
local notation "sourceClosure" => Chapter1.RadicalNormalizers.ThompsonSource.closure
variable {H : Type*} [Group H] {S : Sylow 2 H}
  [IsElementaryAbelian 2 (sourceClosure S)]

def commutatorSpace (X : Subgroup H) : Submodule (ZMod 2) (Additive (sourceClosure S)) :=
  AddSubgroup.toZModSubmodule 2 ((⁅sourceClosure S,X⁆ : Subgroup H).subgroupOf (sourceClosure S)).toAddSubgroup

theorem vector_commutator (d : Exceptional S) (v : sourceClosure S) (h : H) :
    Additive.ofMul (⟨⁅(v : H),h⁆, (commutator_le_left (sourceClosure S) ⊤)
      (commutator_mem_commutator v.property (mem_top h))⟩ : sourceClosure S) =
      Additive.ofMul v - d.representation (starMap (sourceClosure S) h) (Additive.ofMul v) := by
  apply Additive.toMul.injective
  rw [toMul_sub,div_eq_mul_inv]
  apply Subtype.ext
  change ⁅(v : H),h⁆ = (v : H)*(((d.representation (starMap (sourceClosure S) h)
    (Additive.ofMul v)).toMul : H))⁻¹
  rw [d.conjugation]
  simp only [commutatorElement_def,mul_inv_rev,inv_inv,mul_assoc]

theorem commutatorSpace_eq (d : Exceptional S) (X : Subgroup H) :
    commutatorSpace (S := S) X =
      subspaceCommutator d.representation ⊤ (X.map (starMap (sourceClosure S))) := by
  let W := subspaceCommutator d.representation ⊤ (X.map (starMap (sourceClosure S)))
  let C := W.toAddSubgroup.toSubgroup'.map (sourceClosure S).subtype
  have hcV : ⁅sourceClosure S,X⁆ ≤ sourceClosure S := commutator_le_left _ _
  have hcomm : ⁅sourceClosure S,X⁆ ≤ C := by
    apply commutator_le.mpr
    intro v hv x hx
    refine ⟨⟨⁅v,x⁆,hcV (commutator_mem_commutator hv hx)⟩,?_,rfl⟩
    change Additive.ofMul (⟨⁅v,x⁆,_⟩ : sourceClosure S) ∈ W
    rw [vector_commutator d ⟨v,hv⟩ x]
    apply W.neg_mem_iff.mp
    rw [neg_sub]
    exact Submodule.subset_span ⟨_,mem_map_of_mem (starMap (sourceClosure S)) hx,
      Additive.ofMul ⟨v,hv⟩,Submodule.mem_top,rfl⟩
  apply le_antisymm
  · intro v hv
    change (v.toMul : H) ∈ ⁅sourceClosure S,X⁆ at hv
    obtain ⟨u,hu,he⟩ := hcomm hv
    have he' : u = v.toMul := Subtype.ext he
    change Additive.ofMul u ∈ W at hu
    simpa only [he',ofMul_toMul] using hu
  · apply Submodule.span_le.mpr
    rintro _ ⟨a,⟨x,hx,rfl⟩,v,_,rfl⟩
    apply (commutatorSpace (S := S) X).neg_mem_iff.mp
    rw [neg_sub]
    have he := vector_commutator d v.toMul x
    simp only [ofMul_toMul] at he
    rw [← he]
    exact commutator_mem_commutator v.toMul.property hx

theorem commutatorSpace_card (X : Subgroup H) :
    Nat.card (commutatorSpace (S := S) X) = Nat.card (⁅sourceClosure S,X⁆ : Subgroup H) := by
  let e : commutatorSpace (S := S) X ≃ ((⁅sourceClosure S,X⁆ : Subgroup H).subgroupOf (sourceClosure S)) :=
    { toFun := fun v => ⟨v.val.toMul,v.property⟩
      invFun := fun v => ⟨Additive.ofMul v.val,v.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  exact (Nat.card_congr e).trans (Nat.card_congr
    (subgroupOfEquivOfLe (commutator_le_left (sourceClosure S) X)).toEquiv)

variable [Finite H]

theorem actual_moved_card (d : Exceptional S) (I : Finset (Fin d.count))
    (hI : I.card = 1 ∨ I.card = 2) (X : Subgroup H)
    (hX : X.map (starMap (sourceClosure S)) = cubicProduct d I) :
    Nat.card (⁅sourceClosure S,X⁆ : Subgroup H) = 2^(2*I.card) := by
  rw [← commutatorSpace_card X,commutatorSpace_eq d X,hX,
    Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod,cubicProduct_moved_finrank d I hI]

theorem actual_moved_rank (d : Exceptional S) (I : Finset (Fin d.count))
    (hI : I.card = 1 ∨ I.card = 2) (X : Subgroup H)
    (hX : X.map (starMap (sourceClosure S)) = cubicProduct d I) :
    Group.rank (⁅sourceClosure S,X⁆ : Subgroup H) = 2*I.card := by
  have hle : ⁅sourceClosure S,X⁆ ≤ sourceClosure S := commutator_le_left _ _
  let : IsElementaryAbelian 2 (⁅sourceClosure S,X⁆ : Subgroup H) := IsElementaryAbelian.of_le hle
  have hc := actual_moved_card d I hI X hX
  apply le_antisymm (IsElementaryAbelian.rank_le_of_card_le (p := 2) _ hc.le)
  apply (Nat.pow_dvd_pow_iff_le_right (by decide : 1 < 2)).mp
  rw [← hc]
  exact card_dvd_exponent_pow_rank' _
    (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp (IsElementaryAbelian.exponent_dvd_p 2 (⁅sourceClosure S,X⁆ : Subgroup H)))

theorem actual_moved_rank_map (d : Exceptional S) (I : Finset (Fin d.count))
    (hI : I.card = 1 ∨ I.card = 2) (X : Subgroup H)
    (hX : X.map (starMap (sourceClosure S)) = cubicProduct d I)
    {G : Type*} [Group G] [Finite G] (f : H →* G) (hf : Function.Injective f) :
    Group.rank (⁅(sourceClosure S).map f,X.map f⁆ : Subgroup G) =
      2*I.card := by
  rw [← map_commutator,← Group.rank_congr (Subgroup.equivMapOfInjective _ f hf)]
  exact actual_moved_rank d I hI X hX

end CFSG.Quasithin.Chapter15.Section04.FamilySource.ThompsonFactors
