module
public import Theory.SpecificGroups.BinaryFiveAffine.Marking
public import Theory.GroupTheory.PResidual.PGroupFactor
public import Theory.SpecificGroups.SymmetricFour.ResidualFactorization
/-!
# Residual and fixed four-group of the marked pair centralizer

The existing centralizer splitting is D₈ × S₄. Its two-residual projects
isomorphically to A₄ in the S₄ factor. The natural binary module vectors
fixed by that residual are exactly the zero vector, the marked pair vector,
and the two weight-four vectors supported on one of the first two letters
and all three remaining letters.

Source: Aschbacher--Smith 2.4.29, printed p.545; the same finite model is
used in 13.9.10, printed p.973.
-/
public section
namespace BinaryFiveAffine
open Subgroup
private theorem dihedral_two : IsPGroup 2 (DihedralGroup 4) := by
  apply (IsPGroup.iff_card).mpr
  exact ⟨3,by norm_num [Nat.card_eq_fintype_card,DihedralGroup.card]⟩
noncomputable def residualEquiv : pResidual 2 centralizer ≃* alternatingGroup (Fin 4) :=
  (pResidualEquivOfPGroupFactor 2 productEquiv.symm dihedral_two).trans
    (MulEquiv.subgroupCongr Theory.SpecificGroups.SymmetricFourResidual.residual_eq)
theorem residualEquiv_val (x : pResidual 2 centralizer) :
    symmetricEmbedding (residualEquiv x).val = x.val.val := by
  have hf := fst_eq_one_of_mem_pResidual 2 productEquiv.symm dihedral_two x.property
  have hh := productEquiv.apply_symm_apply x.val
  have hv := congrArg Subtype.val hh
  rw [productEquiv_val,hf,map_one,one_mul] at hv
  have he : (residualEquiv x).val=(productEquiv.symm x.val).2 :=
    pResidualEquivOfPGroupFactor_apply 2 productEquiv.symm dihedral_two x
  rw [he]
  exact hv

def residualImage : Subgroup W := (pResidual 2 centralizer).map centralizer.subtype

theorem residualImage_def : residualImage=(pResidual 2 centralizer).map centralizer.subtype := by rfl

theorem residualImage_eq : residualImage=(alternatingGroup (Fin 4)).map symmetricEmbedding := by
  apply le_antisymm
  · rintro _ ⟨x,hx,rfl⟩
    exact ⟨(residualEquiv ⟨x,hx⟩).val,(residualEquiv ⟨x,hx⟩).property,residualEquiv_val ⟨x,hx⟩⟩
  · rintro _ ⟨g,hg,rfl⟩
    let x := residualEquiv.symm ⟨g,hg⟩
    refine ⟨x.val,x.property,?_⟩
    have hh := residualEquiv_val x
    rw [residualEquiv.apply_symm_apply] at hh
    exact hh.symm

def secondSingular : V := .ofAdd ⟨![0,1,1,1,1],by decide +kernel⟩
def firstSingular : V := .ofAdd ⟨![1,0,1,1,1],by decide +kernel⟩
def centralSingular : V := .ofAdd ⟨![1,1,1,1,0],by decide +kernel⟩

theorem centralSingular_value : centralSingular =
    (Multiplicative.ofAdd ⟨![1,1,1,1,0],by decide +kernel⟩ : V) := by rfl

theorem residual_fixed_vectors (v : V) :
    SemidirectProduct.inl v ∈ Subgroup.centralizer (residualImage:Set W) ↔
      v=1 ∨ v=pair01 ∨ v=firstSingular ∨ v=secondSingular := by
  rw [residualImage_eq]
  constructor
  · intro hv
    have hc : ∀ g : alternatingGroup (Fin 4),
        action (symmetricEmbedding g.val).right v=v := by
      intro g
      have hh := hv (symmetricEmbedding g.val) (mem_map_of_mem _ g.property)
      have hl := congrArg SemidirectProduct.left hh
      change (symmetricEmbedding g.val).left * action (symmetricEmbedding g.val).right v =
        v * (symmetricEmbedding g.val).left at hl
      rwa [mul_comm v,mul_left_cancel_iff] at hl
    have hcalc : ∀ v : V,
        (∀ g : alternatingGroup (Fin 4), action (symmetricEmbedding g.val).right v=v) →
        v=1 ∨ v=pair01 ∨ v=firstSingular ∨ v=secondSingular := by decide +kernel
    exact hcalc v hc
  · intro hv
    have hcalc : ∀ v : V,
        (v=1 ∨ v=pair01 ∨ v=firstSingular ∨ v=secondSingular) →
        ∀ g : alternatingGroup (Fin 4), action (symmetricEmbedding g.val).right v=v := by decide +kernel
    rintro a ⟨g,hg,rfl⟩
    apply SemidirectProduct.ext
    · change (symmetricEmbedding g).left * action (symmetricEmbedding g).right v =
        v * (symmetricEmbedding g).left
      rw [hcalc v hv ⟨g,hg⟩,mul_comm]
    · simp
abbrev fixedFour : Subgroup W := vectorGroup ⊓ Subgroup.centralizer (residualImage:Set W)

theorem fixedFour_members (w : W) : w∈fixedFour ↔
    w=1 ∨ w=t ∨ w=SemidirectProduct.inl firstSingular ∨ w=SemidirectProduct.inl secondSingular := by
  constructor
  · rintro ⟨⟨v,rfl⟩,hv⟩
    rcases (residual_fixed_vectors v).mp hv with rfl|rfl|rfl|rfl
    · exact Or.inl (map_one _)
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr (Or.inl rfl))
    · exact Or.inr (Or.inr (Or.inr rfl))
  · intro h
    rcases h with rfl|rfl|rfl|rfl
    · exact fixedFour.one_mem
    · exact ⟨⟨pair01,rfl⟩,(residual_fixed_vectors _).mpr (Or.inr (Or.inl rfl))⟩
    · exact ⟨⟨firstSingular,rfl⟩,(residual_fixed_vectors _).mpr (Or.inr (Or.inr (Or.inl rfl)))⟩
    · exact ⟨⟨secondSingular,rfl⟩,(residual_fixed_vectors _).mpr (Or.inr (Or.inr (Or.inr rfl)))⟩

theorem fixedFour_card : Nat.card fixedFour=4 := by
  classical
  let vs : Fin 4 → W := ![1,t,SemidirectProduct.inl firstSingular,SemidirectProduct.inl secondSingular]
  have hm (i : Fin 4) : vs i∈fixedFour := by
    rw [fixedFour_members]
    fin_cases i <;> simp [vs]
  let f : Fin 4 → fixedFour := fun i=>⟨vs i,hm i⟩
  have hinj : Function.Injective f := by
    have hv : Function.Injective vs := by decide +kernel
    intro i j hij
    exact hv (congrArg Subtype.val hij)
  have hsurj : Function.Surjective f := by
    intro w
    rcases (fixedFour_members w).mp w.property with h|h|h|h
    · exact ⟨0,Subtype.ext h.symm⟩
    · exact ⟨1,Subtype.ext h.symm⟩
    · exact ⟨2,Subtype.ext h.symm⟩
    · exact ⟨3,Subtype.ext h.symm⟩
  exact (Nat.card_congr (Equiv.ofBijective f ⟨hinj,hsurj⟩)).symm.trans (by simp)

theorem fixedFour_singular_marks :
    firstSingular≠1 ∧ secondSingular≠1 ∧ firstSingular≠pair01 ∧
      secondSingular≠pair01 ∧ firstSingular≠secondSingular ∧
      firstSingular*secondSingular=pair01 := by decide +kernel

theorem firstSingular_conjugate :
    ∃ g : alternatingGroup (Fin 5),
      SemidirectProduct.inr (g.val) * SemidirectProduct.inl centralSingular *
        (SemidirectProduct.inr (g.val))⁻¹ = (SemidirectProduct.inl firstSingular : W) := by
  refine ⟨⟨Equiv.swap 1 4 * Equiv.swap 0 2, ?_⟩, ?_⟩
  · rw [Equiv.Perm.mem_alternatingGroup]
    decide +kernel
  · apply SemidirectProduct.ext <;> decide +kernel

theorem secondSingular_conjugate :
    ∃ g : alternatingGroup (Fin 5),
      SemidirectProduct.inr (g.val) * SemidirectProduct.inl centralSingular *
        (SemidirectProduct.inr (g.val))⁻¹ = (SemidirectProduct.inl secondSingular : W) := by
  refine ⟨⟨Equiv.swap 0 4 * Equiv.swap 1 2, ?_⟩, ?_⟩
  · rw [Equiv.Perm.mem_alternatingGroup]
    decide +kernel
  · apply SemidirectProduct.ext <;> decide +kernel

end BinaryFiveAffine
