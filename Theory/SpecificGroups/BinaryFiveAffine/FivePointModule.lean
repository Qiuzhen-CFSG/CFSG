module
public import Theory.SpecificGroups.BinaryFiveAffine.Basic
public import Theory.ElementaryAbelian.VectorSpace
/-!
# Five binary generators with the full-product relation

Five points generating an elementary sixteen-group with only the full-product
relation identify that group with the even binary permutation core. The
identification retains the marked pair product and is equivariant for the
literal permutation of the five generators. This is the natural module
comparison used by Aschbacher–Smith 13.9.9–10.
-/

public section
noncomputable section
open scoped IsMulCommutative
namespace BinaryFiveAffine
variable {E:Type*} [Group E] [IsElementaryAbelian 2 E]

def evaluate (v:Fin 5→E) : (Fin 5→ZMod 2)→ₗ[ZMod 2] Additive E where
  toFun a := ∑i,a i • Additive.ofMul (v i)
  map_add' a b := by simp [add_smul,Finset.sum_add_distrib]
  map_smul' c a := by simp [Finset.smul_sum,smul_smul]

def vectorMap (v:Fin 5→E) : V→*E :=
  ((evaluate v).comp (BinaryPermutation.core (Fin 5)).subtype).toAddMonoidHom.toMultiplicativeLeft

theorem vectorMap_apply (v:Fin 5→E) (a:V) :
    vectorMap v a = ∏i,v i^(a.toAdd.val i).val := by
  change (∑i,a.toAdd.val i • Additive.ofMul (v i)).toMul = _
  rw [toMul_sum]
  apply Finset.prod_congr rfl
  intro i _
  generalize a.toAdd.val i = b
  rfl

/-- The original permutation of the five generators gives exact equivariance. -/
theorem vectorMap_equivariant (v:Fin 5→E) (α:MulAut E) (σ:S)
    (h:∀i,α (v i)=v (σ i)) (a:V) :
    vectorMap v (action σ a)=α (vectorMap v a) := by
  rw [vectorMap_apply,vectorMap_apply,map_prod]
  simp only [map_pow,h,action_apply]
  have hinv (i:Fin 5) : σ⁻¹ (σ i)=i := σ.symm_apply_apply i
  simpa only [hinv] using
    (Equiv.prod_comp σ (fun i=>v i^(a.toAdd.val (σ⁻¹ i)).val)).symm

private theorem vectorMap_eq_one_iff (v:Fin 5→E)
    (hv:∀a:Fin 5→Fin 2,
      v 0^(a 0).val*v 1^(a 1).val*v 2^(a 2).val*v 3^(a 3).val*v 4^(a 4).val=1 ↔ a=0 ∨ a=1)
    (a:V) : vectorMap v a=1 ↔ a=1 := by
  rw [vectorMap_apply]
  let b:Fin 5→Fin 2 := fun i=>⟨(a.toAdd.val i).val,ZMod.val_lt _⟩
  have he : (∏i,v i^(a.toAdd.val i).val)=
      v 0^(b 0).val*v 1^(b 1).val*v 2^(b 2).val*v 3^(b 3).val*v 4^(b 4).val := by
    simp [Fin.prod_univ_succ,b,mul_assoc]
  rw [he,hv]
  constructor
  · rintro (h|h)
    · apply Subtype.ext
      funext i
      have hi := congrFun h i
      have hi' : (a.toAdd.val i).val=0 := congrArg Fin.val hi
      exact (ZMod.val_eq_zero _).mp hi'
    · have hi (i:Fin 5) : a.toAdd.val i=1 := by
        have he' := congrArg Fin.val (congrFun h i)
        exact ZMod.val_injective 2 he'
      have hh := a.toAdd.property
      rw [BinaryPermutation.mem_core] at hh
      simp [hi] at hh
      exact False.elim ((by decide : (5:ZMod 2)≠0) hh)
  · rintro rfl
    exact Or.inl rfl

/-- The five marked points identify the literal even core with E. -/
def fivePointEquiv [Finite E] (v:Fin 5→E) (hE:Nat.card E=16)
    (hv:∀a:Fin 5→Fin 2,
      v 0^(a 0).val*v 1^(a 1).val*v 2^(a 2).val*v 3^(a 3).val*v 4^(a 4).val=1 ↔ a=0 ∨ a=1) :
    V≃*E := MulEquiv.ofBijective (vectorMap v) (by
  have hi : Function.Injective (vectorMap v) := (MonoidHom.ker_eq_bot_iff (vectorMap v)).mp (by
    ext a
    exact vectorMap_eq_one_iff v hv a)
  apply (Nat.bijective_iff_injective_and_card _).mpr
  refine ⟨hi,?_⟩
  rw [hE,Nat.card_eq_fintype_card]
  decide +kernel)

theorem fivePointEquiv_pair01 [Finite E] (v:Fin 5→E) (hE:Nat.card E=16)
    (hv:∀a:Fin 5→Fin 2,
      v 0^(a 0).val*v 1^(a 1).val*v 2^(a 2).val*v 3^(a 3).val*v 4^(a 4).val=1 ↔ a=0 ∨ a=1) :
    fivePointEquiv v hE hv pair01=v 0*v 1 := by
  change vectorMap v pair01=_
  rw [vectorMap_apply]
  simp [Fin.prod_univ_succ,pair01_apply,Pi.single_apply,ZMod.val_one_eq_one_mod]

/-- The identified core action is the actual action on the five generators. -/
theorem fivePointEquiv_equivariant [Finite E] (v:Fin 5→E) (hE:Nat.card E=16)
    (hv:∀a:Fin 5→Fin 2,
      v 0^(a 0).val*v 1^(a 1).val*v 2^(a 2).val*v 3^(a 3).val*v 4^(a 4).val=1 ↔ a=0 ∨ a=1)
    (α:MulAut E) (σ:S) (h:∀i,α (v i)=v (σ i)) (a:V) :
    fivePointEquiv v hE hv (action σ a)=α (fivePointEquiv v hE hv a) :=
  vectorMap_equivariant v α σ h a

end BinaryFiveAffine
