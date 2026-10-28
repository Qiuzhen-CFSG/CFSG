module
public import Theory.Representation.BinaryPermutation.FiveTensorSquare.SylowAction
public import Theory.Representation.PermutationBasisOrbits
public import Mathlib.LinearAlgebra.TensorProduct.Basis

/-!
# A permutation basis for the Sylow action on the deleted tensor square

The four core vectors eᵢ + e₄ form a basis permuted by D₈. Their tensor
products identify fixed-space dimension with the number of orbits on the
sixteen-point square. This supplies the literal representation bridge for
the deleted-square exclusion in Aschbacher--Smith D.3.7, pp.197–199.
-/

@[expose] public section
namespace BinaryPermutation.FiveTensorSquare.Small
open scoped TensorProduct

def coords : C ≃ₗ[ZMod 2] (ZMod 4 → ZMod 2) where
  toFun v i := v.val ⟨i.val,Nat.lt_trans (ZMod.val_lt _) (show 4<5 from Nat.lt_succ_self 4)⟩
  invFun f := ⟨fun i => if i.val<4 then f (i.val:ZMod 4) else ∑j,f j,
    (by
      change ∑i:Fin 5,(if i.val<4 then f (i.val:ZMod 4) else ∑j,f j)=0
      exact (by decide +kernel : ∀f:ZMod 4→ZMod 2,
        ∑i:Fin 5,(if i.val<4 then f (i.val:ZMod 4) else ∑j,f j)=0) f)⟩
  left_inv v := by
    apply Subtype.ext
    exact (by decide +kernel : ∀v:Fin 5→ZMod 2, (∑i,v i)=0 →
      (fun i:Fin 5 => if i.val<4 then
        v ⟨(i.val:ZMod 4).val,Nat.lt_trans (ZMod.val_lt _) (show 4<5 from Nat.lt_succ_self 4)⟩
        else ∑j:ZMod 4,v ⟨j.val,Nat.lt_trans (ZMod.val_lt _) (show 4<5 from Nat.lt_succ_self 4)⟩)=v)
      v.val v.property
  right_inv := by decide +kernel
  map_add' v w := rfl
  map_smul' a v := rfl

def basisVector (i : ZMod 4) : C :=
  ⟨Pi.single ⟨i.val,Nat.lt_trans (ZMod.val_lt _) (show 4<5 from Nat.lt_succ_self 4)⟩ 1 + Pi.single 4 1, by
    simp [mem_core,Finset.sum_add_distrib,show (1:ZMod 2)+1=0 from rfl]⟩

noncomputable def coreBasis : Module.Basis (ZMod 4) (ZMod 2) C := Module.Basis.ofEquivFun coords

theorem coreBasis_apply (i : ZMod 4) : coreBasis i=basisVector i := by
  rw [coreBasis,Module.Basis.coe_ofEquivFun]
  exact (by decide +kernel : ∀i:ZMod 4,coords.symm (Pi.single i 1)=basisVector i) i

theorem coreBasis_permuted (g : D8) (i : ZMod 4) :
    coreRepresentation (Fin 5) (dihedralHom g) (coreBasis i)=coreBasis (dihedralPoint g i) := by
  simp only [coreBasis_apply]
  exact (by decide +kernel : ∀g i,
    coreRepresentation (Fin 5) (dihedralHom g) (basisVector i)=basisVector (dihedralPoint g i)) g i

noncomputable def tensorBasis : Module.Basis Point (ZMod 2) V := coreBasis.tensorProduct coreBasis

theorem tensorBasis_permuted (g : P) (i : Point) :
    tensorWreathAction (embed g) (tensorBasis i)=tensorBasis (g • i) := by
  change tensorWreathAction (embed g) (tensorBasis i)=tensorBasis (point g i)
  simp only [tensorBasis,Module.Basis.tensorProduct_apply']
  rw [tensorWreathAction_tmul]
  change (if g.right=1 then _ else _)=_
  split_ifs with hg <;> simp [point,hg,embed,coreBasis_permuted]

theorem fixedSpace_finrank (A : Subgroup P) :
    Module.finrank (ZMod 2)
      (Representation.BinaryOffender.fixedSpace (tensorWreathAction.comp embed) A)=
      Nat.card (MulAction.orbitRel.Quotient A Point) := by
  apply Representation.permutedBasis_fixedSubspace_finrank_eq_orbitQuotient_card
    ((tensorWreathAction.comp embed).comp A.subtype) tensorBasis
  intro g i
  exact tensorBasis_permuted g i

end BinaryPermutation.FiveTensorSquare.Small
