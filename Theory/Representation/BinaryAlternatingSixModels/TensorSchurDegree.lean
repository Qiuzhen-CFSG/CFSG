module

public import Theory.Representation.BinaryAlternatingSixModels.TensorIrreducibility
public import Theory.Representation.EndFieldRep

/-!
# The Schur degree of the binary A₆ tensor

A nonzero vector fixed by the literal Sylow two-subgroup is cyclic, since the
binary tensor is simple. Evaluation at that vector embeds its endomorphism
field into the common fixed space of two published matrices. The existing
checked projection certificate recovers this fixed vector from two binary
coordinates, so the endomorphism field has degree at most two.
Together with Jacobson density this excludes the tensor from four-dimensional
actions over any characteristic-two coefficient field.
Source: Aschbacher–Smith G.5.1, printed pp.342–343.
-/
open Representation Module
open scoped MonoidAlgebra
open BinaryAlternatingSix
open BinaryAlternatingSix.TensorIrreducibility.Native
open BinaryAlternatingSix.TensorIrreducibility.Certificate
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
namespace BinaryAlternatingSix.ScalarFour
private def σ : Representation (ZMod 2) Theory.SpecificGroups.SymmetricSix.A6 TensorModule := alternatingTensor
/-- The actual binary tensor has Schur degree at most two. -/
theorem alternatingTensor_endField_finrank_le_two : Module.finrank (ZMod 2)
 (Module.End (ZMod 2)[Theory.SpecificGroups.SymmetricSix.A6]
   (Representation.asModule alternatingTensor)) ≤ 2 := by
 change Module.finrank (ZMod 2)
   (Module.End (ZMod 2)[Theory.SpecificGroups.SymmetricSix.A6] σ.asModule) ≤ 2
 classical
 let : σ.IsIrreducible := alternatingTensor_irreducible
 let : Nontrivial TensorModule := Subrepresentation.irreducible_module_nontrivial σ
 obtain ⟨v,hv,hfix⟩ := BinaryLinearThree.IrreducibleCatalogue.binary_pGroup_fixed_vector
   (σ.comp Theory.SpecificGroups.SymmetricSix.a6Borel.subtype)
   (IsPGroup.of_card (show Nat.card Theory.SpecificGroups.SymmetricSix.a6Borel = 2^3 from
     Theory.SpecificGroups.SymmetricSix.a6Borel_order))
 let E := Module.End (ZMod 2)[Theory.SpecificGroups.SymmetricSix.A6] σ.asModule
 let j : E →ₗ[ZMod 2] (Fin 2 → ZMod 2) := {
   toFun f := ![coords (σ.asModuleEquiv (f (σ.asModuleEquiv.symm v))) 3,
     coords (σ.asModuleEquiv (f (σ.asModuleEquiv.symm v))) 15]
   map_add' f g := by
     ext k
     fin_cases k <;>
       change coords (σ.asModuleEquiv (f (σ.asModuleEquiv.symm v) + g (σ.asModuleEquiv.symm v))) _ = _
     all_goals rw [map_add,map_add]; rfl
   map_smul' c f := by
     ext k
     fin_cases k <;>
       change coords (σ.asModuleEquiv (c • f (σ.asModuleEquiv.symm v))) _ = _
     all_goals rw [map_smul,map_smul]; rfl }
 have hj : Function.Injective j := by
   intro f g hfg
   have hz : j (f-g) = 0 := by rw [map_sub,hfg,sub_self]
   let z := σ.asModuleEquiv ((f-g) (σ.asModuleEquiv.symm v))
   let q : σ.IntertwiningMap σ :=
     (Representation.IntertwiningMap.equivLinearMapAsModule σ σ).symm (f-g)
   have hcomm (h : Theory.SpecificGroups.SymmetricSix.A6) :
       σ h z = σ.asModuleEquiv
         ((f-g) (σ.asModuleEquiv.symm (σ h v))) := by
     exact (LinearMap.congr_fun (q.isIntertwining' h) v).symm
   have hzr : R.mulVec (coords z) = coords z := by
     rw [show R = matrix 0 from rfl, ←matrix_action 0]
     change coords (σ r z) = coords z
     rw [hcomm,show σ r v = v from hfix ⟨r,r_mem⟩]
   have hzs : S.mulVec (coords z) = coords z := by
     rw [show S = matrix 1 from rfl, ←matrix_action 1]
     change coords (σ s z) = coords z
     rw [hcomm,show σ s v = v from hfix ⟨s,s_mem⟩]
   have he := congrArg (fun M : TensorIrreducibility.Certificate.Mat => M.mulVec (coords z)) fixed_certificate
   have ha : coords z + coords z = 0 := by ext k; exact CharTwo.add_self_eq_zero _
   simp only [Matrix.add_mulVec, ← Matrix.mulVec_mulVec, Matrix.one_mulVec,
     hzr,hzs,ha,Matrix.mulVec_zero,add_zero] at he
   have h3 : coords z 3 = 0 := congrFun hz 0
   have h15 : coords z 15 = 0 := congrFun hz 1
   rw [projection_apply,h3,h15,zero_smul,zero_add] at he
   have hzz : z = 0 := coords.injective (by simpa using he.symm)
   have hf : (f-g) = 0 := by
     rcases IsIrreducible.injective_or_eq_zero q with hinj | hq
     · exfalso
       apply hv
       apply hinj
       have hh : q v = 0 := by exact hzz
       simpa only [map_zero] using hh
     · have hh := congrArg (Representation.IntertwiningMap.equivLinearMapAsModule σ σ) hq
       simpa only [q,LinearEquiv.apply_symm_apply,map_zero] using hh
   exact sub_eq_zero.mp hf
 have hd := LinearMap.finrank_le_finrank_of_injective hj
 simpa using hd

end BinaryAlternatingSix.ScalarFour
