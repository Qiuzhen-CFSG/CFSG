module
public import Theory.SpecificGroups.SymmetricFourWreath.InvolutionClasses.CoreOrbits

/-!
Explicit generators identify the two rank-three spans in Q and their coordinate membership. Products in the first span recover the original t and z; the other span is B intersected with Q. Source: Aschbacher–Smith 13.9.9–10, printed pp.972–973.
-/

@[expose] public section
namespace SymmetricFourWreath.InvolutionClasses
open Subgroup
private instance : Fintype P := Fintype.ofEquiv _ (RegularWreathProduct.equivProd D8 C2).symm
private instance : DecidableEq P := (RegularWreathProduct.equivProd D8 C2).injective.decidableEq
private instance (i:Fin 6) : DecidablePred (·∈gamma i) := fun x=>by
  change Decidable (coreTest x ∧ x*x=1 ∧ x≠1 ∧ x≠centralInP ∧ classIndex (sylowEmbedding x)=i)
  infer_instance

theorem gammaZeroGenerator_t : gammaZeroGenerator 0*gammaZeroGenerator 2=pair (DihedralGroup.r 2,1) := by decide +kernel

theorem gammaZeroGenerator_z : gammaZeroGenerator 1*gammaZeroGenerator 2=centralInP := by decide +kernel

theorem gamma_zero_coordinates : ∀x:P,x∈gamma 0→
    x.right=1 ∧ x.left 1∈plane true ∧ x.left turn∈plane true := by decide +kernel


def tGammaGenerator (i:Fin 3) : P := if i=0 then pair (DihedralGroup.r 2,1)
  else if i=1 then pair (1,DihedralGroup.r 2) else pair (DihedralGroup.sr 0,DihedralGroup.sr 0)

theorem tGammaGenerator_mem : ∀i:Fin 3,tGammaGenerator i∈gamma 1 ∨ tGammaGenerator i∈gamma 3 := by
  decide +kernel

def tGammaWord (e:Fin 3→Fin 2) : P :=
  tGammaGenerator 0^(e 0).val*tGammaGenerator 1^(e 1).val*tGammaGenerator 2^(e 2).val

theorem t_gamma_span_certificate : ∀x:P,coreTest x →
    x.right=1 → x.left 1∈plane false → x.left turn∈plane false →
    ∃e:Fin 3→Fin 2,tGammaWord e=x := by decide +kernel

theorem t_gamma_coordinates : ∀x:P,x∈gamma 1 ∨ x∈gamma 3 →
    x.right=1 ∧ x.left 1∈plane false ∧ x.left turn∈plane false := by decide +kernel

end SymmetricFourWreath.InvolutionClasses
