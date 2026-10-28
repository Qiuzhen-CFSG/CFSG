module
public import Theory.SpecificGroups.SymmetricFourWreath.InvolutionClasses.BGeneration

/-!
# The marked binary circuit of five orbit points

For either local four-point choice, adjoining z gives five distinct
nonidentity elements whose only binary relation is their full product.
The original t is the product of the first two points. This is the
literal natural-module input for the S5 centralizer splitting.

Source: Aschbacher–Smith 13.9.9–10, printed p.973.
-/

@[expose] public section
namespace SymmetricFourWreath.InvolutionClasses

def fiveParameters (b:Bool) (i:Fin 5) : Parameters :=
  if hi:i.val<4 then classBasis b ⟨i.val,hi⟩ else
    (⟨DihedralGroup.r 2,by decide⟩,⟨DihedralGroup.r 2,by decide⟩)

theorem fiveParameters_injective (b:Bool) : Function.Injective (fiveParameters b) := by
  cases b <;> decide +kernel

theorem fiveParameters_ne_one : ∀b:Bool,∀i:Fin 5,fiveParameters b i≠1 := by decide +kernel

theorem fiveParameters_index : ∀b:Bool,∀i:Fin 5,
    parameterIndex (fiveParameters b i)=(if i=4 then 0 else if b then 4 else 2) := by decide +kernel

def fiveWord (b:Bool) (e:Fin 5→Fin 2) : Parameters :=
  fiveParameters b 0^(e 0).val*fiveParameters b 1^(e 1).val*
    fiveParameters b 2^(e 2).val*fiveParameters b 3^(e 3).val*fiveParameters b 4^(e 4).val

theorem fiveWord_relation : ∀b:Bool,∀e:Fin 5→Fin 2,
    fiveWord b e=1 ↔ e=0 ∨ e=1 := by decide +kernel

theorem fiveParameters_pair_t : ∀b:Bool,
    parametersToW (fiveParameters b 0)*parametersToW (fiveParameters b 1)=t := by
  intro b
  apply RegularWreathProduct.ext
  · funext i
    revert b i
    decide +kernel
  · cases b <;> rfl

theorem fiveParameters_four_z : ∀b:Bool,parametersToW (fiveParameters b 4)=z := by
  intro b
  apply RegularWreathProduct.ext
  · funext i
    revert b i
    decide +kernel
  · cases b <;> rfl

end SymmetricFourWreath.InvolutionClasses
