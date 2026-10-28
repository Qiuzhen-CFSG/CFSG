module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.Seven.LocalGeometry.PermutationOvergroups.Coordinates

/-!
# A bounded four-point generation calculation

Any nonidentity cubic permutation of four points, together with its conjugate
by (01)(23), generates A₄. Every even element is a product with three exponents
in {0,1,2}. The second check puts this double transposition in the compatible
seven-point Sylow subgroup. The checks range over S₄, not S₇ subgroups.

Source application: Aschbacher--Smith, combined manuscript (1 March 2004),
15.3.42, printed p.1138, identifying Y₊ with A₄ × C₃.
-/

@[expose] public section

open Equiv Subgroup
namespace CFSG.Quasithin.Chapter15.Section03.RankTwo.NonCharacteristicTwo.AlternatingSeven

def doubleSwap : Perm (Fin 4) := swap 0 1 * swap 2 3

set_option maxRecDepth 10000 in
theorem fourPoint_generation : ∀ f : Perm (Fin 4), f ^ 3 = 1 → f ≠ 1 →
    ∀ g : Perm (Fin 4), g.sign = 1 → ∃ i j k : Fin 3,
      g = f ^ i.val * (doubleSwap * f * doubleSwap⁻¹) ^ j.val * f ^ k.val := by
  decide +kernel

open CFSG.Quasithin.Chapter13.Section08.ComponentSieve.Seven
open LocalGeometry.PermutationOvergroups

theorem doubleSwap_standard : fourThreeHom (doubleSwap, 1) ∈ standardTwo ∧
    fourThreeHom (doubleSwap, 1) ∈ alternatingGroup (Fin 7) := by
  decide +kernel

end CFSG.Quasithin.Chapter15.Section03.RankTwo.NonCharacteristicTwo.AlternatingSeven
