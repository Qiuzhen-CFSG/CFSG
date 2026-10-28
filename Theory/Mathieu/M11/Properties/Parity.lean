module

public import Mathlib.Algebra.Group.Fin.Basic
public import Theory.Mathieu.M11.Properties.Simplicity

set_option maxHeartbeats 800000
set_option maxRecDepth 100000

namespace Sporadic.Mathieu

private noncomputable def m11SignHom : M11 →* ℤˣ :=
  Equiv.Perm.sign.comp M11.subtype

/-- Every element of M11 is an even permutation in its natural action. -/
public theorem m11_sign_eq_one (g : M11) :
    Equiv.Perm.sign (g : Equiv.Perm (Fin 11)) = 1 := by
  let : IsSimpleGroup M11 := m11_isSimpleGroup
  have hnotinj : ¬ Function.Injective m11SignHom := by
    intro hinj
    have hcard := Nat.card_le_card_of_injective m11SignHom hinj
    rw [m11_order] at hcard
    norm_num at hcard
  have hkerne : m11SignHom.ker ≠ ⊥ := by
    intro hbot
    exact hnotinj ((MonoidHom.ker_eq_bot_iff m11SignHom).mp hbot)
  have hker : m11SignHom.ker = ⊤ :=
    m11SignHom.normal_ker.eq_bot_or_eq_top.resolve_left hkerne
  have hg : g ∈ m11SignHom.ker := by rw [hker]; trivial
  exact hg

end Sporadic.Mathieu
