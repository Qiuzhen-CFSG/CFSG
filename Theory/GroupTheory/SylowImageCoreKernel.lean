module
public import Theory.PGroupCore
public import Mathlib.GroupTheory.Index

/-!
# Detecting the two-core from a small Sylow image

For a homomorphism with two-group kernel, that kernel lies in O₂. If its
Sylow image has order at most the Sylow quotient by O₂, multiplicativity of
relative indices forces equality of the two kernels. This keeps the full
kernel, rather than discarding any central subgroup.

Source application: the original F₀ of MS93 (5.1), printed p.913, in
CriticalReduction.RootProductNilesPair. The central-root image bound makes
the original vertex projection have kernel exactly O₂(F₀).
-/

public section
open Subgroup
namespace Theory.GroupTheory
variable {G X : Type*} [Group G] [Finite G] [Group X]

theorem ker_eq_pCore_of_small_sylow_image
    (f : G →* X) (hf : IsPGroup 2 f.ker) (P : Sylow 2 G)
    (hbound : Nat.card ((P : Subgroup G).map f) ≤
      (pCore 2 G).relIndex (P : Subgroup G)) : f.ker = pCore 2 G := by
  have hk : f.ker ≤ pCore 2 G := le_sSup ⟨inferInstance,hf⟩
  have hprod := relIndex_mul_relIndex f.ker (pCore 2 G) (P : Subgroup G)
    hk (pCore_isPGroup.le_sylow_of_normal P)
  rw [relIndex_ker (P : Subgroup G) f] at hprod
  have hpos : 0 < (pCore 2 G).relIndex (P : Subgroup G) :=
    Nat.pos_of_ne_zero index_ne_zero_of_finite
  have hle : f.ker.relIndex (pCore 2 G) ≤ 1 :=
    Nat.le_of_mul_le_mul_right (by simpa only [one_mul,hprod] using hbound) hpos
  have hne : 0 < f.ker.relIndex (pCore 2 G) :=
    Nat.pos_of_ne_zero index_ne_zero_of_finite
  exact le_antisymm hk (relIndex_eq_one.mp (le_antisymm hle hne))
end Theory.GroupTheory
