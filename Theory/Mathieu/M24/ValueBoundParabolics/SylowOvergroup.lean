module

public import Theory.GroupTheory.SylowIndexThreeQuotient
/-!
# Index-three overgroups of self-normalizing Sylow two-subgroups

The Sylow subgroup cannot become normal in a proper overgroup: relative
normality would put the overgroup in its ambient normalizer. For index
three, the faithful coset action therefore identifies the intrinsic
quotient by O₂ with S₃.

This is the local quotient argument used for the minimal Sylow overgroups
in Aschbacher–Smith, E.4.3(2), printed p. 242 (PDF p. 253).
-/

public section
open Subgroup
namespace Theory.GroupTheory
variable {G : Type*} [Group G] [Finite G]
/-- Relative index three and ambient self-normalization give the intrinsic S₃ quotient. -/
theorem symmetricThree_quotient_of_selfNormalizing_sylow (S : Sylow 2 G) (hn : normalizer (S : Set G) ≤ (S : Subgroup G))
    (H : Subgroup G) (hSH : (S : Subgroup G) ≤ H)
    (hi : (S : Subgroup G).relIndex H = 3) :
    Nonempty ((H ⧸ pCore 2 H) ≃* Equiv.Perm (Fin 3)) := by
  let P := S.subtype hSH
  have hindex : (P : Subgroup H).index = 3 := hi
  apply sylow_index_three_core_quotient P hindex
  apply lt_of_le_of_ne (pCore_isPGroup.le_sylow_of_normal P)
  intro he
  have hnormal : ((S : Subgroup G).subgroupOf H).Normal := by
    change (P : Subgroup H).Normal
    rw [← he]
    infer_instance
  have hHS : H ≤ (S : Subgroup G) :=
    ((normal_subgroupOf_iff_le_normalizer hSH).mp hnormal).trans hn
  have hEq := le_antisymm hSH hHS
  rw [hEq, Subgroup.relIndex_self] at hi
  contradiction
end Theory.GroupTheory
