module

public import Theory.GroupTheory.PerfectCentralCoverAbelianSylow
public import Theory.PGroupCore

/-!
# Transfer from a subgroup with abelian quotient by its two-core

If a subgroup has index prime to an odd prime p and is abelian modulo its
two-core, its Sylow p-subgroup embeds in that abelian quotient. It is also
Sylow in the ambient group. Central Sylow transfer therefore excludes p
from every central kernel of a finite perfect ambient group.

The application in `OddPrimary.Split` uses the literal Borel preimage in a
central cover of Sp₄(F). Source: Aschbacher–Smith, I.1.2–I.1.3, printed p.407,
and the covered Borel calculation in E.2.2(2b).
-/

open Subgroup
open scoped IsMulCommutative

namespace PerfectCentralCovering

/-- A subgroup of index prime to p with abelian two-core quotient detects
the absence of central p-torsion in a finite perfect group. -/
public theorem not_dvd_card_kernel_of_two_core_quotient
    {E G : Type*} [Group E] [Finite E] [Group.IsPerfect E] [Group G]
    {p : ℕ} [Fact p.Prime] (hp : p ≠ 2) (f : E →* G)
    (hk : f.ker ≤ center E) (H : Subgroup E) (hi : ¬ p ∣ H.index)
    (hab : IsMulCommutative (H ⧸ pCore 2 H)) : ¬ p ∣ Nat.card f.ker := by
  let P : Sylow p H := default
  let q := (QuotientGroup.mk' (pCore 2 H)).comp (P : Subgroup H).subtype
  have hqi : Function.Injective q := by
    apply (MonoidHom.ker_eq_bot_iff q).mp
    apply eq_bot_iff.mpr
    intro x hx
    have hxcore : (x : H) ∈ pCore 2 H :=
      (QuotientGroup.eq_one_iff _).mp (show q x = 1 from hx)
    apply Subtype.ext
    exact Subgroup.disjoint_def.mp
      (IsPGroup.disjoint_of_ne p 2 hp _ _ P.isPGroup' pCore_isPGroup) x.property hxcore
  let : IsMulCommutative (H ⧸ pCore 2 H) := hab
  let : IsMulCommutative P := ⟨⟨fun x y => hqi (by simp only [map_mul, mul_comm])⟩⟩
  let Q : Subgroup E := (P : Subgroup H).map H.subtype
  have hQ : IsPGroup p Q := P.isPGroup'.map H.subtype
  have hQi : ¬ p ∣ Q.index := by
    rw [Subgroup.index_map_subtype]
    exact Nat.Prime.not_dvd_mul Fact.out P.not_dvd_index hi
  apply not_dvd_card_kernel_of_abelian_sylow f hk (hQ.toSylow hQi)
  change IsMulCommutative ((P : Subgroup H).map H.subtype)
  infer_instance

end PerfectCentralCovering
