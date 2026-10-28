module

public import Theory.GroupTheory.PResidual.PrimeToTransport
public import Theory.PGroupCore

/-!
# Prime-to-p residuals above a nilpotent normal subgroup

If a normal nilpotent subgroup has index prime to p, its normal Sylow
p-subgroup also has index prime to p in the whole group. Hence the
prime-to-p residual equals the p-core. The relative version keeps the
original embedding of a solvable radical or other normal overgroup.

Source: the primary-radical reduction in Aschbacher--Smith 3.2.14, p.585.
-/

public section
open Subgroup
namespace Subgroup
variable {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]

/-- A nilpotent normal subgroup of index prime to p makes the prime-to-p
residual exactly the original p-core. -/
theorem primeToResidual_eq_pCore_of_nilpotent_normal
    (N : Subgroup G) [N.Normal] (hnil : Group.IsNilpotent N)
    (hcop : Nat.Coprime p N.index) : primeToResidual p G = pCore p G := by
  let P : Sylow p N := Classical.arbitrary _
  let S := (P : Subgroup N).map N.subtype
  let : S.Normal := P.normal_of_nilpotent_normal inferInstance hnil p
  have hS : Nat.Coprime p S.index := by
    rw [index_map_subtype]
    exact ((Fact.out : p.Prime).coprime_iff_not_dvd.mpr P.not_dvd_index).mul_right hcop
  apply le_antisymm
  · exact (primeToResidual_le S hS).trans (P.map_le_pCore inferInstance hnil p)
  · intro x hx
    obtain ⟨n,hn⟩ := (pCore_isPGroup (p := p) (G := G)) ⟨x,hx⟩
    exact mem_primeToResidual_of_pow (congrArg Subtype.val hn)

omit [Finite G] [Fact p.Prime] in
/-- The p-core of a normal subgroup containing the ambient p-core is the
same subgroup after its original inclusion. -/
theorem map_pCore_eq_of_normal_of_le
    (R : Subgroup G) [R.Normal] (hle : pCore p G ≤ R) :
    (pCore p R).map R.subtype = pCore p G := by
  refine le_antisymm (le_sSup ⟨inferInstance,pCore_isPGroup.map R.subtype⟩) ?_
  have hi : (pCore p G).subgroupOf R ≤ pCore p R :=
    le_sSup ⟨inferInstance,pCore_isPGroup.comap_subtype⟩
  simpa only [map_subgroupOf_eq_of_le hle] using map_mono (f := R.subtype) hi

end Subgroup
