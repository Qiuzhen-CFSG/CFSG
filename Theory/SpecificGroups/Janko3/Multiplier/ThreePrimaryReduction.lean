module

public import Theory.SpecificGroups.Janko3.Model.ThreePrimary.Structure
public import Theory.GroupTheory.PerfectCentralCoverLocalDerivedBound

/-!
# Transfer from the actual J₃ three-subgroup to perfect covering kernels

Restrict a central extension to the full preimage of the marked order-243
subgroup. After retaining the three-primary kernel, central transfer puts
that kernel in the local derived subgroup. A bound of three for its
intersection with the local kernel therefore excludes nine from the original
kernel, including when that kernel has other prime factors.

The local central-extension bound is an explicit pending input. The marked
subgroup, its generators, cubic relations, order, and prime-to-three index
are proved in `Model.ThreePrimary.Structure`. The two-primary exclusion and
the exact-multiplier lower bound are separate obligations.

Source: Aschbacher–Smith I.1.1–4, printed pp.407–408; GLS III, Table 5.3h.
-/

namespace Sporadic.Janko3.Multiplier
open Subgroup PerfectCentralCovering
universe u

/-- The local algebra still needed for the three-primary upper bound.
The extension is central with three-group kernel, but need not be perfect. -/
@[expose] public def LocalThreeKernelBound : Prop :=
  ∀ {D : Type u} [Group D] [Finite D] (g : D →* ThreePrimary.localSubgroup),
    Function.Surjective g → g.ker ≤ center D → IsPGroup 3 g.ker →
      Nat.card (g.ker ⊓ _root_.commutator D : Subgroup D) ≤ 3

/-- Apply the local derived-kernel bound to the literal order-243 subgroup.
This is a conditional reduction, not the completed J₃ multiplier theorem. -/
public theorem kernel_not_nine_dvd_of_local_bound
    (hlocal : LocalThreeKernelBound.{u})
    {E : Type u} [Group E] [Finite E] [Group.IsPerfect E]
    (f : E →* Model) (hf : Function.Surjective f)
    (hk : f.ker ≤ center E) : ¬ 9 ∣ Nat.card f.ker := by
  let : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let c : Cover E Model := {
    toMonoidHom := f
    surjective := hf
    isPerfect := inferInstance
    ker_le_center := hk }
  apply c.not_primePower_dvd_kernel_of_local_derived_bound
    (p := 3) (n := 2) ThreePrimary.localSubgroup
    ThreePrimary.localSubgroup_index_prime_to_three
  intro D _ _ g hg hgc hgp hd
  have hb := hlocal g hg hgc hgp
  have hl := Nat.le_of_dvd (Nat.card_pos (α :=
    (g.ker ⊓ _root_.commutator D : Subgroup D))) hd
  exact (by decide : ¬ (3 : ℕ) ^ 2 ≤ 3) (hl.trans hb)

end Sporadic.Janko3.Multiplier
