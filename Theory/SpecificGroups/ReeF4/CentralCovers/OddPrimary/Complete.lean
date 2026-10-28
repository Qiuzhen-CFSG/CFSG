module
public import Theory.SpecificGroups.ReeF4.CentralCovers.OddPrimary.KernelSource
public import Theory.SpecificGroups.ReeF4.CentralCovers.OddPrimary.GoodPrimes.Unitary.Descent.Subsystem.Application

/-!
# The complete odd-primary bound for Ree perfect central covers

The actual unitary subsystem supplies the remaining norm-one and Singer
tori. The proved cofactor calculations and three-primary configuration
therefore exclude every odd prime from the kernel of any finite perfect
central cover. In particular a marked quasisimple Ree cover has two-group
center. No multiplier or local-geometry hypothesis remains.

Source: Aschbacher–Smith I.1.1–4 and A.3.6; GLS3 §6.1 and §4.10.
-/

public noncomputable section
namespace ReeF4.CentralCovers.OddPrimary
open PerfectCentralCovering Subgroup Theory.GroupTheory

theorem not_dvd_kernel (m : ℕ) (hm : 1 ≤ m)
    {p : ℕ} [Fact p.Prime] (hp : p ≠ 2)
    {E : Type*} [Group E] [Finite E] (c : Cover E (Model m)) :
    ¬ p ∣ Nat.card c.toMonoidHom.ker :=
  not_dvd_kernel_of_unitary_tori m hm (GoodPrimes.Unitary.Descent.nonempty_tori m hm).1
    (GoodPrimes.Unitary.Descent.nonempty_tori m hm).2 hp c

theorem kernel_isPGroup (m : ℕ) (hm : 1 ≤ m)
    {E : Type*} [Group E] [Finite E] (c : Cover E (Model m)) :
    IsPGroup 2 c.toMonoidHom.ker :=
  kernel_isPGroup_of_unitary_tori m hm (GoodPrimes.Unitary.Descent.nonempty_tori m hm).1
    (GoodPrimes.Unitary.Descent.nonempty_tori m hm).2 c

theorem center_isPGroup_of_quotient_equiv (m : ℕ) (hm : 1 ≤ m)
    {L : Type*} [Group L] [Finite L] [Group.IsPerfect L]
    (e : L ⧸ center L ≃* Model m) : IsPGroup 2 (center L) :=
  center_isPGroup_of_unitary_tori m hm (GoodPrimes.Unitary.Descent.nonempty_tori m hm).1
    (GoodPrimes.Unitary.Descent.nonempty_tori m hm).2 e

theorem localBlock_center_isPGroup (m : ℕ) (hm : 1 ≤ m)
    {L : Type*} [Group L] [Finite L] [IsQuasisimple L]
    (d : LocalBlockInput m) (e : L ⧸ center L ≃* d.fixedGroup) :
    IsPGroup 2 (center L) :=
  center_isPGroup_of_quotient_equiv m hm (e.trans d.modelEquiv)

end ReeF4.CentralCovers.OddPrimary
