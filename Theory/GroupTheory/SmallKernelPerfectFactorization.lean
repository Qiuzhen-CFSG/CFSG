module
public import Theory.GroupTheory.CyclicNormalCentralizer
public import Mathlib.GroupTheory.IsPerfect
public import Mathlib.GroupTheory.Index
public import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
# Factoring a small cover through a perfect quotient

A cyclic kernel over a perfect quotient is central: the derived subgroup
centralizes the kernel, and the two generate the whole cover. Every surjection
from the cover to a centerless group therefore factors through that quotient.

A cover of size at most three times its perfect quotient has cyclic kernel,
so this criterion applies without any perfection assumption on the cover.
An independent lower cardinal bound on the centerless target then makes the
factor map an isomorphism.
-/

public noncomputable section
open Subgroup
namespace Theory.GroupTheory.SmallKernelPerfectFactorization

private theorem cyclic_kernel_central
    {E B : Type*} [Group E] [Group B] [Group.IsPerfect B]
    (f : E →* B) (hf : Function.Surjective f) [IsCyclic f.ker] :
    f.ker ≤ center E := by
  have hs : _root_.commutator E ⊔ f.ker = ⊤ := by
    have hm : (_root_.commutator E).map f = (⊤ : Subgroup E).map f := by
      rw [map_commutator_eq,MonoidHom.range_eq_top.mpr hf,
        ←_root_.commutator_def,Group.IsPerfect.commutator_eq_top,map_top_of_surjective f hf]
    simpa only [top_sup_eq] using map_eq_map_iff.mp hm
  have hD := commutator_le_centralizer_of_isCyclic_normal f.ker
  have hK : f.ker ≤ centralizer (f.ker : Set E) := by
    intro k hk l hl
    exact congrArg Subtype.val (mul_comm' (⟨l,hl⟩ : f.ker) ⟨k,hk⟩)
  have hall : centralizer (f.ker : Set E) = ⊤ := top_unique (hs ▸ sup_le hD hK)
  intro k hk
  exact mem_center_iff.mpr fun y => ((hall.ge (mem_top y)) k hk).symm

/-- A centerless quotient of a cyclic extension of a perfect group factors
surjectively through the perfect group, over the specified maps. -/
theorem exists_surjective_factor_of_cyclic_kernel
    {E B G : Type*} [Group E] [Group B] [Group G] [Group.IsPerfect B]
    (f : E →* B) (hf : Function.Surjective f) [IsCyclic f.ker]
    (q : E →* G) (hq : Function.Surjective q) (hcenter : center G = ⊥) :
    ∃ r : B →* G, Function.Surjective r ∧ r.comp f = q := by
  have hk : f.ker ≤ q.ker := by
    intro x hx
    have hxc := cyclic_kernel_central f hf hx
    have hqxc : q x ∈ center G := by
      apply mem_center_iff.mpr
      intro g
      obtain ⟨y,rfl⟩ := hq g
      simpa only [map_mul] using congrArg q (mem_center_iff.mp hxc y)
    rw [hcenter,mem_bot] at hqxc
    exact hqxc
  let e := QuotientGroup.quotientKerEquivOfSurjective f hf
  let l := QuotientGroup.lift f.ker q hk
  let r := l.comp e.symm.toMonoidHom
  refine ⟨r,(QuotientGroup.lift_surjective_of_surjective _ q hq hk).comp e.symm.surjective,?_⟩
  apply MonoidHom.ext
  intro x
  have he : e.symm (f x) = QuotientGroup.mk x := e.symm_apply_eq.mpr rfl
  change l (e.symm (f x)) = q x
  rw [he]
  rfl

private theorem kernel_isCyclic_of_card_le_three_mul
    {E B : Type*} [Group E] [Group B] [Finite E] [Finite B]
    (f : E →* B) (hf : Function.Surjective f)
    (hbound : Nat.card E ≤ 3 * Nat.card B) : IsCyclic f.ker := by
  have hc := f.ker.card_mul_index
  rw [index_eq_card,Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective f hf).toEquiv] at hc
  have hB : 0 < Nat.card B := Nat.card_pos
  have hk : 0 < Nat.card f.ker := Nat.card_pos
  have hn : Nat.card f.ker ≤ 3 := by nlinarith
  rcases (show Nat.card f.ker = 1 ∨ Nat.card f.ker = 2 ∨ Nat.card f.ker = 3 by omega)
    with h | h | h
  · exact isCyclic_of_card_dvd_prime (p := 2) (by rw [h]; decide)
  · exact isCyclic_of_prime_card h
  · exact isCyclic_of_prime_card h

/-- The size bound on the actual cover supplies the cyclic kernel; no
perfection of that cover is required. -/
theorem exists_surjective_factor_of_card_le_three_mul
    {E B G : Type*} [Group E] [Group B] [Group G]
    [Finite E] [Finite B] [Group.IsPerfect B]
    (f : E →* B) (hf : Function.Surjective f)
    (q : E →* G) (hq : Function.Surjective q) (hcenter : center G = ⊥)
    (hbound : Nat.card E ≤ 3 * Nat.card B) :
    ∃ r : B →* G, Function.Surjective r ∧ r.comp f = q := by
  let : IsCyclic f.ker := kernel_isCyclic_of_card_le_three_mul f hf hbound
  exact exists_surjective_factor_of_cyclic_kernel f hf q hq hcenter

/-- An independent target lower bound upgrades the factor map to an
isomorphism, still commuting with the original two quotient maps. -/
theorem exists_equiv_of_card_le_three_mul
    {E B G : Type*} [Group E] [Group B] [Group G]
    [Finite E] [Finite B] [Finite G] [Group.IsPerfect B]
    (f : E →* B) (hf : Function.Surjective f)
    (q : E →* G) (hq : Function.Surjective q) (hcenter : center G = ⊥)
    (hbound : Nat.card E ≤ 3 * Nat.card B) (hlower : Nat.card B ≤ Nat.card G) :
    ∃ e : B ≃* G, e.toMonoidHom.comp f = q := by
  obtain ⟨r,hr,hcomp⟩ := exists_surjective_factor_of_card_le_three_mul f hf q hq hcenter hbound
  have hc : Nat.card B = Nat.card G := le_antisymm hlower (Nat.card_le_card_of_surjective r hr)
  exact ⟨MulEquiv.ofBijective r ((Nat.bijective_iff_surjective_and_card r).mpr ⟨hr,hc⟩),hcomp⟩

end Theory.GroupTheory.SmallKernelPerfectFactorization
