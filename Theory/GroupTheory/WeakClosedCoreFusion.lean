module
public import Theory.GroupTheory.PResidual.FiniteImage
public import Theory.GroupTheory.SylowKernelCore
public import Theory.GroupTheory.CentralizerSmallKernelTransport
/-!
# Weak closure and a two-perfect centralizer factor

A homomorphism from a two-perfect group has image in the target two-residual.
If that residual has odd order, the homomorphism kills the source two-core.
When a centralizer has such a quotient with kernel in a weak-closure subgroup,
this excludes fusion to an element centralizing a two-perfect factor whose
two-core contains the original central involution.

Source application: Aschbacher--Smith 2.4.29, printed p.546.
-/
public section
open Subgroup
namespace IsPPerfect

theorem twoCore_le_ker_of_odd_residual
    {A B : Type*} [Group A] [Group B] [Finite A] [Finite B]
    (hp : IsPPerfect 2 A) (f : A →* B)
    (hodd : Odd (Nat.card (pResidual 2 B))) :
    pCore 2 A ≤ f.ker := by
  have hr : f.range ≤ pResidual 2 B := by
    have hh := map_pResidual_le 2 f
    rwa [(pResidual_eq_top_iff 2 A).mpr hp, ← MonoidHom.range_eq_map] at hh
  have hle : (pCore 2 A).map f ≤ pResidual 2 B :=
    (show (pCore 2 A).map f ≤ f.range from by
      rintro x ⟨a, _, rfl⟩
      exact ⟨a, rfl⟩).trans hr
  have hmap : IsPGroup 2 ((pCore 2 A).map f) := pCore_isPGroup.map f
  have hcop : Nat.Coprime (Nat.card ((pCore 2 A).map f)) (Nat.card (pResidual 2 B)) := by
    obtain ⟨n, hn⟩ := hmap.exists_card_eq
    rw [hn]
    exact hodd.coprime_two_left.pow_left n
  have hd := disjoint_of_coprime_natCard hcop
  apply (Subgroup.map_eq_bot_iff _).mp
  exact bot_unique fun x hx => hd.le_bot ⟨hx, hle hx⟩
end IsPPerfect

namespace Subgroup

theorem not_isConj_of_weak_closed_core_and_odd_residual
    {G B : Type*} [Group G] [Group B] [Finite G] [Finite B]
    (M P : Subgroup G) (f : M →* B)
    (hker : f.ker.map M.subtype ≤ P)
    (hodd : Odd (Nat.card (pResidual 2 B)))
    (z y : G) (hCM : centralizer ({z} : Set G) = M)
    (hweak : ∀ x ∈ P, IsConj z x → x = z)
    (L : Subgroup G) (hp : IsPPerfect 2 L)
    (hLC : L ≤ centralizer ({y} : Set G))
    (hzL : z ∈ L.pCoreIn 2) (hne : y ≠ z) : ¬ IsConj z y := by
  intro hc
  obtain ⟨g, hg⟩ := isConj_iff.mp hc
  let e : G ≃* G := MulAut.conj g⁻¹
  have hey : e y = z := by
    change g⁻¹ * y * (g⁻¹)⁻¹ = z
    rw [← hg]
    simp [mul_assoc]
  have hLM : L.map e.toMonoidHom ≤ M := by
    have hh := map_mono hLC (f := e.toMonoidHom)
    rw [Theory.GroupTheory.CentralizerSmallKernelTransport.map_centralizer, hey, hCM] at hh
    exact hh
  let a : L →* M := (e.toMonoidHom.comp L.subtype).codRestrict M
    (fun x => hLM ⟨x, x.property, rfl⟩)
  have hcore : pCore 2 L ≤ (f.comp a).ker := hp.twoCore_le_ker_of_odd_residual _ hodd
  obtain ⟨l, hl, hzl⟩ := hzL
  change (l : G) = z at hzl
  have hezP : e z ∈ P := by
    have ha : a l ∈ f.ker := hcore hl
    have hh := hker ⟨a l, ha, rfl⟩
    change e (l : G) ∈ P at hh
    rwa [hzl] at hh
  have hez : e z = z := hweak _ hezP (isConj_iff.mpr ⟨g⁻¹, rfl⟩)
  apply hne
  apply e.injective
  exact hey.trans hez.symm
end Subgroup
