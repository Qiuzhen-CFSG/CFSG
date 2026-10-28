module
public import Theory.GroupTheory.PCoreLocalSetup
public import Mathlib.GroupTheory.GroupAction.ConjAct
public import Mathlib.GroupTheory.PGroup

/-!
# A normal p-subgroup centralizes a single nonidentity conjugacy orbit

A p-group acting on a finite group of order divisible by p fixes a
nonidentity element. If all nonidentity elements of a normal subgroup form
one ambient conjugacy orbit, normality of the acting p-subgroup transports
that fixedness to every element. Thus it centralizes the entire subgroup.

The application is O₂(X) acting on the normal four-plane in the binary
triality short centralizer, in Aschbacher--Smith F.4.42, printed p.295.
-/

public noncomputable section
open Subgroup
namespace Subgroup
variable {G : Type*} [Group G] [Finite G]

theorem normal_pGroup_centralizes_of_transitive_nonidentity
    {p : ℕ} [Fact p.Prime] (N V : Subgroup G) [N.Normal] [V.Normal]
    (hN : IsPGroup p N) (hcard : p ∣ Nat.card V)
    (htrans : ∀ x ∈ V, x ≠ 1 → ∀ y ∈ V, y ≠ 1 → ∃ g : G, g*x*g⁻¹=y) :
    N ≤ centralizer (V : Set G) := by
  let action : N →* MulAut V := (MulAut.conjNormal (H := V)).comp N.subtype
  let : MulAction N V := MulAction.compHom V action
  obtain ⟨v,hv,hv1⟩ := hN.exists_fixed_point_of_prime_dvd_card_of_fixed_point V hcard
    (a := 1) (by intro n; exact map_one (action n))
  have hvne : (v : G) ≠ 1 := fun h => hv1 (Subtype.ext h).symm
  have hvfix (n : G) (hn : n ∈ N) : n*(v:G)*n⁻¹=(v:G) :=
    congrArg Subtype.val (hv ⟨n,hn⟩)
  intro n hn y hy
  by_cases hy1 : y=1
  · simp only [hy1,mul_one,one_mul]
  · obtain ⟨g,hg⟩ := htrans v v.property hvne y hy hy1
    have hb : g⁻¹*n*g ∈ N := by
      simpa only [inv_inv] using (inferInstance : N.Normal).conj_mem n hn g⁻¹
    have hh := congrArg (fun x : G => g*x*g⁻¹) (hvfix (g⁻¹*n*g) hb)
    have he : n*(g*(v:G)*g⁻¹)*n⁻¹=g*(v:G)*g⁻¹ := by
      calc
        _ = g*((g⁻¹*n*g)*(v:G)*(g⁻¹*n*g)⁻¹)*g⁻¹ := by group
        _ = _ := hh
    rw [hg] at he
    exact (mul_inv_eq_iff_eq_mul.mp he).symm

end Subgroup
