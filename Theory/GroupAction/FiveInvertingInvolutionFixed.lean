module
public import Theory.GroupAction.InvolutionDisplacementCard
public import Theory.GroupAction.FiveActionMinimalOrder
public import Theory.GroupTheory.NormalizedSupCard

/-!
# An involution inverting a five-action on an elementary group of order sixteen

Let E be an elementary abelian two-group of order sixteen. An automorphism
of square one that inverts an automorphism of order five has exactly four
fixed elements. Both automorphisms are actual elements of MulAut E; no
additional irreducibility or fixed-point hypothesis is imposed.

Orbit counting makes the order-five automorphism fixed-point-free on
nonidentity elements. If F is the fixed subgroup of the involution, then
F and its image under the order-five automorphism intersect trivially:
inversion makes an intersection point fixed by the square of that
automorphism, hence by the automorphism itself. Their product therefore
has order |F| squared and is contained in E. In the opposite direction,
the characteristic-two involution displacement map has image contained
in its kernel, giving |E| at most |F| squared. The two bounds force |F|=4.

This is the finite-action calculation used for the outer involution in
David Parrott, *A characterization of the Tits' simple group* (1972),
pp.674–675, before Lemma 3. The statement is independent of that local
group structure.
-/

open Subgroup
open scoped IsMulCommutative

private theorem mem_fixed_zpowers_iff {E : Type*} [Group E]
    (a : MulAut E) (x : E) :
    x ∈ FixedPoints.subgroup (zpowers a) E ↔ a x = x := by
  constructor
  · intro hx
    exact hx ⟨a, mem_zpowers a⟩
  · intro hx c
    obtain ⟨n, hn⟩ := c.property
    change (c : MulAut E) x = x
    rw [← hn]
    exact MulAction.mem_fixedBy_zpow (show x ∈ MulAction.fixedBy E a from hx) n

/-- An involution inverting an order-five automorphism on elementary sixteen fixes four elements. -/
public theorem card_fixed_of_involution_inverting_five_on_sixteen
    {E : Type*} [Group E] [Finite E] [IsElementaryAbelian 2 E]
    (hE : Nat.card E = 16) (a b : MulAut E) (ha : orderOf a = 5)
    (hb : b ^ 2 = 1) (hab : b * a * b⁻¹ = a⁻¹) :
    Nat.card (FixedPoints.subgroup (zpowers b) E) = 4 := by
  have hAcard : Nat.card (zpowers a) = 5 := by rw [Nat.card_zpowers, ha]
  have hfixedA : FixedPoints.subgroup (zpowers a) E = ⊥ := by
    apply Theory.GroupAction.fixed_eq_bot_of_five_action_card_sixteen hAcard hE
    intro htop
    have haone : a = 1 := by
      apply MulEquiv.ext
      intro x
      exact (mem_fixed_zpowers_iff a x).mp (htop ▸ mem_top x)
    simp [haone] at ha
  let F := FixedPoints.subgroup (zpowers b) E
  have hdisjoint : Disjoint F (F.map a.toMonoidHom) := by
    apply disjoint_iff.mpr
    apply bot_unique
    intro x hx
    obtain ⟨u, hu, rfl⟩ := hx.2
    have hbu : b u = u := (mem_fixed_zpowers_iff b u).mp hu
    have hbAu : b (a u) = a u := (mem_fixed_zpowers_iff b (a u)).mp hx.1
    have hba : b * a = a⁻¹ * b := mul_inv_eq_iff_eq_mul.mp hab
    have hinv : a⁻¹ u = a u := by
      have heval := congrArg (fun c : MulAut E => c u) hba
      change b (a u) = a⁻¹ (b u) at heval
      rw [hbu, hbAu] at heval
      exact heval.symm
    have hau2 : a (a u) = u := by
      have heval := congrArg a hinv
      simpa using heval.symm
    have hau4 : (a ^ 4) u = u := by
      change a (a (a (a u))) = u
      rw [hau2, hau2]
    have hau5 : (a ^ 5) u = u := by
      rw [← ha, pow_orderOf_eq_one]
      rfl
    have hau : a u = u := by
      calc
        a u = a ((a ^ 4) u) := congrArg a hau4.symm
        _ = (a ^ 5) u := rfl
        _ = u := hau5
    have huA : u ∈ FixedPoints.subgroup (zpowers a) E := (mem_fixed_zpowers_iff a u).mpr hau
    have huone : u = 1 := by simpa only [hfixedA, mem_bot] using huA
    exact mem_bot.mpr (by simp [huone])
  have hupper : Nat.card F * Nat.card F ≤ Nat.card E := by
    have hcard := card_sup_eq_mul_of_normalizes_of_disjoint F (F.map a.toMonoidHom)
      (le_normalizer_of_normal (H := F)) hdisjoint
    rw [card_map_of_injective a.injective] at hcard
    rw [← hcard]
    exact card_le_card_group _
  have hlower : Nat.card E ≤ Nat.card F * Nat.card F := by
    obtain ⟨hcount, hle⟩ := MulAut.involution_fixed_displacement_card_data b hb
    change Nat.card E = Nat.card F * _ at hcount
    rw [hcount]
    exact Nat.mul_le_mul_left _ (card_le_of_le hle)
  change Nat.card F = 4
  rw [hE] at hupper hlower
  nlinarith
