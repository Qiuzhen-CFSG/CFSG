module
public import Theory.GroupTheory.ElementaryEightFixedPointOrder24
public import Theory.GroupTheory.ElementaryEightSolvableCore
public import Theory.GroupTheory.PCoreFrattiniTransport
public import Theory.GroupTheory.SymmetricThreeTwoCoreStructure

/-!
# A symmetric-three core quotient acting on an elementary eight

Let a finite group act on an elementary abelian group of order eight,
fixing a nonidentity element. If the action kernel is properly contained
in the two-core and the quotient by that core is S₃, the action image is
S₄. The literal quotient by the action kernel is identified with S₄.

The fixed point makes the image order divide 24. Removing the two-group
kernel preserves its S₃ core quotient, so its order is 6 times the order
of its nontrivial two-core. Order 12 is impossible: a solvable automizer
of an elementary eight with four-divisible order has two-core of order
at least four. The faithful four-character action then recognizes S₄.

Source application: Delgado--Goldschmidt--Stellmacher, Groups and Graphs
(1985), (13.1)(f), printed p.191. Its consumer uses the actual radius-one
center span and constructs the kernel as the intersection of vertex cores.
-/

public noncomputable section
open Subgroup

/-- The action quotient is S₄, with its order and its literal kernel retained. -/
theorem elementaryEight_fixed_point_symmetricThree_core_quotient
    {H E : Type*} [Group H] [Finite H] [Group E] [Finite E]
    [IsElementaryAbelian 2 E] (hE : Nat.card E = 8)
    (ρ : H →* MulAut E) (z : E) (hz : z ≠ 1)
    (hfix : ∀ h, ρ h z = z)
    (e : (H ⧸ pCore 2 H) ≃* Equiv.Perm (Fin 3))
    (hk : ρ.ker < pCore 2 H) :
    Nat.card ρ.range = 24 ∧ Nonempty ((H ⧸ ρ.ker) ≃* Equiv.Perm (Fin 4)) := by
  let A := ρ.range
  let f := ρ.rangeRestrict
  have hf : Function.Surjective f := ρ.rangeRestrict_surjective
  have hker : f.ker = ρ.ker := by
    ext x
    change (⟨ρ x, ⟨x,rfl⟩⟩ : ρ.range) = 1 ↔ ρ x = 1
    exact Subtype.ext_iff
  have hp : IsPGroup 2 f.ker := hker.symm ▸ pCore_isPGroup.to_le hk.le
  let eq := (f.pCoreQuotientEquiv hf hp).symm.trans e
  have hratio : Nat.card A = 6 * Nat.card (pCore 2 A) := by
    rw [card_eq_card_quotient_mul_card_subgroup (pCore 2 A), Nat.card_congr eq.toEquiv]
    norm_num [Nat.card_eq_fintype_card, Fintype.card_perm]
  have hcore : pCore 2 A ≠ ⊥ := by
    intro hbot
    have hh := f.comap_pCore_of_ker_isPGroup hf hp
    rw [hbot, MonoidHom.comap_bot, hker] at hh
    exact hk.ne hh
  have hgt : 1 < Nat.card (pCore 2 A) := by
    have hpos : 0 < Nat.card (pCore 2 A) := Nat.card_pos
    have hne : Nat.card (pCore 2 A) ≠ 1 := fun he => hcore (card_eq_one.mp he)
    omega
  have hfixA : ∀ a : A, (a : MulAut E) z = z := by
    intro a
    obtain ⟨h,rfl⟩ := hf a
    exact hfix h
  have hd := elementaryEight_fixed_point_image_card_dvd_twentyfour hE z hz A hfixA
  have hmem := Nat.mem_divisors.mpr ⟨hd, by decide⟩
  have hd24 : (24 : ℕ).divisors = {1,2,3,4,6,8,12,24} := by decide
  rw [hd24] at hmem
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
  have hchoice : Nat.card A = 12 ∨ Nat.card A = 24 := by omega
  have hcard : Nat.card A = 24 := by
    rcases hchoice with h12 | h24
    · let : Group.IsSolvable A := SymmetricThreeTwoCore.solvable eq
      have hh := four_le_card_pCore_of_solvable_elementary_eight_automorphisms E hE A
        (by rw [h12]; decide)
      omega
    · exact h24
  obtain ⟨eA⟩ := elementaryEight_fixed_point_order24_equiv_S4 hE z hz A hcard hfixA
  exact ⟨hcard, ⟨(QuotientGroup.quotientKerEquivRange ρ).trans eA⟩⟩
