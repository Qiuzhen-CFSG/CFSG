module

public import Theory.Mathieu.M22.Properties.FourNormalizers.FixedSylow
public import Theory.Mathieu.M22.Properties.SylowPointwise.Innerness
public import Theory.GroupAction.ElementarySylowFixerBound

/-!
# Elementary pointwise Sylow fixers of M₂₂

The existing 128-row Sylow enumeration has just two central rows. Testing
commutation with the three certified generators proves this in the kernel.
Sylow conjugacy transports the bound to every Sylow subgroup. Together with
the intrinsic pointwise-fixer innerness theorem, this bounds elementary
abelian groups of Sylow fixers by two.

Source: Aschbacher–Smith, 1.1.5(3)(f), printed pp.501–503, and the
sporadic exclusion in the proof of 13.6.6, printed p.927. The permutation
data and its attribution are retained in `FourNormalizers.FixedSylow`.
-/

public section
open Subgroup
namespace Sporadic.Mathieu
open M22FourNormalizers.FixedSylow

set_option maxRecDepth 100000 in
private theorem central_rows : ∀ i : Fin 128,
    (∀ (j : Fin 3) (x : Fin 22),
      rowTable i (generatorTable j x) = generatorTable j (rowTable i x)) →
    i = 0 ∨ i = 104 := by
  decide +kernel

private theorem standard_center_card_le_two :
    Nat.card (center M22EvenGeometry.sylow) ≤ 2 := by
  classical
  let f : center M22EvenGeometry.sylow → ({0, 104} : Finset (Fin 128)) := fun z =>
    let i := Classical.choose (rowSylow_surjective z.val)
    ⟨i, by
      have hi := Classical.choose_spec (rowSylow_surjective z.val)
      have hc (j : Fin 3) (x : Fin 22) :
          rowTable i (generatorTable j x) = generatorTable j (rowTable i x) := by
        have he := mem_center_iff.mp z.property
          ⟨generator j, generator_mem_standard j⟩
        rw [← hi] at he
        have hp := congrArg (fun y : M22EvenGeometry.sylow => y.val.val x) he
        change generatorTable j ((rowElement i).val x) =
          (rowElement i).val (generatorTable j x) at hp
        simpa only [rowElement_apply] using hp.symm
      simpa only [Finset.mem_insert, Finset.mem_singleton] using central_rows i hc⟩
  have hf : Function.Injective f := by
    intro x y h
    have hi := congrArg Subtype.val h
    apply Subtype.ext
    exact (Classical.choose_spec (rowSylow_surjective x.val)).symm.trans
      ((congrArg rowSylow hi).trans (Classical.choose_spec (rowSylow_surjective y.val)))
  exact (Nat.card_le_card_of_injective f hf).trans (by
    rw [Nat.card_eq_fintype_card, Fintype.card_coe]
    exact Finset.card_le_two)

/-- Every Sylow center in the native M₂₂ has at most two elements. -/
theorem m22_sylow_center_card_le_two (S : Sylow 2 M22) : Nat.card (center S) ≤ 2 := by
  rw [Nat.card_congr (centerCongr (S.equiv M22EvenGeometry.sylow)).toEquiv]
  exact standard_center_card_le_two

/-- The cyclic Sylow-center input, with the finite calculation discharged. -/
theorem m22_sylow_center_isCyclic (S : Sylow 2 M22) : IsCyclic (center S) :=
by
  apply isCyclic_of_card_dvd_prime (p := 2)
  have h := m22_sylow_center_card_le_two S
  have hp := Nat.card_pos (α := center S)
  have hc : Nat.card (center S) = 1 ∨ Nat.card (center S) = 2 := by omega
  rcases hc with hc | hc <;> simp [hc]

/-- Centerlessness is inherited from the component's central quotient at the consumer. -/
theorem m22_elementary_sylow_fixer_card_le_two (hZ : center M22 = ⊥)
    (S : Sylow 2 M22) (A : Subgroup (MulAut M22)) [IsElementaryAbelian 2 A]
    (hfix : ∀ a ∈ A, ∀ x ∈ S, a x = x) : Nat.card A ≤ 2 := by
  let _ := m22_sylow_center_isCyclic S
  exact Theory.GroupAction.elementary_sylow_fixer_card_le_two_of_inner S hZ
    (fun a _ ha => M22SylowPointwise.automorphism_inner_of_fixes_sylow a S
      (fun x hx => ha ⟨x, hx⟩)) A hfix

end Sporadic.Mathieu
