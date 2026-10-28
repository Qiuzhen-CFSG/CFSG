module

public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.ComponentBranch.OtherModels.AlternatingSeven.FixedModel.Embedding
import Mathlib.Tactic
/-!
# The actual S₅ fixed subgroup in A₇

A permutation commuting with `(0 1)` preserves the two-letter block. Splitting
along that block and its five-letter complement, evenness determines the first
factor from the sign of the second. This proves surjectivity of the explicit
sign-corrected embedding, and hence identifies the fixed subgroup with S₅.
Its two-core is trivial and therefore is not self-centralizing.

Source: the A₇ exclusion in Aschbacher–Smith 15.4.18, printed pp.1162–1163,
for the components of F.6.18(7),(9), printed pp.309–310.
-/

@[expose] public section

open Equiv Equiv.Perm Subgroup
namespace CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.ComponentBranch.OtherModels.AlternatingSeven

lemma modelToFixed_surjective : Function.Surjective modelToFixed := by
  intro x
  let g : Perm (Fin 7) := x.val.val
  have hcomm : t * g = g * t := by
    have hx := congrArg Subtype.val ((MulAut.mem_fixedSubgroup _ _).mp x.property)
    change t * g * t⁻¹ = g at hx
    exact mul_inv_eq_iff_eq_mul.mp hx
  have h0 : g 0 = 0 ∨ g 0 = 1 := by
    apply Equiv.eq_or_eq_of_swap_apply_ne_self
    have hc := congrArg (fun f : Perm (Fin 7) => f 0) hcomm
    change t (g 0) = g 1 at hc
    change t (g 0) ≠ g 0
    rw [hc]
    exact g.injective.ne (by decide)
  have h1 : g 1 = 0 ∨ g 1 = 1 := by
    apply Equiv.eq_or_eq_of_swap_apply_ne_self
    have hc := congrArg (fun f : Perm (Fin 7) => f 1) hcomm
    change t (g 1) = g 0 at hc
    change t (g 1) ≠ g 1
    rw [hc]
    exact g.injective.ne (by decide)
  let e : Fin 2 ⊕ Fin 5 ≃ Fin 7 := finSumFinEquiv
  let δ : Perm (Fin 2 ⊕ Fin 5) := e.permCongrHom.symm g
  have hm : Set.MapsTo δ (Set.range Sum.inl) (Set.range Sum.inl) := by
    rintro _ ⟨i, rfl⟩
    fin_cases i
    · rcases h0 with h0 | h0
      · refine ⟨0, ?_⟩
        apply e.injective
        change e (Sum.inl 0) = e (e.symm (g (e (Sum.inl 0))))
        rw [e.apply_symm_apply]
        exact h0.symm
      · refine ⟨1, ?_⟩
        apply e.injective
        change e (Sum.inl 1) = e (e.symm (g (e (Sum.inl 0))))
        rw [e.apply_symm_apply]
        exact h0.symm
    · rcases h1 with h1 | h1
      · refine ⟨0, ?_⟩
        apply e.injective
        change e (Sum.inl 0) = e (e.symm (g (e (Sum.inl 1))))
        rw [e.apply_symm_apply]
        exact h1.symm
      · refine ⟨1, ?_⟩
        apply e.injective
        change e (Sum.inl 1) = e (e.symm (g (e (Sum.inl 1))))
        rw [e.apply_symm_apply]
        exact h1.symm
  obtain ⟨a, ha⟩ := Equiv.Perm.mem_sumCongrHom_range_of_perm_mapsTo_inl hm
  have hag : blockHom a = g := by
    change e.permCongrHom ((Equiv.Perm.sumCongrHom _ _) a) = g
    rw [ha]
    exact e.permCongrHom.apply_symm_apply g
  have heven : (blockHom a).sign = 1 := by
    rw [hag]
    exact x.val.property
  change (e.permCongr (Equiv.sumCongr a.1 a.2)).sign = 1 at heven
  rw [Equiv.Perm.sign_permCongr, Equiv.Perm.sign_sumCongr] at heven
  have hsmall : ∀ (u : Perm (Fin 2)) (v : ℤˣ),
      u.sign * v = 1 → u = signToTwo v := by decide +kernel
  have hleft := hsmall a.1 a.2.sign heven
  refine ⟨a.2, ?_⟩
  apply Subtype.ext
  apply Subtype.ext
  change blockHom (signToTwo a.2.sign, a.2) = g
  rw [← hleft]
  exact hag

noncomputable def transpositionFixedEquiv : S5 ≃* transpositionFixed :=
  MulEquiv.ofBijective modelToFixed ⟨modelToFixed_injective, modelToFixed_surjective⟩

lemma transpositionFixed_card : Nat.card transpositionFixed = 120 := by
  rw [← Nat.card_congr transpositionFixedEquiv.toEquiv]
  norm_num [S5, Nat.card_eq_fintype_card, Fintype.card_perm, Nat.factorial]

lemma transpositionFixed_twoCore_eq_bot : pCore 2 transpositionFixed = ⊥ := by
  rw [← pCore_map_iso 2 transpositionFixedEquiv, s5_twoCore_eq_bot, Subgroup.map_bot]

lemma transpositionFixed_obstruction :
    ¬ centralizer (pCore 2 transpositionFixed : Set transpositionFixed) ≤
      pCore 2 transpositionFixed := by
  rw [transpositionFixed_twoCore_eq_bot]
  intro h
  have htop : (⊤ : Subgroup transpositionFixed) ≤ ⊥ := by
    intro x _
    exact h (by simp [Subgroup.mem_centralizer_iff])
  have hc := Subgroup.card_le_of_le htop
  rw [Subgroup.card_top, Subgroup.card_bot, transpositionFixed_card] at hc
  omega
end CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.ComponentBranch.OtherModels.AlternatingSeven
