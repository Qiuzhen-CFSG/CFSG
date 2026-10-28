module

public import BenderSuzuki.ZD.Recognition.MinimalReduction.Radical.CentralLifting.Rigidity.BaseAutomorphisms.Suzuki
public import Theory.SpecificGroups.Suzuki.SylowOmegaGeometry
public import Theory.SpecificGroups.Suzuki.RootCenter
public import Theory.GroupAction.AutomorphismFixedTransport

/-!
# Pointwise rigidity of a Suzuki Borel

The existing inner-field coverage shows that a pointwise Sylow fixer is
conjugation by a member of that Sylow subgroup. Transport this conclusion
through an actual model equivalence and Sylow conjugacy. For Sz(8), fixation
of an order-seven subgroup forces the conjugating element to be identity:
otherwise its centralizer is contained in the Sylow two-subgroup.

No involutory or seven-group normalization assumption is needed for this
stronger rigidity statement. Its consumer is the centralization step of
Aschbacher–Smith, J.2.9, printed p.438 (PDF p.449), refs/quasithin.pdf.
The underlying automorphism calculation is GLS3, Theorem 2.6.5(e).
-/

@[expose] public section
open Subgroup
namespace BenderSuzuki.MatrixGroups

/-- An arbitrary pointwise Sylow fixer is induced by a member of that Sylow subgroup. -/
theorem suzuki_aut_fixing_sylow_inner {H : Type*} [Group H] [Finite H]
    {m : ℕ} (hm : 0 < m) (e : H ≃* SuzukiMatrixGroup m)
    (P : Sylow 2 H) (α : MulAut H) (hP : ∀ x ∈ P, α x = x) :
    ∃ g ∈ P, α = MulAut.conj g := by
  obtain ⟨f, hf, _⟩ := suzukiSylow_aligned_equiv hm e P
  let β := MulAut.congr f.symm α
  have hβ : ∀ x ∈ SuzukiRootSubgroup m, β x = x := by
    intro x hx
    have hxP : f x ∈ P := by
      change f x ∈ (P : Subgroup H)
      rw [← hf]
      exact mem_map_of_mem f.toMonoidHom hx
    change f.symm (α (f x)) = x
    rw [hP _ hxP, f.symm_apply_apply]
  obtain ⟨g, hg, he⟩ :=
    BenderSuzuki.ZD.BaseAutomorphisms.suzuki_aut_fixing_root_inner m hm β hβ
  refine ⟨f g, ?_, ?_⟩
  · change f g ∈ (P : Subgroup H)
    rw [← hf]
    exact mem_map_of_mem f.toMonoidHom hg
  apply (MulAut.congr f.symm).injective
  rw [MulAut.congr_conj, f.symm_apply_apply]
  exact he

/-- Fixing a Sylow two-subgroup and a seven-subgroup pointwise forces identity. -/
theorem suzuki_eight_aut_eq_one_of_fixing_sylow_and_seven
    {H : Type*} [Group H] [Finite H] (e : H ≃* SuzukiMatrixGroup 1)
    (P : Sylow 2 H) (D : Subgroup H) (hD : Nat.card D = 7)
    (α : MulAut H) (hP : ∀ x ∈ P, α x = x)
    (hfixD : ∀ x ∈ D, α x = x) : α = 1 := by
  obtain ⟨g, hg, rfl⟩ := suzuki_aut_fixing_sylow_inner (by decide) e P α hP
  by_cases hg1 : g = 1
  · rw [hg1, map_one]
  have hDP : D ≤ P := by
    intro x hx
    apply (suzukiSylow_borel_structure (by decide) e P).2.1 g hg hg1
    apply mem_centralizer_singleton_iff.mpr
    exact (mul_inv_eq_iff_eq_mul.mp (hfixD x hx)).symm
  have hd := card_dvd_of_le hDP
  rw [hD, suzukiSylow_card (by decide) e P] at hd
  norm_num at hd

end BenderSuzuki.MatrixGroups
