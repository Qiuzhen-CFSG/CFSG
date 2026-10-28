module
public import Theory.SpecificGroups.Suzuki.EightOuterTori

/-!
# Odd-torus automorphisms under actual Suzuki model isomorphisms

Transport the pointwise-fixer and extension theorems through an actual
Sz(8) equivalence, retaining the literal inclusion of each Sylow subgroup.
The exact outer index three also shows that inner automorphisms together
with any outer automorphism generate the full automorphism group.

These are the model inputs for the cubic local extension in
Aschbacher–Smith, J.2.10, printed p.438 (PDF p.449), refs/quasithin.pdf.
The underlying torus and field actions are proved in EightOuterTori.
-/

open Subgroup
public section
namespace BenderSuzuki.MatrixGroups

/-- Pointwise torus rigidity transported through the actual model equivalence. -/
theorem suzuki_eight_sylow_odd_fixing_inner_model {H : Type*} [Group H] [Finite H]
    (e : H ≃* SuzukiMatrixGroup 1) {p : ℕ} [Fact p.Prime]
    (hp : p = 7 ∨ p = 13) (Y : Sylow p H)
    (α : MulAut H) (hfix : ∀ y : Y, α y = y) :
    ∃ y : Y, α = MulAut.conj (y : H) := by
  let Q := Y.mapSurjective (f := e.toMonoidHom) e.surjective
  let f : Y ≃* Q := e.subgroupMap (Y : Subgroup H)
  obtain ⟨z, hz⟩ := suzuki_eight_sylow_odd_fixing_inner hp Q (MulAut.congr e α) (by
    intro z
    obtain ⟨y, rfl⟩ := f.surjective z
    change e (α (e.symm (e y))) = e y
    rw [e.symm_apply_apply, hfix])
  refine ⟨f.symm z, (MulAut.congr e).injective ?_⟩
  rw [hz, MulAut.congr_conj]
  congr 1
  exact (congrArg Subtype.val (f.apply_symm_apply z)).symm

/-- Torus automorphisms extend through an actual Suzuki model equivalence. -/
theorem suzuki_eight_sylow_odd_aut_extend_model {H : Type*} [Group H] [Finite H]
    (e : H ≃* SuzukiMatrixGroup 1) {p : ℕ} [Fact p.Prime]
    (hp : p = 7 ∨ p = 13) (Y : Sylow p H) (β : MulAut Y) :
    ∃ α : MulAut H, ∀ y : Y, α (y : H) = (β y : H) := by
  let Q := Y.mapSurjective (f := e.toMonoidHom) e.surjective
  let f : Y ≃* Q := e.subgroupMap (Y : Subgroup H)
  obtain ⟨α, hα⟩ := suzuki_eight_sylow_odd_aut_extend hp Q (MulAut.congr f β)
  refine ⟨(MulAut.congr e).symm α, ?_⟩
  intro y
  apply e.injective
  change e (e.symm (α (e y))) = e (β y)
  rw [e.apply_symm_apply]
  have h := hα (f y)
  change α (e y) = e (β (f.symm (f y))) at h
  rwa [f.symm_apply_apply] at h

/-- Inner automorphisms and one outer automorphism generate the full automorphism group of Sz(8). -/
theorem suzuki_eight_aut_subgroup_eq_top (A : Subgroup (MulAut (SuzukiMatrixGroup 1)))
    (hI : (MulAut.conj : SuzukiMatrixGroup 1 →* MulAut (SuzukiMatrixGroup 1)).range ≤ A)
    (houter : ∃ α ∈ A, α ∉ (MulAut.conj : SuzukiMatrixGroup 1 →* MulAut (SuzukiMatrixGroup 1)).range) :
    A = ⊤ := by
  let I := (MulAut.conj : SuzukiMatrixGroup 1 →* MulAut (SuzukiMatrixGroup 1)).range
  have hlt : I < A := lt_of_le_of_ne hI (by
    rintro rfl
    obtain ⟨α, hα, hn⟩ := houter
    exact hn hα)
  have hd : A.index ∣ 3 := by
    simpa only [suzuki_eight_outer_index] using index_dvd_of_le hI
  have hi : A.index < 3 := by
    simpa only [I, suzuki_eight_outer_index] using index_strictAnti hlt
  exact index_eq_one.mp ((Nat.dvd_prime (by decide : Nat.Prime 3)).mp hd |>.resolve_right (by omega))

end BenderSuzuki.MatrixGroups
