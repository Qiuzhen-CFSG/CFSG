module
public import Theory.GroupTheory.Fitting.Centralizer
public import Theory.GroupTheory.SolvableOuterQuotient
public import Theory.GroupTheory.SylowSmallIndexModels

/-!
# Solvable groups with Fitting subgroup of order five

The Fitting subgroup is self-centralizing. Its conjugation image has order
dividing four, so an even solvable group with Fitting order five has order
ten or twenty and trivial two-core. The existing recognition theorems give
actual isomorphisms with D₁₀ or the binary Suzuki matrix group.

Source application: Aschbacher--Smith 15.2.13, printed pp.1111--1112,
refs/quasithin.pdf.
-/

public section
open Subgroup
open scoped IsMulCommutative
namespace Theory.GroupTheory
variable {D : Type*} [Group D] [Finite D]

theorem small_models_of_fitting_card_five
    (hs : Group.IsSolvable D) (hF : Nat.card (fittingSubgroup D) = 5)
    (h2 : 2 ∣ Nat.card D) :
    Nonempty (D ≃* DihedralGroup 5) ∨
      Nonempty (D ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup 0) := by
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  let F := fittingSubgroup D
  let : IsCyclic F := isCyclic_of_prime_card hF
  have hCF : centralizer (F : Set D) = F := by
    apply le_antisymm (centralizer_fittingSubgroup_le_fittingSubgroup_of_solvable hs)
    intro x hx y hy
    exact congrArg Subtype.val (mul_comm (⟨y,hy⟩ : F) ⟨x,hx⟩)
  let f : D →* MulAut F := MulAut.conjNormal
  have hker : f.ker = F := (MulAut.conjNormal_ker_eq_centralizer F).trans hCF
  have hr : Nat.card f.range ∣ 4 := by
    have hh := f.range.card_subgroup_dvd_card
    rw [IsCyclic.card_mulAut,hF] at hh
    exact hh
  have hcount := f.ker.card_mul_index
  rw [index_ker,hker,hF] at hcount
  have hd20 : Nat.card D ∣ 20 := by
    rw [←hcount]
    exact Nat.mul_dvd_mul_left 5 hr
  have hd10 : 10 ∣ Nat.card D := (by decide : Nat.Coprime 2 5).mul_dvd_of_dvd_of_dvd
    h2 (hF ▸ F.card_subgroup_dvd_card)
  have hc : Nat.card D = 10 ∨ Nat.card D = 20 := by
    have hpos : 0 < Nat.card D := Nat.card_pos
    have hle := Nat.le_of_dvd (by decide : 0 < 20) hd20
    obtain ⟨n,hn⟩ := hd10
    omega
  have hcore : pCore 2 D = ⊥ := by
    have hd := card_dvd_of_le (pCore_le_fitting D 2)
    rw [hF] at hd
    have hcop : Nat.Coprime (Nat.card (pCore 2 D)) 5 := by
      obtain ⟨n,hn⟩ := (pCore_isPGroup (p := 2) (G := D)).exists_card_eq
      rw [hn]
      exact (by decide : Nat.Coprime 2 5).pow_left n
    have hcard : Nat.card (pCore 2 D) = 1 := by
      rcases (Nat.dvd_prime (by decide : Nat.Prime 5)).mp hd with he | he
      · exact he
      · rw [he] at hcop
        norm_num at hcop
    exact eq_bot_of_card_eq _ hcard
  exact hc.elim (fun hh => Or.inl (equiv_dihedral_of_card_ten hh hcore))
    (fun hh => Or.inr (Theory.SpecificGroups.SymmetricFive.FiveNormalizerOvergroups.equiv_suzuki_of_card_twenty hh hcore))
end Theory.GroupTheory
