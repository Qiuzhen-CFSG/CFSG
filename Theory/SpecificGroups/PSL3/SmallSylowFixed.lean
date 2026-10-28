module

public import Theory.GroupAction.SylowFixedSolvable
public import Theory.SpecificGroups.PSL3.LinearThreeSylow.PointwiseFixer
public import Theory.SpecificGroups.PSL3.EvenInnerCentralizers.InvolutionConjugacy
public import Theory.SpecificGroups.PSL3.EvenInnerCentralizers.FourElementField

/-!
# Solvable fixed groups of small binary PSL₃ Sylow fixers

The pointwise fixer of the upper unitriangular Sylow subgroup consists of
highest-root conjugations. A nonidentity root element is conjugate to the
marked transvection. Over fields of orders two and four, the centralizing
torus is scalar, so the full projective centralizer is a two-group.
Sylow conjugacy transports the calculation to every actual Sylow subgroup.

Source: Aschbacher--Smith, E.6.22, printed p.254 (PDF p.265), for the small
linear models and covers from E.6.8(1), printed pp.247--248.
-/

public section
open Subgroup
open scoped MatrixGroups
namespace Matrix.PSL3.EvenInnerCentralizers
open Matrix.PSL3Even.UnipotentGeometry
variable (F : Type*) [Field F] [Finite F]

/-- At q = 2 and q = 4, the full marked projective root centralizer is a two-group. -/
theorem small_centralizer_isTwoGroup (hF : Nat.card F = 2 ∨ Nat.card F = 4)
    [CharP F 2] : IsPGroup 2 (centralizer F) := by
  have ht (a : Fˣ) : torus F a = 1 := by
    apply (torus_eq_one_iff F a).mpr
    rcases hF with hF | hF
    · have hc : Nat.card Fˣ = 1 := by rw [Nat.card_units, hF]
      have ha : a = 1 := by simpa only [hc, pow_one] using (pow_card_eq_one' (x := a))
      simp [ha]
    · have hc : Nat.card Fˣ = 3 := by rw [Nat.card_units, hF]
      simpa only [hc] using (pow_card_eq_one' (x := a))
  have hs : Function.Surjective (unipotentInCentralizer F) := by
    intro g
    obtain ⟨a,u,he⟩ := centralizer_factorization F g
    rw [ht, one_mul] at he
    exact ⟨u,he.symm⟩
  have hu : IsPGroup 2 (U F) := by
    rcases hF with hF | hF
    · apply IsPGroup.of_card (n := 3)
      rw [card_U, hF]
    · apply IsPGroup.of_card (n := 6)
      rw [card_U, hF]
      rfl
  exact hu.of_surjective (unipotentInCentralizer F) hs

/-- Every nonidentity Sylow pointwise fixer in PSL₃(2) or PSL₃(4) has solvable
fixed subgroup. No coverage or innerness premise remains. -/
theorem small_sylow_fixed_solvable {n : ℕ} (hn : 0 < n) (hn2 : n ≤ 2)
    (hF : Nat.card F = 2 ^ n) (S : Sylow 2 PSL(3,F))
    (a : MulAut PSL(3,F)) (ha : a ≠ 1) (hfix : ∀ x ∈ S, a x = x) :
    _root_.Group.IsSolvable a.fixedSubgroup := by
  let := Fintype.ofFinite F
  have hc : ringChar F = 2 := FiniteField.even_card_iff_char_two.mpr (by
    rw [← Nat.card_eq_fintype_card, hF]
    simp [Nat.pow_mod, Nat.ne_of_gt hn])
  let : CharP F 2 := ringChar.of_eq hc
  have hs : Nat.card F = 2 ∨ Nat.card F = 4 := by
    have : n = 1 ∨ n = 2 := by omega
    rcases this with rfl | rfl <;> simp_all
  let : _root_.Group.IsNilpotent (centralizer F) := (small_centralizer_isTwoGroup F hs).isNilpotent
  let P := LinearThree.unipotentSylow F hn hF
  apply MulAut.fixed_solvable_of_sylow P S _ a ha hfix
  intro b hb hP
  obtain ⟨z, hz, rfl⟩ := LinearThree.exists_projectiveCenter_of_fixes_unipotent F hn hF b hP
  obtain ⟨c, rfl⟩ := (mem_projectiveCenter F z).mp hz
  have hu : (⟨0,0,c⟩ : U F) ≠ 1 := by
    intro he
    rw [he, map_one, map_one] at hb
    exact hb rfl
  have hu2 : (⟨0,0,c⟩ : U F) ^ 2 = 1 :=
    (square_eq_one_iff F _).mpr (Or.inl rfl)
  have hconj : IsConj (projective F ⟨0,0,c⟩) (root F) :=
    (projection F).map_isConj (specialLinear_isConj_root F _ hu hu2)
  obtain ⟨g, hg⟩ := isConj_iff.mp hconj
  let e := MulAut.fixedSubgroupCongr (MulAut.conj g) (MulAut.conj (projective F ⟨0,0,c⟩))
  have hfixed : (MulAut.congr (MulAut.conj g) (MulAut.conj (projective F ⟨0,0,c⟩))).fixedSubgroup =
      centralizer F := by
    rw [MulAut.congr_conj, show MulAut.conj g (projective F ⟨0,0,c⟩) = root F from hg,
      MulAut.fixedSubgroup_conj]
    rfl
  let f := e.trans (MulEquiv.subgroupCongr hfixed)
  exact _root_.Group.isSolvable_of_isSolvable_injective (f := f.toMonoidHom) f.injective
end Matrix.PSL3.EvenInnerCentralizers
