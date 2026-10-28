module

public import Theory.SpecificGroups.Suzuki.AbelianSubgroups
public import Theory.SpecificGroups.Suzuki.ElementaryNormalizer

/-!
# Suzuki root involutions and two-group centralizers

Sylow conjugacy puts an involution in the concrete root subgroup. The
upper-right coordinate of its square forces its first root parameter to
vanish, so it is a genuine long-root matrix u(0,b), with b nonzero.
The existing root centralizer calculation puts its centralizer in that same
two-group, and hence in the corresponding Borel. No automorphism
classification or assertion about central covers is needed here.

Source: Huppert–Blackburn III, XI.3.1 and XI.3.3; the rank-one cases used
in Aschbacher–Smith, *The Classification of Quasithin Groups*,
16.1.4(1) and 16.1.6, printed pp.1171–1172.
-/

public section

open Subgroup
namespace BenderSuzuki.MatrixGroups
open PFAppendixIII

/-- Suzuki long-root involutions are conjugates of nonzero central root matrices. -/
@[expose] def IsSuzukiLongRootInvolution {m : ℕ} (x : SuzukiMatrixGroup m) : Prop :=
  orderOf x = 2 ∧
    ∃ g : SuzukiMatrixGroup m, ∃ b : BinaryGaloisField (2 * m + 1), b ≠ 0 ∧
      (MulAut.conj g x).val = SuzukiRootGL m 0 b

private theorem first_coordinate_zero (m : ℕ) (x : SuzukiMatrixGroup m)
    (hx : x ^ 2 = 1) (a b : BinaryGaloisField (2 * m + 1))
    (he : x.val = SuzukiRootGL m a b) : a = 0 := by
  have h := congrArg (fun y : SuzukiMatrixGroup m => y.val (0 : Fin 4) (2 : Fin 4)) hx
  have hab : a * a ^ (2 ^ (m + 1)) = 0 := by
    have heq : b + (a * a ^ (2 ^ (m + 1)) + b) = 0 := by
      simpa [pow_two, he, SuzukiRootGL, SuzukiRootMatrix,
        Matrix.mul_apply, Fin.sum_univ_four, add_assoc] using h
    have hc : b + (a * a ^ (2 ^ (m + 1)) + b) = a * a ^ (2 ^ (m + 1)) := by
      rw [add_left_comm, CharTwo.add_self_eq_zero, add_zero]
    rwa [hc] at heq
  rcases mul_eq_zero.mp hab with ha | ha
  · exact ha
  · exact (eq_zero_of_pow_eq_zero ha)

/-- The concrete root and centralizer calculation for every Suzuki involution. -/
theorem suzuki_involution_root_geometry (m : ℕ) (hm : 0 < m)
    (x : SuzukiMatrixGroup m) (hx : orderOf x = 2) :
    ∃ (g : SuzukiMatrixGroup m) (b : BinaryGaloisField (2 * m + 1)), b ≠ 0 ∧
      (MulAut.conj g x).val = SuzukiRootGL m 0 b ∧
      centralizer {x} ≤ (SuzukiBorelSubgroup m).comap (MulAut.conj g).toMonoidHom ∧
      IsPGroup 2 (centralizer {x}) := by
  have hp : IsPGroup 2 (zpowers x) := by
    apply IsPGroup.of_card_dvd_pow (n := 1)
    rw [Nat.card_zpowers, hx]
    exact dvd_refl 2
  obtain ⟨Q, hQ⟩ := hp.exists_le_sylow
  obtain ⟨P, hP⟩ := suzukiRootSubgroup_isSylow m hm
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (SuzukiMatrixGroup m) Q P
  have hroot : MulAut.conj g x ∈ SuzukiRootSubgroup m := by
    rw [← hP, ← hg]
    exact ⟨x, hQ (mem_zpowers x), rfl⟩
  obtain ⟨a, b, hab⟩ := (mem_suzukiRootSubgroup_iff m _).mp hroot
  have hs : (MulAut.conj g x) ^ 2 = 1 := by
    have hx2 : x ^ 2 = 1 := by simpa only [hx] using pow_orderOf_eq_one x
    rw [← map_pow, hx2, map_one]
  have ha := first_coordinate_zero m _ hs a b hab
  subst a
  have hne : MulAut.conj g x ≠ 1 := by
    intro he
    have hx1 : x = 1 := (MulAut.conj g).injective (he.trans (map_one _).symm)
    simp [hx1] at hx
  have hb : b ≠ 0 := by
    intro hb
    apply hne
    apply Subtype.ext
    rw [hab, hb, External.suzukiRootGL_zero_zero]
    rfl
  have hle : centralizer {x} ≤
      (SuzukiRootSubgroup m).comap (MulAut.conj g).toMonoidHom := by
    intro y hy
    apply suzukiRootSubgroup_centralizer_le m hm hroot hne
    exact mem_centralizer_singleton_iff.mpr
      ((show Commute y x from mem_centralizer_singleton_iff.mp hy).map (MulAut.conj g)).eq
  have hUB : SuzukiRootSubgroup m ≤ SuzukiBorelSubgroup m := by
    rw [suzukiBorelSubgroup_eq_sup]
    exact le_sup_left
  exact ⟨g, b, hb, hab, hle.trans (comap_mono hUB),
    ((suzukiRootSubgroup_isPGroup m hm).comap_of_injective _
      (MulAut.conj g).injective).to_le hle⟩

end BenderSuzuki.MatrixGroups
