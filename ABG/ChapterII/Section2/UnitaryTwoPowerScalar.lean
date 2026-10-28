module
public import ABG.ChapterII.Section2.UnitaryScalarGeneration
public import Theory.SpecificGroups.GL2.TwoPowerScalar

/-!
# Bounded scalar factors of the unitary determinant levels

For odd q with `2^(m+1)` dividing `q+1`, the actual scalar subgroup
`SU2ScalarLevel m` is cyclic of order `2^(m+1)`, central in GU2, and meets
the determinant-one level in a subgroup of order two. Together with scalar
generation, this supplies the scalar-factor data in ABG Chapter II,
Section 2, Lemma 1(v), article pages 17-18.

Every scalar root in the corresponding GL2 subgroup has norm one by the
divisibility hypothesis, so the entire subgroup lies in the actual GU2.
The canonical subgroup restriction equivalence transfers cyclicity and
cardinality from the proved GL2 scalar theorem. Centrality descends through
the actual inclusion. The level-zero intersection is the restriction of
the same GL2 determinant-kernel intersection, so its order remains two.
No special-unitary/special-linear identification is used.
-/

namespace ABG

open Matrix.GeneralLinearGroup

public theorem SU2ScalarLevel_structure
    (p n : ℕ) [Fact p.Prime] (hn : n ≠ 0) (hodd : Odd (p ^ n))
    (m : ℕ) (hdiv : 2 ^ (m + 1) ∣ p ^ n + 1) :
    let C := SU2ScalarLevel p n hn m
    IsCyclic C ∧ Nat.card C = 2 ^ (m + 1) ∧
      C ≤ Subgroup.center (GU2 p n hn) ∧
      Nat.card (C ⊓ SU2Level p n hn 0 : Subgroup (GU2 p n hn)) = 2 := by
  let F := GaloisField p (2 * n)
  let U := (unitaryForm 2 p n hn).unitarySubgroup
  let C := (rootsOfUnity (2 ^ (m + 1)) F).map (scalar (Fin 2))
  have hcard : Nat.card F = (p ^ n) ^ 2 := by
    rw [GaloisField.card p (2 * n) (Nat.mul_ne_zero (by decide) hn),
      ← pow_mul, Nat.mul_comm n 2]
  have hdivq : p ^ n + 1 ∣ Nat.card F - 1 := by
    rw [hcard]
    exact ⟨p ^ n - 1, by simpa only [one_pow] using Nat.sq_sub_sq (p ^ n) 1⟩
  have hoddF : Odd (Nat.card F) := by rw [hcard]; exact hodd.pow
  obtain ⟨hcyc, hCcard, hcent, hinter⟩ := twoPowerScalar_structure F hoddF m (hdiv.trans hdivq)
  have hCU : C ≤ U := by
    rintro A ⟨c, hc, rfl⟩
    apply (scalar_mem_GU2_iff p n hn c).mpr
    exact orderOf_dvd_iff_pow_eq_one.mp
      ((orderOf_dvd_iff_pow_eq_one.mpr hc).trans hdiv)
  let e := Subgroup.subgroupOfEquivOfLe hCU
  have hcyc' : IsCyclic (C.subgroupOf U) :=
    isCyclic_of_injective e.toMonoidHom e.injective
  refine ⟨hcyc', (Nat.card_congr e.toEquiv).trans hCcard, ?_, ?_⟩
  · intro A hA
    apply Subgroup.mem_center_iff.mpr
    intro B
    apply Subtype.ext
    exact Subgroup.mem_center_iff.mp (hcent hA) B.val
  · have hI : C.subgroupOf U ⊓ SU2Level p n hn 0 =
        (C ⊓ (det : GL (Fin 2) F →* Fˣ).ker).subgroupOf U := by
      ext A
      change (A.val ∈ C ∧ det A.val ^ (2 ^ 0) = 1) ↔
        A.val ∈ C ∧ det A.val = 1
      simp only [pow_zero, pow_one]
    change Nat.card (C.subgroupOf U ⊓ SU2Level p n hn 0 : Subgroup (GU2 p n hn)) = 2
    rw [hI]
    let eI := Subgroup.subgroupOfEquivOfLe
      (show C ⊓ (det : GL (Fin 2) F →* Fˣ).ker ≤ U from inf_le_left.trans hCU)
    exact (Nat.card_congr eI.toEquiv).trans hinter

end ABG
