module

public import Theory.SpecificGroups.SU3.OddPrimeSylowAutomorphisms.NormalizedOuterInvolutions.Coverage.Roots
public import Mathlib.GroupTheory.Sylow

/-!
# The defining-characteristic Sylow subgroup of PSU₃ with prime fixed-field order

The explicit upper root group has order `p³`. Comparing this with the actual
projective group order from Huppert II.10.12 shows that its index is prime to
`p`, including `p = 3`: the scalar divisor `gcd(3,p+1)` divides `p²-1`.
Sylow conjugacy consequently normalizes any automorphism to preserve this
root group. Normalizing the second root group still needs the rank-one
geometry.

This is the first normalization in Steinberg, Theorem 36, used by GLS3,
Theorem 2.5.12; the group and root maps are the actual matrices of §2.7.
-/

open Matrix BenderSuzuki.External
namespace BenderSuzuki.MatrixGroups.HermitianForm.OddPrimeSylow.NormalizedOuter.Coverage
variable {E : Type*} [Field E] [Finite E] (J : HermitianForm 3 E)
variable (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])
variable {p : ℕ} (hp : p.Prime)
variable (hcard : Nat.card E = p ^ 2)
variable (hfixed : Nat.card {x : E // J.conj x = x} = p)

include hp hcard hfixed in
/-- No additional factor of the defining prime occurs in the root index. -/
public theorem rootGroup_index_not_dvd : ¬ p ∣ (rootGroup J hJ).index := by
  obtain ⟨_, _, _, _, _, _, _, _, hGcard, _⟩ :=
    huppert_II_10_12 J p hcard hfixed hJ
  have hgcd : Nat.gcd 3 (p + 1) ∣ p ^ 2 - 1 := by
    have hf : p ^ 2 - 1 = (p - 1) * (p + 1) := by
      simpa [mul_comm] using Nat.sq_sub_sq p 1
    rw [hf]
    exact dvd_mul_of_dvd_right (Nat.gcd_dvd_right 3 (p + 1)) _
  have hdiv : Nat.gcd 3 (p + 1) ∣ (p ^ 3 + 1) * p ^ 3 * (p ^ 2 - 1) :=
    dvd_mul_of_dvd_right hgcd _
  have hi := (rootGroup J hJ).card_mul_index
  rw [rootGroup_card J hJ p hcard hfixed] at hi
  have hprod : (rootGroup J hJ).index * Nat.gcd 3 (p + 1) =
      (p ^ 3 + 1) * (p ^ 2 - 1) := by
    apply Nat.eq_of_mul_eq_mul_left (pow_pos hp.pos 3)
    calc
      p ^ 3 * ((rootGroup J hJ).index * Nat.gcd 3 (p + 1)) =
          Nat.card (ProjectiveSpecialUnitaryMatrixGroup J) * Nat.gcd 3 (p + 1) := by
            rw [← mul_assoc, hi]
      _ = (p ^ 3 + 1) * p ^ 3 * (p ^ 2 - 1) := by
        rw [hGcard, Nat.div_mul_cancel hdiv]
      _ = p ^ 3 * ((p ^ 3 + 1) * (p ^ 2 - 1)) := by ring
  intro hbad
  have hd : p ∣ (p ^ 3 + 1) * (p ^ 2 - 1) :=
    hprod ▸ dvd_mul_of_dvd_left hbad _
  have hnot : ¬ p ∣ 1 := hp.not_dvd_one
  rcases hp.dvd_mul.mp hd with h | h
  · exact hnot ((Nat.dvd_add_iff_right (dvd_pow_self p (by decide : 3 ≠ 0))).mpr h)
  · have hsq : 1 ≤ p ^ 2 := one_le_pow₀ hp.one_le
    have hp2 : p ∣ p ^ 2 := dvd_pow_self p (by decide : 2 ≠ 0)
    rw [← Nat.sub_add_cancel hsq] at hp2
    exact hnot ((Nat.dvd_add_iff_right h).mpr hp2)

/-- The root image, now certified as a Sylow subgroup in the defining prime. -/
public def rootSylow [Fact p.Prime] : Sylow p (ProjectiveSpecialUnitaryMatrixGroup J) :=
  (rootGroup_isPGroup J hJ hcard hfixed).toSylow
    (rootGroup_index_not_dvd J hJ hp hcard hfixed)

@[simp] public theorem rootSylow_coe [Fact p.Prime] :
    (rootSylow J hJ hp hcard hfixed : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)) =
      rootGroup J hJ := by rfl

include hp hcard hfixed in
/-- Sylow conjugacy normalizes an arbitrary automorphism to preserve the
actual upper root group. The remaining opposite-root normalization is separate. -/
public theorem exists_root_normalization
    (a : MulAut (ProjectiveSpecialUnitaryMatrixGroup J)) :
    ∃ (k : ProjectiveSpecialUnitaryMatrixGroup J)
      (b : MulAut (ProjectiveSpecialUnitaryMatrixGroup J)),
      a = MulAut.conj k * b ∧
      (rootGroup J hJ).map b.toMonoidHom = rootGroup J hJ := by
  let : Fact p.Prime := ⟨hp⟩
  let : Finite (ProjGenLinGroup (Fin 3) E) :=
    Finite.of_surjective ProjGenLinGroup.mk ProjGenLinGroup.mk_surjective
  let P := rootSylow J hJ hp hcard hfixed
  let Q := P.mapSurjective (f := a.toMonoidHom) a.surjective
  obtain ⟨k, hk⟩ := MulAction.exists_smul_eq (ProjectiveSpecialUnitaryMatrixGroup J) Q P
  have heq : ((rootGroup J hJ).map a.toMonoidHom).map (MulAut.conj k).toMonoidHom =
      rootGroup J hJ := congrArg Sylow.toSubgroup hk
  let b := MulAut.conj k * a
  refine ⟨k⁻¹, b, ?_, ?_⟩
  · dsimp [b]
    rw [map_inv]
    group
  · have hb : b.toMonoidHom = (MulAut.conj k).toMonoidHom.comp a.toMonoidHom := rfl
    rw [hb, ← Subgroup.map_map]
    exact heq

end BenderSuzuki.MatrixGroups.HermitianForm.OddPrimeSylow.NormalizedOuter.Coverage
