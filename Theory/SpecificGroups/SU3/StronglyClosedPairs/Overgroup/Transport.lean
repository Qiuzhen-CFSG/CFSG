module
public import Theory.SpecificGroups.SU3.StronglyClosedPairs.Overgroup.Normalized
public import Theory.GroupAction.AutomorphismFixedTransport

/-!
# Transport of the outer-factor argument to the original Sylow

Conjugate the supplied Sylow subgroup of PSU₃ to the matrix root Sylow.
The induced equivalence of the full automorphism group transports the
two-group and its factor together. Its compatibility with the inner map
preserves both alternatives for the inner intersection and innerness of
involutions. Transporting the conclusion back retains the original factor.
No assertion that a separate model conjugator lies in the given overgroup
is needed.

Source: Sylow conjugacy and the unitary model calculation for
Aschbacher (1975), Lemma 3.4, pp.94–96.
-/

open Subgroup BenderSuzuki.External
namespace BenderSuzuki.MatrixGroups.HermitianForm.StronglyClosedPairs
open BorelTorus
variable {E : Type*} [Field E] [Finite E]
variable (J : HermitianForm 3 E)

/-- The normalized matrix argument transports along an actual Sylow conjugacy,
retaining the original factor and its inner part. -/
public theorem sylow_normalizing_factor_inner
    {n : ℕ} (hn : 2 ≤ n) (hJ : J.form = !![0,0,1;0,1,0;1,0,0])
    (hcard : Nat.card E = (2^n)^2)
    (hfixed : Nat.card {x : E // J.conj x = x} = 2^n)
    (P : Sylow 2 (ProjectiveSpecialUnitaryMatrixGroup J))
    (A B : Subgroup (MulAut (ProjectiveSpecialUnitaryMatrixGroup J)))
    (hA : IsPGroup 2 A) (hBA : B ≤ A)
    (hPA : (P : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)).map MulAut.conj ≤ A)
    (hstable : ∀ a ∈ A, (P : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)).map a.toMonoidHom = P)
    (hinv : ∀ b ∈ B, b^2 = 1 → b ∈ (MulAut.conj : ProjectiveSpecialUnitaryMatrixGroup J →* _).range)
    (hpart : (∀ x : ProjectiveSpecialUnitaryMatrixGroup J, MulAut.conj x ∈ B → x^2 = 1) ∨
      (P : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)).map MulAut.conj ≤ B) :
    B ≤ (MulAut.conj : ProjectiveSpecialUnitaryMatrixGroup J →* _).range := by
  let X : Type _ := ProjectiveSpecialUnitaryMatrixGroup J
  let : Finite X := Finite.of_surjective J.specialToProjective J.specialToProjective_surjective
  let : Fintype E := Fintype.ofFinite E
  let : CharP E 2 := charP_of_card_eq_prime_pow (p := 2) (f := n*2) (by
    simpa only [Nat.card_eq_fintype_card, pow_mul] using hcard)
  let U := EvenTwoRank.rootSylow J hJ (show 0 < n by omega) hcard hfixed
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq X P U
  let e := MulAut.conj g
  let f := MulAut.congr e
  have hP : (P : Subgroup X).map e.toMonoidHom = projectiveRoot J hJ := congrArg Sylow.toSubgroup hg
  have hfconj (x : X) : f (MulAut.conj x) = MulAut.conj (e x) := MulAut.congr_conj e x
  have himap : (projectiveRoot J hJ).map MulAut.conj =
      ((P : Subgroup X).map MulAut.conj).map f.toMonoidHom := by
    rw [← hP, map_map, map_map]
    congr 1
    apply MonoidHom.ext
    intro x
    exact (hfconj x).symm
  have hinner {a : MulAut X} (ha : a ∈ (MulAut.conj : X →* _).range) :
      f a ∈ (MulAut.conj : X →* _).range := by
    obtain ⟨x, rfl⟩ := ha
    exact ⟨e x, (hfconj x).symm⟩
  have hn : B.map f.toMonoidHom ≤ (MulAut.conj : X →* _).range := by
    apply root_normalizing_factor_inner J hJ hn hcard hfixed
      (A.map f.toMonoidHom) (B.map f.toMonoidHom) (hA.map f.toMonoidHom) (map_mono hBA)
    · rw [himap]; exact map_mono hPA
    · rintro _ ⟨a, ha, rfl⟩
      rw [← hP, map_map]
      have hh : (f a).toMonoidHom.comp e.toMonoidHom = e.toMonoidHom.comp a.toMonoidHom := by
        apply MonoidHom.ext
        intro x
        change e (a (e.symm (e x))) = e (a x)
        rw [e.symm_apply_apply]
      change (P : Subgroup X).map ((f a).toMonoidHom.comp e.toMonoidHom) = _
      rw [hh, ← map_map, hstable a ha]
    · rintro _ ⟨b, hb, rfl⟩ hs
      apply hinner
      apply hinv b hb
      apply f.injective
      change (f b)^2 = 1 at hs
      simpa only [map_pow, map_one] using hs
    · rcases hpart with hs | hh
      · left
        intro x hx
        have hx' : MulAut.conj (e.symm x) ∈ B := by
          have hh : f (MulAut.conj (e.symm x)) ∈ B.map f.toMonoidHom := by
            simpa only [hfconj, e.apply_symm_apply] using hx
          obtain ⟨b, hb, he⟩ := hh
          exact f.injective he ▸ hb
        apply e.symm.injective
        rw [map_pow, map_one]
        exact hs _ hx'
      · right
        rw [himap]
        exact map_mono hh
  intro b hb
  obtain ⟨x, hx⟩ := hn (mem_map_of_mem f.toMonoidHom hb)
  refine ⟨e.symm x, f.injective ?_⟩
  rw [hfconj, e.apply_symm_apply, hx]
  rfl

end BenderSuzuki.MatrixGroups.HermitianForm.StronglyClosedPairs
