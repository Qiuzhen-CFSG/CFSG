module
public import Theory.SpecificGroups.SU3.SylowOmega
public import Theory.GroupTheory.SylowNormalizerCommutingFamily
import all Theory.SpecificGroups.SU3.NormalizedRootCentralizers

/-!
# Elementary subgroups normalized by a binary unitary Borel

A nonzero elementary subgroup of a Sylow two-subgroup lies in its center.
For the standard Hermitian form, the full torus is transitive on the
nonzero central coordinates, so normalizer invariance makes that subgroup
the whole center. Sylow conjugacy and a Hermitian basis change give every
PSU₃ marking. The actual SU₃ scalar projection is injective on Sylow
two-subgroups and maps their normalizers onto the projective normalizers;
this retains the full special-unitary carrier and its scalar center.

The DGS (12.5) consumer identifies the original neighboring span image with
this entire omega subgroup, rather than merely bounding its order.
Source: Huppert II.10.12; Delgado--Goldschmidt--Stellmacher,
Groups and Graphs (1985), (5.9)(b) and (12.3)(a), printed pp.110,179.
The implementation import reuses the existing torus normalization proof
without changing that module's public boundary.
-/

public noncomputable section
open Subgroup BenderSuzuki.External
namespace BenderSuzuki.MatrixGroups.HermitianForm.BorelElementary
open BorelTorus BorelTorus.EvenCenterAction
open OddPrimeSylow.NormalizedOuter.FormTransport

private theorem card_transport {A B : Type*} [Group A] [Group B] [Finite A] [Finite B]
    (f : A →* B) (hf : Function.Surjective f) (P : Sylow 2 A)
    (hfi : Function.Injective (f.comp (P : Subgroup A).subtype))
    {q : ℕ}
    (hB : ∀ (T : Sylow 2 B) (D : Subgroup B), IsElementaryAbelian 2 D →
      D ≤ T → D ≠ ⊥ → normalizer (T : Set B) ≤ normalizer (D : Set B) → Nat.card D = q)
    (D : Subgroup A) [IsElementaryAbelian 2 D]
    (hDP : D ≤ P) (hne : D ≠ ⊥)
    (hnorm : normalizer (P : Set A) ≤ normalizer (D : Set A)) : Nat.card D = q := by
  let T := P.mapSurjective hf
  let E := D.map f
  let : IsElementaryAbelian 2 E := IsElementaryAbelian.map f
  have hi : Function.Injective (f.comp D.subtype) := by
    intro x y he
    have hh := hfi (a₁ := ⟨x,hDP x.property⟩) (a₂ := ⟨y,hDP y.property⟩) he
    exact Subtype.ext (congrArg (fun z : P => (z : A)) hh)
  have hc : Nat.card D = Nat.card E := Nat.card_congr
    (MonoidHom.ofInjective hi).toEquiv |>.trans (by
      rw [MonoidHom.range_comp,range_subtype])
  have he : E ≠ ⊥ := by
    intro he
    have hh := hc
    rw [he,card_bot] at hh
    exact hne (card_eq_one.mp hh)
  have hn : normalizer (T : Set B) ≤ normalizer (E : Set B) := by
    change normalizer ((P : Subgroup A).map f : Set B) ≤ _
    rw [←P.normalizer_map_surjective f hf]
    exact (map_mono hnorm).trans (D.le_normalizer_map f)
  exact hc.trans (hB T E inferInstance (map_mono hDP) he hn)

variable {K : Type*} [Field K] [Finite K]
private instance (J : HermitianForm 3 K) : Finite (ProjectiveSpecialUnitaryMatrixGroup J) :=
  Finite.of_surjective J.specialToProjective J.specialToProjective_surjective

private theorem standard [CharP K 2] (J : HermitianForm 3 K)
    (hJ : J.form = !![0,0,1;0,1,0;1,0,0]) {n : ℕ} (hn : 2 ≤ n)
    (hc : Nat.card K = (2^n)^2) (hf : Nat.card {x : K // J.conj x = x} = 2^n)
    (P : Sylow 2 (ProjectiveSpecialUnitaryMatrixGroup J))
    (D : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)) [IsElementaryAbelian 2 D]
    (hDP : D ≤ P) (hne : D ≠ ⊥)
    (hnorm : normalizer (P : Set (ProjectiveSpecialUnitaryMatrixGroup J)) ≤ normalizer (D : Set (ProjectiveSpecialUnitaryMatrixGroup J))) : Nat.card D = 2^n := by
  let R := EvenTwoRank.rootSylow J hJ (by omega) hc hf
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq (ProjectiveSpecialUnitaryMatrixGroup J) P R
  let c := (MulAut.conj g).toMonoidHom
  have hP : (P : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)).map c = R :=
    congrArg Sylow.toSubgroup hg
  let E := D.map c
  let : IsElementaryAbelian 2 E := IsElementaryAbelian.map c
  have hER : E ≤ R := hP ▸ map_mono hDP
  have hEO : E ≤ omegaOneAmbient (R : Subgroup _) := by
    rw [←omegaOneAmbient_eq_self E]
    exact omegaOneAmbient_mono hER
  have hEZ : E ≤ centralImage J hJ := by
    have he := (SylowOmega.projective_sylow_omega J hn hc hf hJ R).1
    rw [he] at hEO
    exact hEO.trans_eq (NormalizedRootCentralizers.root_center J hn hc hf hJ)
  have hN : normalizer (R : Set (ProjectiveSpecialUnitaryMatrixGroup J)) ≤
      normalizer (E : Set (ProjectiveSpecialUnitaryMatrixGroup J)) := by
    change normalizer ((R : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)) : Set (ProjectiveSpecialUnitaryMatrixGroup J)) ≤ _
    rw [←hP,←P.normalizer_map_surjective c (MulAut.conj g).surjective]
    exact (map_mono hnorm).trans (D.le_normalizer_map c)
  have ht : projectiveTorus J hJ ≤ normalizer (E : Set (ProjectiveSpecialUnitaryMatrixGroup J)) :=
    (NormalizedRootCentralizers.torus_normalizes_root J hJ).trans hN
  have hneE : E ≠ ⊥ := fun he => hne
    ((map_eq_bot_iff_of_injective D (MulAut.conj g).injective).mp he)
  have he := (central_irreducible J hJ hc hf E hEZ ht).resolve_left hneE
  calc Nat.card D = Nat.card E := (card_map_of_injective (MulAut.conj g).injective).symm
       _ = 2^n := by rw [he]; exact centralImage_card J hJ hf

/-- The full Sylow normalizer forces a nonzero elementary subgroup in PSU₃
of even parameter greater than two to have the full center order. -/
theorem projective (J : HermitianForm 3 K) {n : ℕ} (hn : 2 ≤ n)
    (hc : Nat.card K = (2^n)^2) (hconj : ∀ x, J.conj x = x^(2^n))
    (P : Sylow 2 (ProjectiveSpecialUnitaryMatrixGroup J))
    (D : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)) [IsElementaryAbelian 2 D]
    (hDP : D ≤ P) (hne : D ≠ ⊥)
    (hnorm : normalizer (P : Set (ProjectiveSpecialUnitaryMatrixGroup J)) ≤ normalizer (D : Set (ProjectiveSpecialUnitaryMatrixGroup J))) : Nat.card D = 2^n := by
  let : CharP K 2 := by
    let := Fintype.ofFinite K
    apply charP_of_card_eq_prime_pow (p := 2) (f := n*2)
    simpa only [pow_mul,Nat.card_eq_fintype_card] using hc
  have hf := FiniteField.card_fixed_of_quadratic_frobenius J.conj 2 n (by omega) hc hconj
  let e := Classical.choice (exists_projectiveEquiv J (2^n) hc hf)
  exact card_transport e.toMonoidHom e.surjective P
    (e.injective.comp (P : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)).subtype_injective)
    (fun T E hE hET hneE hN => @standard K _ _ _ (standardForm J) rfl n hn hc hf T E hE hET hneE hN)
    D hDP hne hnorm

/-- The scalar projection preserves the result in the full SU₃ carrier. -/
theorem special (J : HermitianForm 3 K) {n : ℕ} (hn : 2 ≤ n)
    (hc : Nat.card K = (2^n)^2) (hconj : ∀ x, J.conj x = x^(2^n))
    (P : Sylow 2 J.specialSubgroup)
    (D : Subgroup J.specialSubgroup) [IsElementaryAbelian 2 D]
    (hDP : D ≤ P) (hne : D ≠ ⊥)
    (hnorm : normalizer (P : Set J.specialSubgroup) ≤ normalizer (D : Set J.specialSubgroup)) :
    Nat.card D = 2^n := by
  exact card_transport J.specialToProjective J.specialToProjective_surjective P
    (SylowOmega.specialProjection_injective_on_sylow J P)
    (fun T E hE hET hneE hN => @projective K _ _ J n hn hc hconj T E hE hET hneE hN)
    D hDP hne hnorm

/-- The original marked projective group retains its whole Sylow omega. -/
theorem of_projective_equiv {A : Type*} [Group A] [Finite A]
    (J : HermitianForm 3 K) {n : ℕ} (hn : 2 ≤ n)
    (hc : Nat.card K = (2^n)^2) (hconj : ∀ x, J.conj x = x^(2^n))
    (e : A ≃* ProjectiveSpecialUnitaryMatrixGroup J)
    (P : Sylow 2 A) (D : Subgroup A) [IsElementaryAbelian 2 D]
    (hDP : D ≤ P) (hne : D ≠ ⊥)
    (hnorm : normalizer (P : Set A) ≤ normalizer (D : Set A)) :
    D = omegaOneAmbient (P : Subgroup A) ∧ Nat.card D = 2^n := by
  have hd := card_transport e.toMonoidHom e.surjective P
    (e.injective.comp (P : Subgroup A).subtype_injective)
    (fun T E hE hET hneE hN => @projective K _ _ J n hn hc hconj T E hE hET hneE hN)
    D hDP hne hnorm
  have hf := FiniteField.card_fixed_of_quadratic_frobenius J.conj 2 n (by omega) hc hconj
  let f := Classical.choice (exists_projectiveEquiv J (2^n) hc hf)
  have ho := SylowOmega.omega_of_projective_equiv (standardForm J) hn hc hf rfl (e.trans f) P
  refine ⟨eq_of_le_of_card_ge ?_ (by rw [hd,ho.2.2]),hd⟩
  rw [←omegaOneAmbient_eq_self D]
  exact omegaOneAmbient_mono hDP

/-- The same equality for an original SU₃ marking, including its scalar center. -/
theorem of_special_equiv {A : Type*} [Group A] [Finite A]
    (J : HermitianForm 3 K) {n : ℕ} (hn : 2 ≤ n)
    (hc : Nat.card K = (2^n)^2) (hconj : ∀ x, J.conj x = x^(2^n))
    (e : A ≃* J.specialSubgroup)
    (P : Sylow 2 A) (D : Subgroup A) [IsElementaryAbelian 2 D]
    (hDP : D ≤ P) (hne : D ≠ ⊥)
    (hnorm : normalizer (P : Set A) ≤ normalizer (D : Set A)) :
    D = omegaOneAmbient (P : Subgroup A) ∧ Nat.card D = 2^n := by
  have hd := card_transport e.toMonoidHom e.surjective P
    (e.injective.comp (P : Subgroup A).subtype_injective)
    (fun T E hE hET hneE hN => @special K _ _ J n hn hc hconj T E hE hET hneE hN)
    D hDP hne hnorm
  have hf := FiniteField.card_fixed_of_quadratic_frobenius J.conj 2 n (by omega) hc hconj
  obtain ⟨C,hC⟩ := exists_standard_basis J (2^n) hc hf
  let f := specialEquiv J C hC
  have ho := SylowOmega.omega_of_special_equiv (standardForm J) hn hc hf rfl (e.trans f) P
  refine ⟨eq_of_le_of_card_ge ?_ (by rw [hd,ho.2.2]),hd⟩
  rw [←omegaOneAmbient_eq_self D]
  exact omegaOneAmbient_mono hDP

end BenderSuzuki.MatrixGroups.HermitianForm.BorelElementary
