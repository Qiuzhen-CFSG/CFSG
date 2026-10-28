module
public import CFSG.Quasithin.ChapterF.Section01.SourceCartan.Unitary.Reduction
public import CFSG.Quasithin.ChapterF.Section01.RankOneBorels.Unitary.FieldParameters
public import Theory.SpecificGroups.SU3.EvenSemilinear
public import Theory.SpecificGroups.SU3.Quasisimplicity
public import Theory.SpecificGroups.SU3.BorelTorus.SemilinearActors.TorusAction
public import Theory.SpecificGroups.SU3.BorelTorus.SemilinearActors.RootNormalizer

/-!
# Cartan actions from the concrete unitary semilinear formulas

A root-preserving semilinear automorphism has triangular unitary part.
Its torus displacement lies in the root group. If it also preserves the
torus, trivial root–torus intersection gives the exact field action, in SU₃
or the actual projective image respectively. Thus the quadratic identity
passes to the literal torus homomorphism, keeping the projective cubic kernel.

The finite-field quadratic assertion is an explicit remaining premise.
The projective semilinear coverage and its simplicity premise are discharged.
Source: Aschbacher–Smith F.1.3(5), printed p.260, and GLS3 2.5.12.
-/

public section
open Subgroup BenderSuzuki.MatrixGroups BenderSuzuki.External
open BenderSuzuki.MatrixGroups.HermitianForm
open BenderSuzuki.MatrixGroups.HermitianForm.BorelTorus
open BenderSuzuki.MatrixGroups.HermitianForm.BorelTorus.SemilinearActors
namespace CFSG.Quasithin.ChapterF.Source.Unitary

private theorem fixes_of_field_action {G F : Type*} [Group G] [Field F]
    (t : Fˣ →* G) (a : MulAut G) (σ : F ≃+* F)
    (hact : ∀ k, a (t k) = t (Units.map σ.toMonoidHom k))
    (hfield : (∀ k : Fˣ,
      t (Units.map σ.toMonoidHom (Units.map σ.toMonoidHom k * k⁻¹)) =
        t (Units.map σ.toMonoidHom k * k⁻¹)) →
      ∀ k : Fˣ, t (Units.map σ.toMonoidHom k) = t k)
    (hq : ∀ x ∈ t.range, a (a x * x⁻¹) = a x * x⁻¹) :
    ∀ x ∈ t.range, a x = x := by
  have hd (k : Fˣ) : t (Units.map σ.toMonoidHom k * k⁻¹) = a (t k) * (t k)⁻¹ := by
    rw [map_mul, map_inv, hact]
  have hf := hfield (fun k => by
    calc
      _ = a (t (Units.map σ.toMonoidHom k * k⁻¹)) := (hact _).symm
      _ = a (a (t k) * (t k)⁻¹) := congrArg a (hd k)
      _ = a (t k) * (t k)⁻¹ := hq _ ⟨k,rfl⟩
      _ = _ := (hd k).symm)
  rintro x ⟨k,rfl⟩
  exact (hact k).trans (hf k)

variable {F : Type*} [Field F] [Finite F] (J : HermitianForm 3 F)
    (hJ : J.form = !![0,0,1;0,1,0;1,0,0])

/-- The exact special-unitary pair assertion from matrix semilinearity and
quadratic rigidity of the full multiplicative torus. Both premises are explicit. -/
theorem special_pairRigidity_of_semilinear_and_field {q : ℕ}
    (hcard : Nat.card F = q ^ 2) (hfixed : Nat.card {x : F // J.conj x = x} = q)
    (hcoverage : ∀ a : MulAut J.specialSubgroup,
      ∃ σ : F ≃+* F, J.HasSpecialUnitarySemilinearForm a σ)
    (hfield : ∀ σ : F ≃+* F,
      (∀ k : Fˣ, hermitianTorusSU J hJ
          (Units.map σ.toMonoidHom (Units.map σ.toMonoidHom k * k⁻¹)) =
        hermitianTorusSU J hJ (Units.map σ.toMonoidHom k * k⁻¹)) →
      ∀ k : Fˣ, hermitianTorusSU J hJ (Units.map σ.toMonoidHom k) = hermitianTorusSU J hJ k) :
    PairRigidity (specialRoot J hJ) (specialTorus J hJ) := by
  intro a _hao haU haD hq
  obtain ⟨σ, u, hu⟩ := hcoverage a
  obtain ⟨h10,h20,h21⟩ := special_semilinear_upper J hJ hcard hfixed a σ u hu haU
  have hact (k : Fˣ) : a (hermitianTorusSU J hJ k) =
      hermitianTorusSU J hJ (Units.map σ.toMonoidHom k) := by
    apply mul_inv_eq_one.mp
    apply Subgroup.disjoint_def.mp (special_root_disjoint_torus J hJ)
    · exact special_semilinear_torus_displacement J hJ a σ u h10 h20 h21 hu k
    · exact (specialTorus J hJ).mul_mem
        (haD ▸ mem_map_of_mem a.toMonoidHom (show hermitianTorusSU J hJ k ∈ specialTorus J hJ from ⟨k,rfl⟩))
        ((specialTorus J hJ).inv_mem ⟨_,rfl⟩)
  exact fixes_of_field_action (hermitianTorusSU J hJ) a σ hact (hfield σ) hq

/-- For n ≥ 2, the exact projective pair assertion has only its finite-field
quadratic premise left. Simplicity follows from the actual model theorem. -/
theorem projective_pairRigidity_of_field {n : ℕ} (hn : 2 ≤ n)
    (hcard : Nat.card F = (2 ^ n) ^ 2) (hconj : ∀ x, J.conj x = x ^ (2 ^ n))
    (hfield : ∀ σ : F ≃+* F,
      (∀ k : Fˣ, hermitianTorusPSU J hJ
          (Units.map σ.toMonoidHom (Units.map σ.toMonoidHom k * k⁻¹)) =
        hermitianTorusPSU J hJ (Units.map σ.toMonoidHom k * k⁻¹)) →
      ∀ k : Fˣ, hermitianTorusPSU J hJ (Units.map σ.toMonoidHom k) = hermitianTorusPSU J hJ k) :
    PairRigidity (projectiveRoot J hJ) (projectiveTorus J hJ) := by
  have hfixed := fixed_card J n (by omega) hcard hconj
  have hq : 2 < 2 ^ n := lt_of_lt_of_le (by decide : 2 < 2 ^ 2)
    (Nat.pow_le_pow_right (by decide) hn)
  let : IsSimpleGroup (ProjectiveSpecialUnitaryMatrixGroup J) :=
    huppert_II_10_13 J (2 ^ n) hq hcard hfixed
  intro a _hao haU haD hquad
  obtain ⟨σ, u, hu⟩ := EvenSemilinear.semilinear_coverage J hJ hn hcard hconj a
  obtain ⟨h10,h20,h21⟩ := projective_semilinear_upper J hJ hcard hfixed a σ u hu haU
  have hact (k : Fˣ) : a (hermitianTorusPSU J hJ k) =
      hermitianTorusPSU J hJ (Units.map σ.toMonoidHom k) := by
    apply mul_inv_eq_one.mp
    apply Subgroup.disjoint_def.mp (projective_root_disjoint_torus J hJ)
    · exact projective_semilinear_torus_displacement J hJ a σ u h10 h20 h21 hu k
    · exact (projectiveTorus J hJ).mul_mem
        (haD ▸ mem_map_of_mem a.toMonoidHom (show hermitianTorusPSU J hJ k ∈ projectiveTorus J hJ from ⟨k,rfl⟩))
        ((projectiveTorus J hJ).inv_mem ⟨_,rfl⟩)
  exact fixes_of_field_action (hermitianTorusPSU J hJ) a σ hact (hfield σ) hquad

end CFSG.Quasithin.ChapterF.Source.Unitary
