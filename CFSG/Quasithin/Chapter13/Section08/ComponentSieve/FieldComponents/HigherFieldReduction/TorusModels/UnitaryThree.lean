module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.Residuals
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.TorusModels.UnitaryThree.Setup
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.TorusModels.UnitaryThree.Borel
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.TorusModels.UnitaryThree.Actors
public import Theory.SpecificGroups.SU3.BorelTorus.GraphAction
public import Theory.GroupTheory.PResidual.FiniteImage
public import Theory.GroupTheory.SylowKernelCore
public import Theory.GroupAction.ModelConjugation.InnerImage

/-!
# The unitary Borel and automorphism calculation for 13.8.20

For either SU₃ or its actual projective image over a matrix field of order
(2ⁿ)², n > 1, the normalizer B₀ of any specified Sylow two-subgroup S is
its own two-residual, with two-core S. The imported quotient equivalences
identify B₀/O₂(B₀) with the full matrix-field unit group, respectively its
quotient by the norm-one cube roots, compatibly with the torus inclusion.

An actor in a two-subgroup containing the inner image of S, and stabilizing
S, fixes O³(B)O₂(B)/O₂(B) exactly when it is in that inner image, unless
n = 3. Transport first aligns the actual Sylow and its Borel with the
standard Hermitian model. The semilinear calculation then removes the
field parameter and the odd diagonal factor. The only remaining explicit
classification input is semilinear coverage of the standard model,
the matrix form of GLS3, Theorem 2.5.12(a,d,f) and Section 2.7; all Borel,
quotient and torus-action premises are discharged here or in the imported
calculations. Arbitrary two-power actors are allowed.

The sole unitary alternative is (S)U₃(8). The imported graph calculation
also proves that the constructed graph actor fixes the full torus's
three-residual exactly at this degree. On lifting to an ambient conjugation
action, the fixer includes the actual kernel C_T(K), with only relative
normalization of K required.

Source: Aschbacher–Smith, proof of 13.8.20, printed p.954 (PDF p.971).
-/

public section
open Subgroup BenderSuzuki.MatrixGroups
open HermitianForm.BorelTorus
open CFSG.Quasithin.ChapterF.Source.Unitary
open Theory.GroupAction.ModelConjugation
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.TorusModels.UnitaryThree
variable {D K : Type*} [Group D] [Group K]

/-- The source residual-fixer condition is invariant under a genuine model equivalence. -/
theorem fixesThreeTorus_map_iff [Finite D] (e : D ≃* K) (B : Subgroup D) (a : MulAut D) :
    FixesThreeTorus (B.map e.toMonoidHom) (MulAut.congr e a) ↔ FixesThreeTorus B a := by
  have hR : residualIn 3 (B.map e.toMonoidHom) = (residualIn 3 B).map e.toMonoidHom :=
    (map_embedded_pResidual 3 B e.toMonoidHom).symm
  have hU : (B.map e.toMonoidHom).pCoreIn 2 = (B.pCoreIn 2).map e.toMonoidHom :=
    (map_pCoreIn_of_injective 2 B e.toMonoidHom e.injective).symm
  unfold FixesThreeTorus
  rw [hR, hU, ← Subgroup.map_sup]
  constructor
  · intro h x hx
    have hh := h (e x) (mem_map_of_mem e.toMonoidHom hx)
    have he : (MulAut.congr e a) (e x) * (e x)⁻¹ = e (a x * x⁻¹) := by
      simp [MulAut.congr]
    rw [he] at hh
    exact (mem_map_iff_mem e.injective).mp hh
  · intro h y hy
    obtain ⟨x, hx, rfl⟩ := hy
    simpa [MulAut.congr] using mem_map_of_mem e.toMonoidHom (h x hx)

private theorem transport_calculation [Finite D]
    (e : D ≃* K) (B U : Subgroup D) (C V : Subgroup K)
    (hB : B.map e.toMonoidHom = C) (hU : U.map e.toMonoidHom = V)
    (hcalc : ∀ (A : Subgroup (MulAut K)), IsPGroup 2 A → V.map MulAut.conj ≤ A →
      ∀ a ∈ A, V.map a.toMonoidHom = V → (FixesThreeTorus C a ↔ a ∈ V.map MulAut.conj))
    (A : Subgroup (MulAut D)) (hA : IsPGroup 2 A) (hUA : U.map MulAut.conj ≤ A)
    (a : MulAut D) (ha : a ∈ A) (hstable : U.map a.toMonoidHom = U) :
    FixesThreeTorus B a ↔ a ∈ U.map MulAut.conj := by
  let A' := A.map (MulAut.congr e).toMonoidHom
  have hinner : V.map MulAut.conj ≤ A' := by
    rw [← hU, ← inner_image_congr]
    exact map_mono hUA
  have hstable' : V.map (MulAut.congr e a).toMonoidHom = V := by
    rw [← hU]
    exact stable_map_congr e U a hstable
  have hh := hcalc A' (hA.map _) hinner (MulAut.congr e a)
    (mem_map_of_mem _ ha) hstable'
  rw [← hB, fixesThreeTorus_map_iff, ← hU, ← inner_image_congr] at hh
  exact hh.trans (mem_map_iff_mem (MulAut.congr e).injective)

variable {E : Type*} [Field E] [Finite E] (J : HermitianForm 3 E)
variable {n : ℕ} (hn : 1 < n) (hcard : Nat.card E = (2 ^ n) ^ 2)
variable (hconj : ∀ x : E, J.conj x = x ^ (2 ^ n))
include hn hcard hconj

/-- Intrinsic SU₃ calculation at any specified Sylow subgroup. The only
classification input is semilinear coverage on the standard Hermitian model. -/
theorem su_sylow_fixesThreeTorus_iff
    (hform : ∀ a : MulAut (FormTransport.standardForm J).specialSubgroup,
      ∃ σ : E ≃+* E, (FormTransport.standardForm J).HasSpecialUnitarySemilinearForm a σ)
    (hn3 : n ≠ 3) (S : Sylow 2 J.specialSubgroup)
    (A : Subgroup (MulAut J.specialSubgroup)) (hA : IsPGroup 2 A)
    (hSA : (S : Subgroup J.specialSubgroup).map MulAut.conj ≤ A)
    (a : MulAut J.specialSubgroup) (ha : a ∈ A)
    (hstable : (S : Subgroup J.specialSubgroup).map a.toMonoidHom = S) :
    FixesThreeTorus (borelResidual (normalizer (S : Set J.specialSubgroup))) a ↔
      a ∈ (S : Subgroup J.specialSubgroup).map MulAut.conj := by
  obtain ⟨e, hS, hB⟩ := su_borel_model J n (by omega) hcard hconj S
  rw [su_borelResidual_eq J n hn hcard hconj S]
  apply transport_calculation e _ _ _ _ hB hS _ A hA hSA a ha hstable
  intro C hC hUC b hb hroot
  exact special_fixesThreeTorus_iff (FormTransport.standardForm J) rfl hn hcard hconj hn3
    _ rfl (specialBorel_twoCore (FormTransport.standardForm J) n (by omega) hcard hconj rfl)
    C hC hUC b hb hroot (hform b)

/-- Intrinsic PSU₃ calculation with the actual projective scalar quotient. -/
theorem psu_sylow_fixesThreeTorus_iff
    (hform : ∀ a : MulAut (ProjectiveSpecialUnitaryMatrixGroup (FormTransport.standardForm J)),
      ∃ σ : E ≃+* E, (FormTransport.standardForm J).HasUnitarySemilinearForm a σ)
    (hn3 : n ≠ 3) (S : Sylow 2 (ProjectiveSpecialUnitaryMatrixGroup J))
    (A : Subgroup (MulAut (ProjectiveSpecialUnitaryMatrixGroup J))) (hA : IsPGroup 2 A)
    (hSA : (S : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)).map MulAut.conj ≤ A)
    (a : MulAut (ProjectiveSpecialUnitaryMatrixGroup J)) (ha : a ∈ A)
    (hstable : (S : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)).map a.toMonoidHom = S) :
    FixesThreeTorus (borelResidual (normalizer (S : Set (ProjectiveSpecialUnitaryMatrixGroup J)))) a ↔
      a ∈ (S : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)).map MulAut.conj := by
  let : Finite (ProjectiveSpecialUnitaryMatrixGroup J) :=
    Finite.of_surjective _ J.specialToProjective_surjective
  obtain ⟨e, hS, hB⟩ := psu_borel_model J n (by omega) hcard hconj S
  rw [psu_borelResidual_eq J n hn hcard hconj S]
  apply transport_calculation e _ _ _ _ hB hS _ A hA hSA a ha hstable
  intro C hC hUC b hb hroot
  exact projective_fixesThreeTorus_iff (FormTransport.standardForm J) rfl hn hcard hconj hn3
    _ rfl (projectiveBorel_twoCore (FormTransport.standardForm J) n (by omega) hcard hconj rfl)
    C hC hUC b hb hroot (hform b)

/-- The source unitary alternative has only fixed-field degree three as a
possible exception, for the special carrier and every chosen Sylow. -/
theorem su_sylow_torus_alternative
    (hform : ∀ a : MulAut (FormTransport.standardForm J).specialSubgroup,
      ∃ σ : E ≃+* E, (FormTransport.standardForm J).HasSpecialUnitarySemilinearForm a σ)
    (S : Sylow 2 J.specialSubgroup)
    (A : Subgroup (MulAut J.specialSubgroup)) (hA : IsPGroup 2 A)
    (hSA : (S : Subgroup J.specialSubgroup).map MulAut.conj ≤ A)
    (hstable : ∀ a ∈ A, (S : Subgroup J.specialSubgroup).map a.toMonoidHom = S) :
    n = 3 ∨ ∀ a ∈ A,
      (FixesThreeTorus (borelResidual (normalizer (S : Set J.specialSubgroup))) a ↔
        a ∈ (S : Subgroup J.specialSubgroup).map MulAut.conj) := by
  by_cases hn3 : n = 3
  · exact Or.inl hn3
  · exact Or.inr fun a ha =>
      su_sylow_fixesThreeTorus_iff J hn hcard hconj hform hn3 S A hA hSA a ha (hstable a ha)

/-- The genuine projective quotient gives the same sole unitary-eight
exception; it introduces no degree-two or degree-six alternative. -/
theorem psu_sylow_torus_alternative
    (hform : ∀ a : MulAut (ProjectiveSpecialUnitaryMatrixGroup (FormTransport.standardForm J)),
      ∃ σ : E ≃+* E, (FormTransport.standardForm J).HasUnitarySemilinearForm a σ)
    (S : Sylow 2 (ProjectiveSpecialUnitaryMatrixGroup J))
    (A : Subgroup (MulAut (ProjectiveSpecialUnitaryMatrixGroup J))) (hA : IsPGroup 2 A)
    (hSA : (S : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)).map MulAut.conj ≤ A)
    (hstable : ∀ a ∈ A,
      (S : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)).map a.toMonoidHom = S) :
    n = 3 ∨ ∀ a ∈ A,
      (FixesThreeTorus
        (borelResidual (normalizer (S : Set (ProjectiveSpecialUnitaryMatrixGroup J)))) a ↔
        a ∈ (S : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)).map MulAut.conj) := by
  by_cases hn3 : n = 3
  · exact Or.inl hn3
  · exact Or.inr fun a ha =>
      psu_sylow_fixesThreeTorus_iff J hn hcard hconj hform hn3 S A hA hSA a ha (hstable a ha)

variable {G : Type*} [Group G]

/-- The ambient SU₃ fixer is the embedded Sylow joined with the actual
conjugation kernel C_T(K). Only normalization of K by T is required. -/
theorem su_conjugation_fixesThreeTorus_iff
    (hform : ∀ a : MulAut (FormTransport.standardForm J).specialSubgroup,
      ∃ σ : E ≃+* E, (FormTransport.standardForm J).HasSpecialUnitarySemilinearForm a σ)
    (hn3 : n ≠ 3) (T K : Subgroup G) (hT : IsPGroup 2 T)
    (hTK : T ≤ normalizer (K : Set G)) (e : K ≃* J.specialSubgroup)
    (S : Sylow 2 J.specialSubgroup)
    (hST : (S : Subgroup J.specialSubgroup).map (K.subtype.comp e.symm.toMonoidHom) ≤ T)
    (hstable : ∀ t : T, (S : Subgroup J.specialSubgroup).map
      (action T K hTK e t).toMonoidHom = S) (t : T) :
    FixesThreeTorus (borelResidual (normalizer (S : Set J.specialSubgroup)))
      (action T K hTK e t) ↔
      (t : G) ∈ (S : Subgroup J.specialSubgroup).map (K.subtype.comp e.symm.toMonoidHom) ⊔
        (T ⊓ centralizer (K : Set G)) := by
  rw [su_sylow_fixesThreeTorus_iff J hn hcard hconj hform hn3 S
    (action T K hTK e).range
    (hT.of_surjective _ (action T K hTK e).rangeRestrict_surjective)
    (inner_le_action_range T K hTK e S hST) _ ⟨t, rfl⟩ (hstable t)]
  exact action_mem_inner_iff T K hTK e S hST t

/-- The ambient PSU₃ formula retains both its genuine model equivalence
and C_T(K); no faithful ambient action is assumed. -/
theorem psu_conjugation_fixesThreeTorus_iff
    (hform : ∀ a : MulAut (ProjectiveSpecialUnitaryMatrixGroup (FormTransport.standardForm J)),
      ∃ σ : E ≃+* E, (FormTransport.standardForm J).HasUnitarySemilinearForm a σ)
    (hn3 : n ≠ 3) (T K : Subgroup G) (hT : IsPGroup 2 T)
    (hTK : T ≤ normalizer (K : Set G)) (e : K ≃* ProjectiveSpecialUnitaryMatrixGroup J)
    (S : Sylow 2 (ProjectiveSpecialUnitaryMatrixGroup J))
    (hST : (S : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)).map
      (K.subtype.comp e.symm.toMonoidHom) ≤ T)
    (hstable : ∀ t : T, (S : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)).map
      (action T K hTK e t).toMonoidHom = S) (t : T) :
    FixesThreeTorus
      (borelResidual (normalizer (S : Set (ProjectiveSpecialUnitaryMatrixGroup J))))
      (action T K hTK e t) ↔
      (t : G) ∈ (S : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)).map
        (K.subtype.comp e.symm.toMonoidHom) ⊔ (T ⊓ centralizer (K : Set G)) := by
  rw [psu_sylow_fixesThreeTorus_iff J hn hcard hconj hform hn3 S
    (action T K hTK e).range
    (hT.of_surjective _ (action T K hTK e).rangeRestrict_surjective)
    (inner_le_action_range T K hTK e S hST) _ ⟨t, rfl⟩ (hstable t)]
  exact action_mem_inner_iff T K hTK e S hST t
end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.TorusModels.UnitaryThree
