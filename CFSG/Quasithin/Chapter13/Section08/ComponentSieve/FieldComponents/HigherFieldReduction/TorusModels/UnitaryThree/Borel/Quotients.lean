module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.TorusModels.UnitaryThree.Borel.Geometry

/-!
# Full torus coordinates on the unitary Borel quotient

The actual torus inclusion induces the isomorphism with B₀/O₂(B₀).
For SU₃ its coordinates are Eˣ. For PSU₃ they are Eˣ modulo the norm-one
cube roots of unity. The formulas on torus matrices determine the induced
quotient action. Transport uses the same ambient equivalence which carries
the specified Sylow subgroup to the standard root range.

Source: Aschbacher–Smith, proof of 13.8.20, printed p.954.
-/

public section
open Subgroup BenderSuzuki.MatrixGroups BenderSuzuki.External
open HermitianForm.BorelTorus
open CFSG.Quasithin.ChapterF.Source.Unitary
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.TorusModels.UnitaryThree
variable {E : Type*} [Field E] [Finite E] (J : HermitianForm 3 E)
variable (n : ℕ) (hn : 0 < n) (hcard : Nat.card E = (2 ^ n) ^ 2)
variable (hconj : ∀ x : E, J.conj x = x ^ (2 ^ n))
variable (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])

/-- The full standard SU₃ Borel quotient has coordinates in Eˣ. -/
noncomputable def specialBorelQuotientEquiv :
    specialBorel J hJ ⧸ pCore 2 (specialBorel J hJ) ≃* Eˣ :=
  (quotientTorusEquiv (specialBorel J hJ) (specialRoot J hJ) (specialTorus J hJ) le_sup_right
    (specialBorel_twoCore J n hn hcard hconj hJ)
    (suRoot_disjoint_torus J hJ) rfl).trans (specialEquiv J hJ).symm

/-- Compatibility with the actual special torus inclusion and quotient map. -/
theorem specialBorelQuotientEquiv_torus (k : Eˣ) :
    specialBorelQuotientEquiv J n hn hcard hconj hJ
      (QuotientGroup.mk' (pCore 2 (specialBorel J hJ)) (specialTorusIn J hJ k)) = k := by
  exact (congrArg (specialEquiv J hJ).symm
    (quotientTorusEquiv_torus (specialBorel J hJ) (specialRoot J hJ) (specialTorus J hJ)
      le_sup_right (specialBorel_twoCore J n hn hcard hconj hJ)
      (suRoot_disjoint_torus J hJ) rfl (specialEquiv J hJ k))).trans
    ((specialEquiv J hJ).symm_apply_apply k)

/-- The full standard PSU₃ Borel quotient retains the exact scalar kernel. -/
noncomputable def projectiveBorelQuotientEquiv :
    projectiveBorel J hJ ⧸ pCore 2 (projectiveBorel J hJ) ≃*
      Eˣ ⧸ (HermitianForm.EvenInner.normOne J ⊓ rootsOfUnity 3 E) :=
  (quotientTorusEquiv (projectiveBorel J hJ) (projectiveRoot J hJ) (projectiveTorus J hJ) le_sup_right
    (projectiveBorel_twoCore J n hn hcard hconj hJ)
    (projectiveRoot_disjoint_torus J n hn hcard hconj hJ) rfl).trans
    (projectiveEquiv J hJ).symm

/-- Compatibility with the actual projective torus and its scalar quotient. -/
theorem projectiveBorelQuotientEquiv_torus (k : Eˣ) :
    projectiveBorelQuotientEquiv J n hn hcard hconj hJ
      (QuotientGroup.mk' (pCore 2 (projectiveBorel J hJ)) (projectiveTorusIn J hJ k)) =
      QuotientGroup.mk' (HermitianForm.EvenInner.normOne J ⊓ rootsOfUnity 3 E) k := by
  exact (congrArg (projectiveEquiv J hJ).symm
    (quotientTorusEquiv_torus (projectiveBorel J hJ) (projectiveRoot J hJ) (projectiveTorus J hJ)
      le_sup_right (projectiveBorel_twoCore J n hn hcard hconj hJ)
      (projectiveRoot_disjoint_torus J n hn hcard hconj hJ) rfl
      (projectiveEquiv J hJ (QuotientGroup.mk' _ k)))).trans
    ((projectiveEquiv J hJ).symm_apply_apply (QuotientGroup.mk' _ k))

include n hn hcard hconj in
/-- Full quotient coordinates for any specified special Sylow, compatible
with the torus transported by the same ambient model equivalence. -/
theorem su_borel_quotient (S : Sylow 2 J.specialSubgroup) :
    ∃ (e : J.specialSubgroup ≃* (FormTransport.standardForm J).specialSubgroup)
      (_hS : (S : Subgroup J.specialSubgroup).map e.toMonoidHom =
        specialRoot (FormTransport.standardForm J) rfl)
      (hB : (normalizer (S : Set J.specialSubgroup)).map e.toMonoidHom =
        specialBorel (FormTransport.standardForm J) rfl)
      (q : normalizer (S : Set J.specialSubgroup) ⧸
        pCore 2 (normalizer (S : Set J.specialSubgroup)) ≃* Eˣ),
      ∀ k : Eˣ, q (QuotientGroup.mk' _
        ((subgroupEquiv e hB).symm (specialTorusIn (FormTransport.standardForm J) rfl k))) = k := by
  obtain ⟨e, hS, hB⟩ := su_borel_model J n hn hcard hconj S
  let b := subgroupEquiv e hB
  let q := (twoCoreQuotientEquiv b).trans
    (specialBorelQuotientEquiv (FormTransport.standardForm J) n hn hcard hconj rfl)
  refine ⟨e, hS, hB, q, ?_⟩
  intro k
  change specialBorelQuotientEquiv (FormTransport.standardForm J) n hn hcard hconj rfl
    (twoCoreQuotientEquiv b (QuotientGroup.mk' _ (b.symm _))) = k
  rw [twoCoreQuotientEquiv_mk, MulEquiv.apply_symm_apply]
  exact specialBorelQuotientEquiv_torus (FormTransport.standardForm J) n hn hcard hconj rfl k

include n hn hcard hconj in
/-- Full quotient coordinates for any specified projective Sylow, with
compatibility for every transported projective torus matrix. -/
theorem psu_borel_quotient (S : Sylow 2 (ProjectiveSpecialUnitaryMatrixGroup J)) :
    ∃ (e : ProjectiveSpecialUnitaryMatrixGroup J ≃*
        ProjectiveSpecialUnitaryMatrixGroup (FormTransport.standardForm J))
      (_hS : (S : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)).map e.toMonoidHom =
        projectiveRoot (FormTransport.standardForm J) rfl)
      (hB : (normalizer (S : Set (ProjectiveSpecialUnitaryMatrixGroup J))).map e.toMonoidHom =
        projectiveBorel (FormTransport.standardForm J) rfl)
      (q : normalizer (S : Set (ProjectiveSpecialUnitaryMatrixGroup J)) ⧸
        pCore 2 (normalizer (S : Set (ProjectiveSpecialUnitaryMatrixGroup J))) ≃*
        Eˣ ⧸ (HermitianForm.EvenInner.normOne (FormTransport.standardForm J) ⊓ rootsOfUnity 3 E)),
      ∀ k : Eˣ, q (QuotientGroup.mk' _
        ((subgroupEquiv e hB).symm (projectiveTorusIn (FormTransport.standardForm J) rfl k))) =
        QuotientGroup.mk' (HermitianForm.EvenInner.normOne (FormTransport.standardForm J) ⊓
          rootsOfUnity 3 E) k := by
  obtain ⟨e, hS, hB⟩ := psu_borel_model J n hn hcard hconj S
  let b := subgroupEquiv e hB
  let q := (twoCoreQuotientEquiv b).trans
    (projectiveBorelQuotientEquiv (FormTransport.standardForm J) n hn hcard hconj rfl)
  refine ⟨e, hS, hB, q, ?_⟩
  intro k
  change projectiveBorelQuotientEquiv (FormTransport.standardForm J) n hn hcard hconj rfl
    (twoCoreQuotientEquiv b (QuotientGroup.mk' _ (b.symm _))) = _
  rw [twoCoreQuotientEquiv_mk, MulEquiv.apply_symm_apply]
  exact projectiveBorelQuotientEquiv_torus (FormTransport.standardForm J) n hn hcard hconj rfl k

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.TorusModels.UnitaryThree
