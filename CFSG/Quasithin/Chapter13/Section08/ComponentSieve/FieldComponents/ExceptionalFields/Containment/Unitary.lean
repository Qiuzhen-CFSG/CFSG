module

public import CFSG.Quasithin.Chapter13.Section08.SourceDefs
public import Theory.GroupTheory.PPrimeCoreReduction
public import Theory.GroupTheory.PPrimeCoreSurjection
public import Theory.SpecificGroups.SU3.UnitaryEight.CubicSylow

/-!
# The external-L₁ unitary branch: quotient and cubic obstruction

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, proof of
13.8.20, printed p.955 (PDF p.972); A.3.16–18, printed pp.51–53.

The chapter's quotient H/O₂(H) and the appendix's quotient H/O₃′(H)
are identified when the former has a self-centralizing simple component
of order divisible by three. The comparison commutes with the actual
quotient maps. Conjugation on that component, transported through an
actual PSU₃(8) isomorphism, is faithful when its centralizer is trivial.
The intrinsic cubic obstruction then applies to the actual Sylow arrangement.

These results are preparatory, not the complete external-L₁ contradiction.
The remaining assembly must construct the outside order-three subgroup from
the T-invariant marked L₀ and L₁,+ sections, and apply A.3.18(2) to put its
action in the diagonal image, excluding the nonsplit diagonal-field extension.
A.3.18(3b) is a special-unitary statement and is not substituted for (2).
Neither an arbitrary E₉ subgroup nor its mere T-invariance supplies this step.
-/

public section
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.ExceptionalFields.Containment.Unitary
open Subgroup BenderSuzuki.MatrixGroups
open scoped Pointwise
variable {G : Type*} [Group G] [Finite G]

/-- The appendix and chapter cores coincide under the actual almost-simple
quotient hypotheses. Normality here is inside H/O₂(H), not in G. -/
theorem threePrimeCore_eq_twoCore (H K : Subgroup G)
    [(Source.starImage H K).Normal] [IsSimpleGroup (Source.starImage H K)]
    (hthree : 3 ∣ Nat.card (Source.starImage H K))
    (hcentralizer : centralizer (Source.starImage H K : Set (Source.Hstar H)) ≤
      Source.starImage H K) : pPrimeCore 3 H = pCore 2 H := by
  have hcore : pPrimeCore 3 (Source.Hstar H) = ⊥ :=
    Theory.GroupTheory.pPrimeCore_eq_bot_of_selfCentralizing (Source.starImage H K)
      (Theory.GroupTheory.pPrimeCore_eq_bot_of_simple hthree) hcentralizer
  have hcop : Nat.Coprime 3 (Nat.card (pCore 2 H)) := by
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp (pCore_isPGroup (p := 2) (G := H))
    rw [hn]
    exact (show Nat.Coprime 3 2 by decide).pow_right n
  have h := pPrimeCore_comap_eq_of_surjective_coprime 3
    (QuotientGroup.mk' (pCore 2 H)) (QuotientGroup.mk'_surjective _) (by
      rwa [QuotientGroup.ker_mk'])
  rw [hcore] at h
  change (QuotientGroup.mk' (pCore 2 H)).ker = pPrimeCore 3 H at h
  rw [QuotientGroup.ker_mk'] at h
  exact h.symm

/-- The genuine quotient comparison, compatible with each element of H. -/
theorem quotient_comparison (H K : Subgroup G)
    [(Source.starImage H K).Normal] [IsSimpleGroup (Source.starImage H K)]
    (hthree : 3 ∣ Nat.card (Source.starImage H K))
    (hcentralizer : centralizer (Source.starImage H K : Set (Source.Hstar H)) ≤
      Source.starImage H K) :
    ∃ e : (H ⧸ pPrimeCore 3 H) ≃* Source.Hstar H,
      ∀ h : H, e (QuotientGroup.mk' (pPrimeCore 3 H) h) =
        QuotientGroup.mk' (pCore 2 H) h := by
  refine ⟨QuotientGroup.quotientMulEquivOfEq
    (threePrimeCore_eq_twoCore H K hthree hcentralizer), ?_⟩
  intro h
  rfl

variable {E : Type*} [Field E]

/-- Conjugation on the actual starred component in the prescribed matrix
coordinates. This is an action map, not a separate model-family label. -/
def componentAction (H K : Subgroup G) [(Source.starImage H K).Normal]
    (J : HermitianForm 3 E)
    (e : Source.starImage H K ≃* ProjectiveSpecialUnitaryMatrixGroup J) :
    Source.Hstar H →* MulAut (ProjectiveSpecialUnitaryMatrixGroup J) :=
  (MulAut.congr e).toMonoidHom.comp MulAut.conjNormal

omit [Finite G] in
/-- Trivial component centralizer proves faithfulness of the actual action. -/
theorem componentAction_injective (H K : Subgroup G)
    [(Source.starImage H K).Normal] (J : HermitianForm 3 E)
    (e : Source.starImage H K ≃* ProjectiveSpecialUnitaryMatrixGroup J)
    (hC : centralizer (Source.starImage H K : Set (Source.Hstar H)) = ⊥) :
    Function.Injective (componentAction H K J e) := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply eq_bot_iff.mpr
  intro x hx
  change MulAut.congr e (MulAut.conjNormal x) = 1 at hx
  have hx' : (MulAut.conjNormal x : MulAut (Source.starImage H K)) = 1 :=
    (MulAut.congr e).injective (show MulAut.congr e (MulAut.conjNormal x) =
      MulAut.congr e 1 by simpa only [map_one] using hx)
  have hc : x ∈ centralizer (Source.starImage H K : Set (Source.Hstar H)) := by
    rw [mem_centralizer_iff]
    intro k hk
    have hh := congrArg (fun a : MulAut (Source.starImage H K) =>
      (a ⟨k, hk⟩ : Source.Hstar H)) hx'
    change x * k * x⁻¹ = k at hh
    exact (mul_inv_eq_iff_eq_mul.mp hh).symm
  rwa [hC] at hc

omit [Finite G] in
/-- The restriction of the action to the component is its inner action. -/
theorem componentAction_component (H K : Subgroup G)
    [(Source.starImage H K).Normal] (J : HermitianForm 3 E)
    (e : Source.starImage H K ≃* ProjectiveSpecialUnitaryMatrixGroup J)
    (k : Source.starImage H K) :
    componentAction H K J e k = MulAut.conj (e k) := by
  change MulAut.congr e (MulAut.conjNormal (k : Source.Hstar H)) = _
  rw [MulAut.conjNormal_val]
  ext y
  simp [MulAut.congr_apply, MulAut.conj_apply]

omit [Finite G] in
/-- An element outside the actual component acts outerly when that action
is faithful; no outerness certificate is assumed. -/
theorem componentAction_outer (H K : Subgroup G)
    [(Source.starImage H K).Normal] (J : HermitianForm 3 E)
    (e : Source.starImage H K ≃* ProjectiveSpecialUnitaryMatrixGroup J)
    (hC : centralizer (Source.starImage H K : Set (Source.Hstar H)) = ⊥)
    (x : Source.Hstar H) (hx : x ∉ Source.starImage H K) :
    componentAction H K J e x ∉
      MulAut.innerSubgroup (ProjectiveSpecialUnitaryMatrixGroup J) := by
  rintro ⟨y, hy⟩
  have he : componentAction H K J e (e.symm y : Source.starImage H K) =
      componentAction H K J e x := by
    rw [componentAction_component, e.apply_symm_apply]
    exact hy
  exact hx ((componentAction_injective H K J e hC he) ▸ (e.symm y).property)

variable [Finite E]

/-- The source's cubic obstruction after its cubic has been constructed and
placed in the diagonal image. The Sylow arrangement, model, field orders,
and the universal automorphism premises are explicit. This conditional lemma
does not assert the missing A.3.18 application or the marked-cubic construction. -/
theorem outside_diagonal_cubic_not_permuting
    (H K T : Subgroup G) [(Source.starImage H K).Normal]
    (J : HermitianForm 3 E) (hJ : J.form = !![0,0,1; 0,1,0; 1,0,0])
    (hcard : Nat.card E = 64) (hfixed : Nat.card {z : E // J.conj z = z} = 8)
    (e : Source.starImage H K ≃* ProjectiveSpecialUnitaryMatrixGroup J)
    (hC : centralizer (Source.starImage H K : Set (Source.Hstar H)) = ⊥)
    (hcoverage : ∀ a : MulAut (ProjectiveSpecialUnitaryMatrixGroup J),
      ∃ σ : E ≃+* E, J.HasUnitarySemilinearForm a σ)
    (hfaithful : ∀ σ : E ≃+* E, J.HasUnitarySemilinearForm 1 σ → σ = 1)
    (S : Sylow 2 (Source.starImage H K))
    (hS : (S : Subgroup (Source.starImage H K)).map (Source.starImage H K).subtype =
      Source.starImage H T ⊓ Source.starImage H K)
    (hT : IsPGroup 2 T)
    (x : Source.Hstar H) (hx : orderOf x = 3) (hxK : x ∉ Source.starImage H K)
    (hdiag : componentAction H K J e x ∈ J.unitaryConjHom.range) :
    ((zpowers x ⊔ Source.starImage H T : Subgroup (Source.Hstar H)) : Set (Source.Hstar H)) ≠
      (zpowers x : Set (Source.Hstar H)) * Source.starImage H T := by
  exact HermitianForm.UnitaryEight.external_diagonal_cubic_not_permuting J hJ hcard hfixed
    hcoverage hfaithful (Source.starImage H K) (Source.starImage H T) e S hS
    (hT.comap_subtype.map _) (componentAction H K J e)
    (componentAction_injective H K J e hC) x hx hxK hdiag
    (componentAction_outer H K J e hC x hxK)

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.ExceptionalFields.Containment.Unitary
