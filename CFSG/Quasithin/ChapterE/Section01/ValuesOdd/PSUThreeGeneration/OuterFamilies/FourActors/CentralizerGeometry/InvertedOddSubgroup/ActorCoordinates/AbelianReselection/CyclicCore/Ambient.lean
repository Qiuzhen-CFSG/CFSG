module

public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSUThreeGeneration.OuterFamilies.FourActors.CentralizerGeometry.InvertedOddSubgroup.ActorCoordinates.AbelianReselection.CyclicCore.ModelInput
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSUThreeGeneration.OuterFamilies.ActorGeometry
public import Theory.GroupTheory.CyclicByFourOuterInvolutions.AmbientTransport

/-!
# Ambient transport of the unitary cyclic coordinates

The model premise supplies coordinates in one full automorphism Sylow of the
normalized projective unitary matrix group. Faithful conjugation identifies the
actual generalized Fitting subgroup with the literal inner automorphism subgroup.
Sylow conjugacy and the four normal forms then show that the supplied ambient
Sylow maps onto a full automorphism Sylow, because it contains an outer element.
The centralizing inner involution is the marked half-power: the inner reflection
coset cannot centralize the cyclic generator.

This proves the conditional transport used in the odd unitary branch of
Aschbacher--Smith E.1.14(7), printed p.214, citing Aschbacher (1982), Lemma 4.11;
see also A.3.21(b), p.55. The concrete model premise remains explicit for its
independent producer. No SQTK, supplement, congruence, or actor-cardinality
hypothesis is needed for this transport once that premise is given.
-/

public section
open Subgroup Theory.GroupTheory BenderSuzuki.MatrixGroups
open BenderSuzuki.MatrixGroups.HermitianForm.OddPrimeSylow.NormalizedOuter.FormTransport
namespace CFSG.Quasithin.ChapterE.ValuesOdd.PSUThreeGeneration.OuterFamilies.FourActors.CentralizerGeometry.InvertedOddSubgroup.AbelianReselection

variable {G : Type*} [Group G] [Finite G]

/-- Transport genuine model coordinates to the supplied Sylow and its original
marked involution. The sole outstanding input is the concrete model realization. -/
theorem cyclicByFourCoordinates_of_modelInput [IsSimpleGroup (generalizedFitting G)]
    {p : ℕ} (input : CyclicCoreModelInput p) (hp : p.Prime) (ho : Odd p)
    (hmodel : ClassicalGroup.IsPSU (generalizedFitting G) 3 p)
    (T : Sylow 2 G) (hout : ¬ (T : Subgroup G) ≤ generalizedFitting G)
    {z : G} (hz : orderOf z = 2) (hzL : z ∈ generalizedFitting G) (hzT : z ∈ T)
    (hTz : (T : Subgroup G) ≤ centralizer ({z} : Set G)) :
    Nonempty (CyclicByFourCoordinates (generalizedFitting G) (T : Subgroup G) z) := by
  have hC := SimpleSocle.centralizer_eq_bot (nonabelian_of_model hp ho hmodel)
  obtain ⟨F, _, _, J, hcard, hc, ⟨e⟩⟩ := hmodel
  let : Fact p.Prime := ⟨hp⟩
  have hfixed : Nat.card {x : F // J.conj x = x} = p := by
    simpa only [pow_one] using
      (FiniteField.card_fixed_of_quadratic_frobenius J.conj p 1 (by decide)
        (by simpa only [pow_one] using hcard)
        (by simpa only [pow_one] using hc))
  obtain ⟨es⟩ := exists_projectiveEquiv J p hcard hfixed
  let e₀ := e.trans es
  let P := ProjectiveSpecialUnitaryMatrixGroup (standardForm J)
  let : Finite P := Finite.of_equiv (generalizedFitting G) e₀.toEquiv
  let : IsSimpleGroup P := e₀.symm.isSimpleGroup
  obtain ⟨S, w, _hw, ⟨d⟩⟩ := input F (standardForm J) inferInstance hcard hc rfl
  let f : G →* MulAut P :=
    (MulAut.congr e₀).toMonoidHom.comp (MulAut.conjNormal (H := generalizedFitting G))
  have hf : Function.Injective f := (MulAut.congr e₀).injective.comp
    (MulAut.conjNormal_injective_of_centralizer_eq_bot _ hC)
  have hinner (x : generalizedFitting G) : f x = MulAut.conj (e₀ x) := by
    change MulAut.congr e₀ (MulAut.conjNormal (x : G)) = _
    rw [MulAut.conjNormal_val, MulAut.congr_conj]
  have hLN : (generalizedFitting G).map f = MulAut.innerSubgroup P := by
    ext a
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨e₀ ⟨x, hx⟩, (hinner ⟨x, hx⟩).symm⟩
    · rintro ⟨x, rfl⟩
      refine ⟨e₀.symm x, (e₀.symm x).property, ?_⟩
      rw [hinner, e₀.apply_symm_apply]
  exact d.of_faithful_sylow f hf (MulAut.innerSubgroup P) hLN S T hout hz hzL hzT hTz

/-- Application to the positioned outer four-actor from the E.1.14 reduction.
Only its outer element and its marked inner involution are used in transport. -/
theorem cyclicByFourCoordinates_of_modelInput_four_actor
    [IsSimpleGroup (generalizedFitting G)]
    {p : ℕ} (input : CyclicCoreModelInput p) (hp : p.Prime) (ho : Odd p)
    (hmodel : ClassicalGroup.IsPSU (generalizedFitting G) 3 p)
    (T : Sylow 2 G) (A : Subgroup G) (hAT : A ≤ (T : Subgroup G))
    (hout : ¬ A ≤ generalizedFitting G)
    {z : G} (hz : orderOf z = 2) (hzL : z ∈ generalizedFitting G) (hzA : z ∈ A)
    (hTz : (T : Subgroup G) ≤ centralizer ({z} : Set G)) :
    Nonempty (CyclicByFourCoordinates (generalizedFitting G) (T : Subgroup G) z) :=
  cyclicByFourCoordinates_of_modelInput input hp ho hmodel T (fun h => hout (hAT.trans h))
    hz hzL (hAT hzA) hTz

end CFSG.Quasithin.ChapterE.ValuesOdd.PSUThreeGeneration.OuterFamilies.FourActors.CentralizerGeometry.InvertedOddSubgroup.AbelianReselection
