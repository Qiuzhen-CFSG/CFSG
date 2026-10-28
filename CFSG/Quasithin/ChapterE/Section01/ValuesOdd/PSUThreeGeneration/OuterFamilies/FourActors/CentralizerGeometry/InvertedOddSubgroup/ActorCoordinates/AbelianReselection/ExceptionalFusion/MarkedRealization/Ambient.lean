module

public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSUThreeGeneration.OuterFamilies.FourActors.CentralizerGeometry.InvertedOddSubgroup.ActorCoordinates.AbelianReselection.ExceptionalFusion.MarkedRealization.ModelInput
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSUThreeGeneration.OuterFamilies.ActorGeometry
public import Theory.SpecificGroups.SU3.MarkedHyperbolicCoordinates.Transport

/-!
# Ambient transport of the marked unitary plane

Normalize the actual projective model and embed the ambient group faithfully
in its automorphism group using conjugation on its simple socle. The socle
maps onto the literal inner-automorphism subgroup. A supplied Sylow with an
outer element then maps onto a full automorphism Sylow. Conjugating the
marked model data and pulling the plane map back retains every matrix
marking and its full field action, including the original central involution.

The sole model premise is `MarkedHyperbolicModelInput`. Its independent
producer must discharge it before the unconditional source conclusion is
available. SQTK and supplement hypotheses are unnecessary for this transport.

Source: Aschbacher--Smith E.1.14(7), p.214, A.3.21(a,b), p.55;
Aschbacher (1982), Lemma 4.11.
-/

public section
open Subgroup Theory.GroupTheory BenderSuzuki.MatrixGroups
open Matrix.UnitaryQuaternionRotation
open BenderSuzuki.MatrixGroups.HermitianForm.OddPrimeSylow.NormalizedOuter.FormTransport
namespace CFSG.Quasithin.ChapterE.ValuesOdd.PSUThreeGeneration.OuterFamilies.FourActors.CentralizerGeometry.InvertedOddSubgroup.AbelianReselection

variable {G : Type*} [Group G] [Finite G]

/-- Transport the whole marked plane to the actual ambient Sylow. The explicit
model premise is independent of any choice of a cyclic-core record. -/
theorem markedCyclicByFour_of_modelInput [IsSimpleGroup (generalizedFitting G)]
    {p : ℕ} (input : MarkedHyperbolicModelInput p) (hp : p.Prime) (ho : Odd p)
    (hmodel : ClassicalGroup.IsPSU (generalizedFitting G) 3 p)
    (T : Sylow 2 G) (hout : ¬ (T : Subgroup G) ≤ generalizedFitting G)
    {z : G} (hz : orderOf z = 2) (hzL : z ∈ generalizedFitting G) (hzT : z ∈ T)
    (hTz : (T : Subgroup G) ≤ centralizer ({z} : Set G)) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (J : HermitianForm 2 F),
      Nonempty (MarkedCyclicByFour (generalizedFitting G) (T : Subgroup G) z J) := by
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
  obtain ⟨S, w, J₂, _hw, ⟨q⟩⟩ := input F (standardForm J) inferInstance hcard hc rfl
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
  exact ⟨F, inferInstance, inferInstance, J₂,
    q.of_faithful_sylow f hf (MulAut.innerSubgroup P) hLN S T hout hz hzL hzT hTz⟩

end CFSG.Quasithin.ChapterE.ValuesOdd.PSUThreeGeneration.OuterFamilies.FourActors.CentralizerGeometry.InvertedOddSubgroup.AbelianReselection
