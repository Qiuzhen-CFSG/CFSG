module

public import CFSG.Quasithin.ChapterK.Section01To04.Alternating.Recognition.Six.Homogeneous
public import Theory.Representation.BinaryAlternatingSixModels.Schur
public import Theory.Representation.BinaryOffender.Homogeneous.Dimension

/-!
# Proper homogeneous A₆ coordinates from a Schur bound

The complete binary catalogue supplies actual model equivalences. Faithfulness
excludes the trivial model, and the tensor's Schur degree at most two excludes
its degree sixteen. A faithful four-space has Schur degree one by actual natural
recognition, including the actor automorphism. The ambient degree is then at
most ten. A third simple copy would force degree at least twelve, so two copies
span. The existing double-coordinate theorem supplies one common A₆ marking
and an intertwining linear equivalence on the original module.

Only the stated ambient Schur bound is assumed. No counterexample-only claim
from G.11 is used unconditionally. Source: Aschbacher--Smith G.11.7--8,
printed pp.366,368--369; the terminal application is14.3.15, printed p.994.
-/

public noncomputable section

open Representation
namespace CFSG.Quasithin.ChapterK.Alternating.RecognitionInputs.Six
open BinaryAlternatingSix.Schur

/-- Actual four-space recognition transports Schur degree one, including
the possible automorphism of the alternating actor. -/
theorem end_finrank_one_of_faithful_fourSpace
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    (σ : Representation (ZMod 2) (alternatingGroup (Fin 6)) V)
    (hf : Function.Injective σ) (hd : Module.finrank (ZMod 2) V = 4) :
    Module.finrank (ZMod 2) (IntertwiningMap σ σ) = 1 := by
  obtain ⟨a⟩ := actionEquiv_of_faithful_fourSpace σ hf hd
  let τ := BinaryPermutation.alternatingNaturalRepresentation (Fin 6)
  let e : σ.Equiv (τ.comp a.groupEquiv.toMonoidHom) :=
    .mk a.linearEquiv (fun g => LinearMap.ext (a.intertwines g))
  exact (endEquiv e).finrank_eq.trans
    ((endCompEquiv τ a.groupEquiv).finrank_eq.trans natural_end_finrank_one)

/-- A proper homogeneous faithful A₆ constituent and the Schur bound
construct actual natural double coordinates with a common actor marking. -/
theorem naturalCoordinates_of_homogeneous_schur_bound
    {D V : Type*} [Group D] [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V] (ρ : Representation (ZMod 2) D V)
    (e6 : D ≃* alternatingGroup (Fin 6))
    (R : Subrepresentation ρ) [IsIrreducible R.toRepresentation]
    (hf : Function.Injective R.toRepresentation)
    (hh : BinaryOffender.Homogeneous.homogeneousPart R ⊤ = ⊤)
    (hp : R.toSubmodule ≠ ⊤)
    (hd : Module.finrank (ZMod 2) V ≤ 2 *
      (Module.finrank (ZMod 2) (IntertwiningMap R.toRepresentation R.toRepresentation) + 4)) :
    BinaryAlternatingSixNaturalNormalizer.HasNaturalCoordinates ρ := by
  let σ := R.toRepresentation.comp e6.symm.toMonoidHom
  let : IsIrreducible σ := (irreducible_comp_surjective_iff
    e6.symm.toMonoidHom e6.symm.surjective _).mpr inferInstance
  have hfσ : Function.Injective σ := hf.comp e6.symm.injective
  have hs := (endCompEquiv R.toRepresentation e6.symm).finrank_eq
  have hlo := ChapterG.Section09.DefiningCharacteristic.SymplecticFourRecognition.SmallParameter.degree_ge_four σ hfσ
  have hfour : Module.finrank (ZMod 2) R.toSubmodule = 4 := by
    rcases BinaryAlternatingSix.alternating_classify σ with h | h | h | h
    all_goals obtain ⟨e⟩ := h
    · have he := e.toLinearEquiv.finrank_eq
      have hone : Module.finrank (ZMod 2) R.toSubmodule = 1 := by simpa using he
      omega
    · exact e.toLinearEquiv.finrank_eq.trans
        Theory.SpecificGroups.SymmetricSix.naturalModule_finrank
    · exact e.toLinearEquiv.finrank_eq.trans
        Theory.SpecificGroups.SymmetricSix.naturalModule_finrank
    · have ht := BinaryAlternatingSix.ScalarFour.alternatingTensor_endField_finrank_le_two
      have he := (endEquiv e).finrank_eq
      have hm : Module.finrank (ZMod 2)
          (IntertwiningMap BinaryAlternatingSix.alternatingTensor BinaryAlternatingSix.alternatingTensor) =
          Module.finrank (ZMod 2)
            (Module.End (MonoidAlgebra (ZMod 2) Theory.SpecificGroups.SymmetricSix.A6)
              (Representation.asModule BinaryAlternatingSix.alternatingTensor)) :=
        (IntertwiningMap.equivLinearMapAsModule
          BinaryAlternatingSix.alternatingTensor BinaryAlternatingSix.alternatingTensor).finrank_eq
      have hsbound : Module.finrank (ZMod 2)
          (IntertwiningMap R.toRepresentation R.toRepresentation) ≤ 2 :=
        (hs.symm.trans (he.trans hm)).le.trans ht
      have hdim := e.toLinearEquiv.finrank_eq.trans BinaryAlternatingSix.tensor_finrank
      have hle := R.toSubmodule.finrank_le
      omega
  have hone := end_finrank_one_of_faithful_fourSpace σ hfσ hfour
  have honeR : Module.finrank (ZMod 2)
      (IntertwiningMap R.toRepresentation R.toRepresentation) = 1 := hs.symm.trans hone
  rw [honeR] at hd
  have hten : Module.finrank (ZMod 2) V ≤ 10 := hd
  have hdouble := BinaryOffender.Homogeneous.degree_le_double_of_lt_triple R
    inferInstance hh hp (by omega)
  exact naturalCoordinates_of_homogeneous_degree_le_eight ρ e6 R hf hh hp (by omega)

end CFSG.Quasithin.ChapterK.Alternating.RecognitionInputs.Six
