module

public import CFSG.Quasithin.Chapter14.Section08
public import CFSG.Quasithin.Chapter14.Section08.LieTypeBranch.Assembly
public import CFSG.Quasithin.Chapter14.Section08.LieTypeBranch.SourcePredicateBridge

/-!
# Constructing the standing source counterexample for Theorem D

The complete Lie-family assembly and the unrestricted-predicate comparison
give the D-model conclusion from the literal Chapter 13 Lie predicate.
Consequently a counterexample to D satisfies that exclusion. Every other
global model exclusion in the existing Chapter 13 record is an explicit
alternative of D. Choosing a faithful local subgroup with the proved uniform
A₅-quotient property therefore constructs the whole standing record.

This proves the opening reduction of Aschbacher--Smith Theorem 14.8.2,
printed pp. 1078--1079, to Hypothesis 13.3.1 and the additional global
exclusions of 13.7.1. The local recognition arguments still have to eliminate
the resulting counterexample; no local action or identification is assumed
in these deductions.
-/

public section

namespace CFSG.Quasithin.Chapter14.Section08.LieTypeBranch

open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension

universe u
variable {G : Type u} [Group G] [Finite G]

/-- The literal unrestricted larger-field predicate gives a full D-model. -/
theorem theoremDModel_of_largerEvenFieldModel
    (h : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hne : (MainForward.faithfulLocalComponents T).Nonempty)
    (hmodel : LargerEvenFieldModel G) : ClassificationModels.IsTheoremDModel G := by
  obtain ⟨n, hn, hm⟩ :=
    isBinaryLieModelAt_of_largerEvenFieldModel_of_isSimpleQTKE h hmodel
  exact theoremDModel_of_binaryLieModel h T hne hn hm

/-- Failure of every D conclusion discharges the exact Chapter 13 Lie exclusion. -/
theorem no_larger_field_of_not_theoremDModel
    (h : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hne : (MainForward.faithfulLocalComponents T).Nonempty)
    (hnot : ¬ ClassificationModels.IsTheoremDModel G) : ¬ LargerEvenFieldModel G :=
  fun hm => hnot (theoremDModel_of_largerEvenFieldModel h T hne hm)

/-- A selected local subgroup of a counterexample to D satisfies every global
clause of the existing Chapter 13 standing configuration. -/
theorem counterexample_of_not_theoremDModel
    (h : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    {L : Subgroup G} (hL : L ∈ MainForward.faithfulLocalComponents T)
    (hfive : Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)) →
      ∀ J ∈ MainForward.faithfulLocalComponents T,
        Nonempty ((J ⧸ pCore 2 J) ≃* alternatingGroup (Fin 5)))
    (hnot : ¬ ClassificationModels.IsTheoremDModel G) : Counterexample T L where
  qtke := h
  local_component := hL
  no_larger_field := no_larger_field_of_not_theoremDModel h T ⟨L, hL⟩ hnot
  no_linear := fun n hn iso => hnot (.exceptional (.linear_binary n hn iso))
  no_alternating_nine := fun iso => hnot (.exceptional (.alternating_nine iso))
  no_sporadic := by
    intro s hs iso
    rcases hs with rfl | rfl | rfl | rfl | rfl
    · exact hnot (.exceptional (.sporadic .m22 (by simp) iso))
    · exact hnot (.exceptional (.sporadic .m23 (by simp) iso))
    · exact hnot (.exceptional (.sporadic .m24 (by simp) iso))
    · exact hnot (.exceptional (.sporadic .he (by simp) iso))
    · exact hnot (.exceptional (.sporadic .j4 (by simp) iso))
  five_minimal := hfive
  no_symplectic_six := fun iso => hnot (.exceptional (.symplectic_binary iso))
  no_unitary_four := fun iso => hnot (.exceptional (.unitary_three iso))

/-- The actual nonempty-family input of D constructs the standing source
counterexample whenever no conclusion of D holds. -/
theorem exists_counterexample_of_not_theoremDModel
    (h : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hne : (MainForward.faithfulLocalComponents T).Nonempty)
    (hnot : ¬ ClassificationModels.IsTheoremDModel G) :
    ∃ L : Subgroup G, Counterexample T L := by
  obtain ⟨L, hL, hfive⟩ := exists_local_with_uniform_A5_quotient _ hne
  exact ⟨L, counterexample_of_not_theoremDModel h T hL hfive hnot⟩

end CFSG.Quasithin.Chapter14.Section08.LieTypeBranch
