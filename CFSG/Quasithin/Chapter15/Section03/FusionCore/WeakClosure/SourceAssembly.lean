module

public import CFSG.Quasithin.Chapter15.Section03.FusionCore.WeakClosure.Assembly
public import CFSG.Quasithin.Chapter15.Section03.FusionCore.WeakClosure.OrbitConstruction
public import CFSG.Quasithin.Chapter15.Section03.FusionCore.WeakClosure.Centralization

/-!
# The conditional source statements of 15.3.46–47

The genuine natural orthogonal action constructs compatible wreath coordinates,
both local orbits, and the Sylow subgroup of the full nonsingular centralizer.
These calculations separate the two orbits in `G`. The mutually normalizing
and dual-core arguments then prove that `W₀(T,V)` centralizes `V`. Frattini and
the earlier residual dichotomy bound its full normalizer. Finally, a fixed
nonsingular vector rules out nonzero totally singular commutator displacement,
giving 15.3.47.

Only earlier-source inputs remain: `M = N_G(V)`, `V = ⟨Z^M⟩ ≤ T ≤ M`,
`Z = C_V(T)` of order two, the two-residual/full-image uniqueness dichotomy
15.3.2(4), and `C_G(C_P(N_T(P))) ≤ M` from 15.3.45(3). The action includes
the nondegenerate four-dimensional plus form and the full isometry image;
`P` is an actual definite plane. The parent source assembly supplies these
inputs. No coordinate, orbit, Sylow-centralizer, fusion, or weak-closure
witness remains a premise of the theorems below.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), printed p.1141;
the earlier inputs are on pp.1121–1122 and 1140.
-/

public section

namespace CFSG.Quasithin.Chapter15.Section03.FusionCore

open Subgroup

variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {M V P : Subgroup G} [IsElementaryAbelian 2 V]

/-- The centralization step of 15.3.46(4), with the coordinate model, the
orbit/Sylow calculations, and both source cases discharged. -/
theorem weakClosure_zero_le_centralizer_of_earlier_inputs
    (d : NaturalOrthogonalAction M V) (h : EarlierFusionInputs T M V P)
    (hP : IsDefinitePlane d.form P) :
    ChapterE.indexedWeakClosure V T 0 ≤ centralizer (V : Set G) := by
  obtain ⟨k, c⟩ := orthogonalCoordinateModel_and_fusionCalculations d h hP
  exact Centralization.weakClosure_zero_le_centralizer d h hP k c

/-- All five clauses of 15.3.46, conditional only on the enumerated earlier
source inputs and the genuine natural orthogonal action. Clause (1) holds
for every element of `V`; in particular it holds for every involution.
The second assertion of clause (2) also holds at the subgroup endpoints. -/
theorem lemma_15_3_46_of_earlier_inputs
    (d : NaturalOrthogonalAction M V) (h : EarlierFusionInputs T M V P)
    (hP : IsDefinitePlane d.form P) :
    (∀ x ∈ V, ∀ g : G, MulAut.conj g x ∈ V →
      ConjugateBy M x (MulAut.conj g x)) ∧
    ((∀ g : G, g ∉ M →
      IsTotallySingular d.form (V ⊓ V.map (MulAut.conj g).toMonoidHom)) ∧
      ∀ U : Subgroup G, U ≤ V → ¬ normalizer (U : Set G) ≤ M →
        IsTotallySingular d.form U) ∧
    1 < ChapterE.globalR V ∧
    (ChapterE.indexedWeakClosure V T 0 ≤ centralizer (V : Set G) ∧
      0 < ChapterE.globalW V T ∧
      (∀ g : G, V.map (MulAut.conj g).toMonoidHom ≤ M →
        V.map (MulAut.conj g).toMonoidHom ≤ centralizer (V : Set G)) ∧
      normalizer (ChapterE.indexedWeakClosure V T 0 : Set G) ≤ M) ∧
    (normalizer (fixedPlane V (planeStabilizer T P) : Set G) ≤ M ∧
      ∀ v : V, d.form (Additive.ofMul v) ≠ 0 →
        centralizer ({(v : G)} : Set G) ≤ M) := by
  obtain ⟨k, c⟩ := orthogonalCoordinateModel_and_fusionCalculations d h hP
  have hfusion := controlsFusion_of_orthogonal_calculations c h
  have hcentral := nonsingular_centralizer_le_of_orthogonal_calculations c h
  have hW := Centralization.weakClosure_zero_le_centralizer d h hP k c
  refine ⟨hfusion, ⟨?_, ?_⟩,
    one_lt_globalR d.form d.nondegenerate d.dimension h.normalizer_eq hcentral,
    ⟨hW, weakClosure_zero_consequences d h hW⟩,
    normalizer_fixedPlane_le_of_orthogonal_calculations c h hP, hcentral⟩
  · exact totallySingular_intersection_of_fusion d.form h.normalizer_eq hfusion hcentral
  · intro U hUV hU
    exact totallySingular_of_normalizer_escape d.form h.normalizer_eq hfusion hcentral hUV hU

/-- The nonsingularity assertion in the proof of 15.3.47, with the fixed
nonsingular vector constructed from the earlier inputs. -/
theorem not_totallySingular_commutator_of_earlier_inputs
    (d : NaturalOrthogonalAction M V) (h : EarlierFusionInputs T M V P)
    (hP : IsDefinitePlane d.form P)
    (x : G) (hx : x ∈ centralizer (fixedPlane V (planeStabilizer T P) : Set G))
    (hne : ⁅V, zpowers x⁆ ≠ ⊥) :
    ¬ IsTotallySingular d.form ⁅V, zpowers x⁆ := by
  obtain ⟨_, c⟩ := orthogonalCoordinateModel_and_fusionCalculations d h hP
  exact not_totallySingular_commutator_of_centralizes_fixedPlane d h c hP x hx hne

/-- The complete alternative of 15.3.47 from the same earlier inputs.
Every whole conjugate normalizing a nontrivial `[V,x]` centralizes `V`. -/
theorem lemma_15_3_47_of_earlier_inputs
    (d : NaturalOrthogonalAction M V) (h : EarlierFusionInputs T M V P)
    (hP : IsDefinitePlane d.form P)
    (x : G) (hx : x ∈ centralizer (fixedPlane V (planeStabilizer T P) : Set G)) :
    ⁅V, zpowers x⁆ = ⊥ ∨
      ∀ g : G,
        V.map (MulAut.conj g).toMonoidHom ≤
          normalizer ((⁅V, zpowers x⁆ : Subgroup G) : Set G) →
        V.map (MulAut.conj g).toMonoidHom ≤ centralizer (V : Set G) := by
  obtain ⟨k, c⟩ := orthogonalCoordinateModel_and_fusionCalculations d h hP
  exact commutator_alternative_of_orthogonal_calculations d h c hP
    (Centralization.weakClosure_zero_le_centralizer d h hP k c) x hx

end CFSG.Quasithin.Chapter15.Section03.FusionCore
