module

public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceMathieuM24ComponentIdentification
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.MathieuJ4RecognitionApplication

/-!
# The original marked M₂₄ cocode supplies type-J₄

The full centralizer quotient constructed in 8.2.13 supplies the actual
surjection to Aut(M₂₂), with kernel of order three. Together with the
original extraspecial core and returning conjugate, this discharges every
local premise of the intrinsic type-J₄ predicate. The generator of the
original Ω₁Z(T) provides the required central involution in the same orbit.

The independent shadow-exclusion producer must select this whole cocode
marking. The independent Aschbacher–Segev recognition producer must turn
type-J₄ in the original simple group into the ambient J₄ isomorphism.
Final assembly remains with qt-d-1222-nonff-mathieu.

Source: Aschbacher–Smith 8.2.12–14, printed pp.722–723; Aschbacher–Segev,
*The uniqueness of groups of type J₄*, Invent. Math. 105 (1991), p.589.
-/

public noncomputable section

open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open Sporadic.Mathieu MathieuCode
open scoped IsMulCommutative

namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open ChapterE Chapter7.NormalizedSource Stellmacher
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)

/-- The original full quotient supplies the cubic extension required by
Aschbacher–Segev, retaining its literal quotient and its kernel. -/
theorem sourceOrbit_m24_cubic_automorphism_quotient
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit)
    (hq : Nonempty ((D.orbitComponent ⧸ center D.orbitComponent) ≃* M24))
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    (a : Automizer D.sourceOrbit ≃* M24)
    (E : Additive D.sourceOrbit ≃ₗ[ZMod 2] Cocode)
    (hE : ∀ b v, E (automizerRepresentation D.sourceOrbit b v) =
      cocodeRepresentation (a b) (E v))
    (z : D.sourceOrbit) (hz : (z : G) ∈ centralizer (T : Set G)) (hne : z ≠ 1) :
    Nonempty (Recognition.JankoFour.CubicAutomorphismQuotient
      ((centralizer ({(z : G)} : Set G)) ⧸ pCore 2 (centralizer ({(z : G)} : Set G)))) := by
  obtain ⟨_,π,hπ,hker⟩ :=
    D.sourceOrbit_m24_centralizer_quotient_extension h hmany hV hq hnon a E hE z hz hne
  exact ⟨⟨π,hπ,hker⟩⟩

/-- The marked cocode constructs all original type-J₄ clauses. There is no
extra quotient, core, fusion, or local-geometry premise. -/
theorem sourceOrbit_m24_isTypeJ4_of_cocode
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit)
    (hq : Nonempty ((D.orbitComponent ⧸ center D.orbitComponent) ≃* M24))
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    (a : Automizer D.sourceOrbit ≃* M24)
    (E : Additive D.sourceOrbit ≃ₗ[ZMod 2] Cocode)
    (hE : ∀ b v, E (automizerRepresentation D.sourceOrbit b v) =
      cocodeRepresentation (a b) (E v))
    (z : D.sourceOrbit) (hz : (z : G) ∈ centralizer (T : Set G)) (hne : z ≠ 1) :
    Recognition.JankoFour.IsTypeJ4 (z : G) := by
  exact D.sourceOrbit_m24_isTypeJ4 h hmany hV hq hnon a E hE z hz hne
    (D.sourceOrbit_m24_cubic_automorphism_quotient h hmany hV hq hnon a E hE z hz hne)

/-- The same original orbit supplies its own central involution and all
recognition inputs, with Ω₁Z(T) and the marked module unchanged. -/
theorem sourceOrbit_m24_exists_isTypeJ4_of_cocode
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit)
    (hq : Nonempty ((D.orbitComponent ⧸ center D.orbitComponent) ≃* M24))
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    (a : Automizer D.sourceOrbit ≃* M24)
    (E : Additive D.sourceOrbit ≃ₗ[ZMod 2] Cocode)
    (hE : ∀ b v, E (automizerRepresentation D.sourceOrbit b v) =
      cocodeRepresentation (a b) (E v)) :
    ∃ z : D.sourceOrbit, z ≠ 1 ∧ (z : G) ∈ centralizer (T : Set G) ∧
      zpowers (z : G) = omegaOneCenterAmbient (T : Subgroup G) ∧
      Recognition.JankoFour.IsTypeJ4 (z : G) := by
  obtain ⟨z,hne,_,hZ,_⟩ :=
    D.sourceOrbit_m24_exists_centralizer_residual h hmany hV hq hnon a E hE
  obtain ⟨_,_,_,_,_,_,_,_,_,hz,_⟩ :=
    D.sourceOrbit_m24_cocode_block_structure h hmany hV hq hnon a E hE
  have hzf : (z : G) ∈ centralizer (T : Set G) :=
    (hz.le.trans inf_le_right) (hZ.le (mem_zpowers _))
  exact ⟨z,hne,hzf,hZ,D.sourceOrbit_m24_isTypeJ4_of_cocode h hmany hV hq hnon a E hE z hzf hne⟩

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
