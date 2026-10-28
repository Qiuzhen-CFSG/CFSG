module

public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.MathieuJ4RecognitionApplication
public import Theory.GroupTheory.Recognition.JankoFour.SourceCycleBase

/-!
# The original marked Mathieu geometry and cycle reduction

The source witness is exactly `sourceOrbit_m24_isTypeJ4`, with the original
central involution, whole-module marking and cubic quotient. The complete
AS91 section 7 argument proves the base of that same ambient system from
its unchanged earlier-source incidence Input. The earlier conditional
adapters retain their public interfaces; their section 7 premises are now
discharged by the cycle-base family.

Construction of every earlier-source Input field and the section 8 comparison
remain with the source-recognition producer. This theorem supplies its actual
source base; it does not assert unconditional ambient recognition.

Source: AS91 (5.5) and §8; Aschbacher–Smith 8.2.12–14, pp.722–723.
-/

public section

open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open Sporadic.Mathieu MathieuCode
open scoped IsMulCommutative

namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule

open ChapterE Chapter7.NormalizedSource Chapter8.Section02.Centralizer
open Recognition.JankoFour

variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)

/-- Literal application to the same ambient system; no J₄ exclusion is used. -/
theorem sourceOrbit_m24_triangle_mem_cycleBase
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit)
    (hq : Nonempty ((D.orbitComponent ⧸ center D.orbitComponent) ≃* M24))
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    (a : Automizer D.sourceOrbit ≃* M24)
    (E : Additive D.sourceOrbit ≃ₗ[ZMod 2] Cocode)
    (hE : ∀ b v, E (automizerRepresentation D.sourceOrbit b v) =
      cocodeRepresentation (a b) (E v))
    (z : D.sourceOrbit) (hz : (z : G) ∈ centralizer (T : Set G)) (hne : z ≠ 1)
    (hquot : Nonempty (CubicAutomorphismQuotient
      ((Subgroup.centralizer ({(z : G)} : Set G)) ⧸
        pCore 2 (Subgroup.centralizer ({(z : G)} : Set G)))))
    (d : SourceCycleBase.Input
      (D.sourceOrbit_m24_isTypeJ4 h hmany hV hq hnon a E hE z hz hne hquot))
    (x : SourceCycleBase.Point d.P) (p : d.system.graph.Walk x x)
    (hp : p.length = 3) : p ∈ d.system.baseCycles x :=
  d.triangle_mem_baseCycles x p hp

/-- Actual marked-source application of the proved reduction and involution
endgame. These three later-source premises remain to be discharged by the
cycle-base owner; they are not earlier-source Input fields. -/
theorem sourceOrbit_m24_isBase_of_incidence_conditions
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit)
    (hq : Nonempty ((D.orbitComponent ⧸ center D.orbitComponent) ≃* M24))
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    (a : Automizer D.sourceOrbit ≃* M24)
    (E : Additive D.sourceOrbit ≃ₗ[ZMod 2] Cocode)
    (hE : ∀ b v, E (automizerRepresentation D.sourceOrbit b v) =
      cocodeRepresentation (a b) (E v))
    (z : D.sourceOrbit) (hz : (z : G) ∈ centralizer (T : Set G)) (hne : z ≠ 1)
    (hquot : Nonempty (CubicAutomorphismQuotient
      ((Subgroup.centralizer ({(z : G)} : Set G)) ⧸
        pCore 2 (Subgroup.centralizer ({(z : G)} : Set G)))))
    (d : SourceCycleBase.Input
      (D.sourceOrbit_m24_isTypeJ4 h hmany hV hq hnon a E hE z hz hne hquot))
    (bridge : d.Bridge) (far : d.FarLineTransitive) (close : d.ComponentClose) :
    d.system.IsBase :=
  d.isBase_of_incidence_conditions bridge far close

/-- The same original marked Mathieu system, with the native far-line orbit
proved. Only B2 and the source component-distance bound remain explicit. -/
theorem sourceOrbit_m24_isBase_of_bridge_componentClose
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit)
    (hq : Nonempty ((D.orbitComponent ⧸ center D.orbitComponent) ≃* M24))
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    (a : Automizer D.sourceOrbit ≃* M24)
    (E : Additive D.sourceOrbit ≃ₗ[ZMod 2] Cocode)
    (hE : ∀ b v, E (automizerRepresentation D.sourceOrbit b v) =
      cocodeRepresentation (a b) (E v))
    (z : D.sourceOrbit) (hz : (z : G) ∈ centralizer (T : Set G)) (hne : z ≠ 1)
    (hquot : Nonempty (CubicAutomorphismQuotient
      ((Subgroup.centralizer ({(z : G)} : Set G)) ⧸
        pCore 2 (Subgroup.centralizer ({(z : G)} : Set G)))))
    (d : SourceCycleBase.Input
      (D.sourceOrbit_m24_isTypeJ4 h hmany hV hq hnon a E hE z hz hne hquot))
    (bridge : d.Bridge) (close : d.ComponentClose) :
    d.system.IsBase :=
  d.isBase_of_bridge_componentClose bridge close

/-- The same marked Mathieu system after discharging the far branch of B2.
Only the δ₃ plane-hitting assertion (7.4.2) and ComponentClose (7.6.2) remain;
the original chosen involution, cubic quotient, and Todd marking are retained. -/
theorem sourceOrbit_m24_isBase_of_deltaThree_componentClose
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit)
    (hq : Nonempty ((D.orbitComponent ⧸ center D.orbitComponent) ≃* M24))
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    (a : Automizer D.sourceOrbit ≃* M24)
    (E : Additive D.sourceOrbit ≃ₗ[ZMod 2] Cocode)
    (hE : ∀ b v, E (automizerRepresentation D.sourceOrbit b v) =
      cocodeRepresentation (a b) (E v))
    (z : D.sourceOrbit) (hz : (z : G) ∈ centralizer (T : Set G)) (hne : z ≠ 1)
    (hquot : Nonempty (CubicAutomorphismQuotient
      ((Subgroup.centralizer ({(z : G)} : Set G)) ⧸
        pCore 2 (Subgroup.centralizer ({(z : G)} : Set G)))))
    (d : SourceCycleBase.Input
      (D.sourceOrbit_m24_isTypeJ4 h hmany hV hq hnon a E hE z hz hne hquot))
    (three : d.DeltaThreePlaneHitting) (close : d.ComponentClose) :
    d.system.IsBase :=
  d.isBase_of_deltaThree_componentClose three close

/-- Both plane-hitting branches are proved. The remaining bound is (7.6.2). -/
theorem sourceOrbit_m24_isBase_of_componentClose
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit)
    (hq : Nonempty ((D.orbitComponent ⧸ center D.orbitComponent) ≃* M24))
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    (a : Automizer D.sourceOrbit ≃* M24)
    (E : Additive D.sourceOrbit ≃ₗ[ZMod 2] Cocode)
    (hE : ∀ b v, E (automizerRepresentation D.sourceOrbit b v) =
      cocodeRepresentation (a b) (E v))
    (z : D.sourceOrbit) (hz : (z : G) ∈ centralizer (T : Set G)) (hne : z ≠ 1)
    (hquot : Nonempty (CubicAutomorphismQuotient
      ((Subgroup.centralizer ({(z : G)} : Set G)) ⧸
        pCore 2 (Subgroup.centralizer ({(z : G)} : Set G)))))
    (d : SourceCycleBase.Input
      (D.sourceOrbit_m24_isTypeJ4 h hmany hV hq hnon a E hE z hz hne hquot))
    (close : d.ComponentClose) :
    d.system.IsBase :=
  d.isBase_of_componentClose close

/-- The literal marked-source base after the native plane-distance calculation.
Only the δ₃ component-disc witness (7.4.1) remains beyond the earlier-source
Input. Its existence is still owned by the same cycle-base theorem family. -/
theorem sourceOrbit_m24_isBase_of_deltaThree_disc
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit)
    (hq : Nonempty ((D.orbitComponent ⧸ center D.orbitComponent) ≃* M24))
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    (a : Automizer D.sourceOrbit ≃* M24)
    (E : Additive D.sourceOrbit ≃ₗ[ZMod 2] Cocode)
    (hE : ∀ b v, E (automizerRepresentation D.sourceOrbit b v) =
      cocodeRepresentation (a b) (E v))
    (z : D.sourceOrbit) (hz : (z : G) ∈ centralizer (T : Set G)) (hne : z ≠ 1)
    (hquot : Nonempty (CubicAutomorphismQuotient
      ((Subgroup.centralizer ({(z : G)} : Set G)) ⧸
        pCore 2 (Subgroup.centralizer ({(z : G)} : Set G)))))
    (d : SourceCycleBase.Input
      (D.sourceOrbit_m24_isTypeJ4 h hmany hV hq hnon a E hE z hz hne hquot))
    (three : d.DeltaThreeComponentDisc) :
    d.system.IsBase :=
  d.isBase_of_deltaThree_disc three

/-- The exact marked Mathieu application of the complete AS91 source cycle
base. The only retained extra premise is the earlier-source Input for this
same type-J₄ witness and literal coset system. -/
theorem sourceOrbit_m24_isBase
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit)
    (hq : Nonempty ((D.orbitComponent ⧸ center D.orbitComponent) ≃* M24))
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    (a : Automizer D.sourceOrbit ≃* M24)
    (E : Additive D.sourceOrbit ≃ₗ[ZMod 2] Cocode)
    (hE : ∀ b v, E (automizerRepresentation D.sourceOrbit b v) =
      cocodeRepresentation (a b) (E v))
    (z : D.sourceOrbit) (hz : (z : G) ∈ centralizer (T : Set G)) (hne : z ≠ 1)
    (hquot : Nonempty (CubicAutomorphismQuotient
      ((Subgroup.centralizer ({(z : G)} : Set G)) ⧸
        pCore 2 (Subgroup.centralizer ({(z : G)} : Set G)))))
    (d : SourceCycleBase.Input
      (D.sourceOrbit_m24_isTypeJ4 h hmany hV hq hnon a E hE z hz hne hquot))
    :
    d.system.IsBase :=
  SourceCycleBase.source_isBase _ d

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
