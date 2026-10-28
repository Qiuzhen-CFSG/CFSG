module

public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.MathieuJ4RecognitionApplication
public import Theory.GroupTheory.Recognition.JankoFour.SourceIncidence

/-!
# The original Mathieu witness and AS91 incidence consequences

Apply the proved incidence clauses to the exact IsTypeJ4 witness constructed
from the original marked Mathieu arguments, retaining the full cubic quotient.
The only extra data are the explicit earlier-section `LocalData` for that
witness. Ambient simplicity is obtained from Hypothesis 12.2.3 itself.

The original seven clauses are retained. The additional application supplies
the literal plane chart, flag transitivity, edge element, line transitivity
and five-point action kernel. The point-residue chart, plane-point maximality,
and radical transitivity, regularity and neighbor faithfulness are also constructed.
The same natural module now gives neighboring-radical intersections, unique lines,
plane closure and the exact plane-edge orbit.
The 1/60/16 plane orbits, all three point–line orbit types, and the edge fixer
are now derived through the same original quotient maps.
The radical now maps onto the original hexad kernel and is transitive on the
sixteen nonneighbors, with stabilizer E∩Q of order 128 and the actual overlap
supplement. The point-side overlap is maximal; its kernel normalizer proves
ambient plane uniqueness. Nonadjacent point radicals meet exactly in the
plane-marker subgroup, supplying source (6.2), with the standing marker-class
hypothesis retained in the exact conjugate-map form used by fusion. All three residues are connected; ambient connectivity follows once generation
is supplied. The five points on a line admit every permutation while incident
planes are fixed, and the original Todd chart transports every native label.
The first three labels are now exactly coplanarity, and plane markers fix
every common neighbor of a nonadjacent point pair. The remaining orbital,
triangle and common-neighbor geometry and ambient generation still require proof; the independent fusion
owner retains (6.3)–(6.5)(2), and LocalData remains with the section 4 producer.
Neither Input nor a recognition implication is a hypothesis, and no J₄
exclusion is used.

Source: AS91 (5.1)–(5.2), (6.1); Aschbacher–Smith 8.2.12–14, pp.722–723.
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

/-- Seven actual Input clauses for the same original marker and Mathieu witness. -/
theorem sourceOrbit_m24_incidence_consequences
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
    (hquot : Nonempty (Recognition.JankoFour.CubicAutomorphismQuotient
      ((centralizer ({(z : G)} : Set G)) ⧸
        pCore 2 (centralizer ({(z : G)} : Set G)))))
    (data : SourceIncidence.LocalData
      (D.sourceOrbit_m24_isTypeJ4 h hmany hV hq hnon a E hE z hz hne hquot)) :
    data.P.M.normalCore = ⊥ ∧
    (∀ l : SourceCycleBase.Line data.L,
      {x | SourceCycleBase.OnLine data.L x l}.ncard = 5) ∧
    (∀ π : SourceCycleBase.Plane (z : G),
      {x | SourceCycleBase.OnPlane data.P x π}.ncard = 77) ∧
    (∀ x l π, SourceCycleBase.OnLine data.L x l →
      SourceCycleBase.LineOnPlane data.L l π → SourceCycleBase.OnPlane data.P x π) ∧
    (∀ x (u : SourceCycleBase.coreAt data.P x) l,
      SourceCycleBase.OnLine data.L x l → (u : G) • l = l) ∧
    (∀ x (u : SourceCycleBase.coreAt data.P x) π,
      SourceCycleBase.OnPlane data.P x π → (u : G) • π = π) ∧
    (∀ π x, SourceCycleBase.marker π ∈ SourceCycleBase.coreAt data.P x ↔
      SourceCycleBase.OnPlane data.P x π) := by
  let : IsSimpleGroup G := h.simpleQTKE.simple
  exact SourceIncidence.source_incidence_consequences
    (D.sourceOrbit_m24_isTypeJ4 h hmany hV hq hnon a E hE z hz hne hquot) data


/-- Actual plane chart, flag transitivity and five-point action for the original
Mathieu marker. Ambient simplicity is inherited from Hypothesis 12.2.3. -/
theorem sourceOrbit_m24_incidence_flags
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
    (hquot : Nonempty (Recognition.JankoFour.CubicAutomorphismQuotient
      ((centralizer ({(z : G)} : Set G)) ⧸
        pCore 2 (centralizer ({(z : G)} : Set G)))))
    (data : SourceIncidence.LocalData
      (D.sourceOrbit_m24_isTypeJ4 h hmany hV hq hnon a E hE z hz hne hquot)) :
    data.P.M.normalCore = ⊥ ∧
    Nonempty (SourceCycleBase.PlaneChart data.P data.L) ∧
    (∀ x l π, SourceCycleBase.OnLine data.L x l → SourceCycleBase.OnPlane data.P x π →
      SourceCycleBase.LineOnPlane data.L l π →
      ∃ g : G, GraphUniquenessSystem.Cosets.vertex data.P.M g = x ∧
        GraphUniquenessSystem.Cosets.vertex data.L.G₂ g = l ∧
        GraphUniquenessSystem.Cosets.vertex (Recognition.JankoFour.centralizer (z : G)) g = π) ∧
    (∃ t : G, t ∈ Recognition.JankoFour.centralizer (z : G) ∧ t ∈ data.L.G₂ ∧
      t ∉ data.P.M ∧ t*t ∈ data.P.M ∧
      GraphUniquenessSystem.Cosets.LineTransitive data.P.M t data.L.G₂) ∧
    (∀ g : data.L.G₂,
      (∀ x : SourceCycleBase.Point data.P,
        SourceCycleBase.OnLine data.L x (GraphUniquenessSystem.Cosets.vertex data.L.G₂ 1) →
        (g : G) • x = x) ↔ (g : G) ∈ data.d.K) := by
  let : IsSimpleGroup G := h.simpleQTKE.simple
  exact SourceIncidence.source_incidence_flags
    (D.sourceOrbit_m24_isTypeJ4 h hmany hV hq hnon a E hE z hz hne hquot) data

/-- The actual Todd residue and radical actions for the same original Mathieu
witness. No chart, incidence relation, or transitivity conclusion is assumed. -/
theorem sourceOrbit_m24_incidence_residue_actions
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
    (hquot : Nonempty (Recognition.JankoFour.CubicAutomorphismQuotient
      ((centralizer ({(z : G)} : Set G)) ⧸
        pCore 2 (centralizer ({(z : G)} : Set G)))))
    (data : SourceIncidence.LocalData
      (D.sourceOrbit_m24_isTypeJ4 h hmany hV hq hnon a E hE z hz hne hquot)) :
    data.P.M.normalCore = ⊥ ∧
    Nonempty (SourceCycleBase.ResidueChart data.P data.L) ∧
    IsCoatom (data.P.M.subgroupOf (Recognition.JankoFour.centralizer (z : G))) ∧
    (∀ x l, SourceCycleBase.OnLine data.L x l → ∀ y b,
      SourceCycleBase.OnLine data.L y l → y ≠ x → SourceCycleBase.OnLine data.L b l → b ≠ x →
        ∃ u : SourceCycleBase.coreAt data.P x, (u : G) • y = b) ∧
    (∀ x l, SourceCycleBase.OnLine data.L x l → ∀ (u : SourceCycleBase.coreAt data.P x) y,
      SourceCycleBase.OnLine data.L y l → y ≠ x → (u : G) • y = y →
        ∀ b, SourceCycleBase.OnLine data.L b l → (u : G) • b = b) ∧
    (∀ x (u : SourceCycleBase.coreAt data.P x),
      (∀ y, SourceCycleBase.Adj data.L x y → (u : G) • y = y) → (u : G) = 1) := by
  let : IsSimpleGroup G := h.simpleQTKE.simple
  exact SourceIncidence.source_incidence_residue_actions
    (D.sourceOrbit_m24_isTypeJ4 h hmany hV hq hnon a E hE z hz hne hquot) data


/-- Neighboring-radical intersections and the resulting incidence clauses for
exactly the original Mathieu witness, with its inherited ambient simplicity. -/
theorem sourceOrbit_m24_incidence_line_closure
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
    (hquot : Nonempty (Recognition.JankoFour.CubicAutomorphismQuotient
      ((centralizer ({(z : G)} : Set G)) ⧸
        pCore 2 (centralizer ({(z : G)} : Set G)))))
    (data : SourceIncidence.LocalData
      (D.sourceOrbit_m24_isTypeJ4 h hmany hV hq hnon a E hE z hz hne hquot)) :
    data.P.M.normalCore = ⊥ ∧
    (∀ y : SourceCycleBase.Point data.P, SourceCycleBase.OnLine data.L y (GraphUniquenessSystem.Cosets.vertex data.L.G₂ 1) →
      y ≠ GraphUniquenessSystem.Cosets.vertex data.P.M 1 →
      data.P.E ⊓ SourceCycleBase.coreAt data.P y = data.d.space ∧
        ((MulAction.stabilizer G y).subgroupOf data.P.E).index = 4) ∧
    Nat.card (data.d.R.subgroupOf data.P.E) = 512 ∧
    (∀ x y, SourceCycleBase.Adj data.L x y → ∃! l, SourceCycleBase.OnLine data.L x l ∧ SourceCycleBase.OnLine data.L y l) ∧
    (∀ x y l π, x ≠ y → SourceCycleBase.OnLine data.L x l → SourceCycleBase.OnLine data.L y l →
      SourceCycleBase.OnPlane data.P x π → SourceCycleBase.OnPlane data.P y π → SourceCycleBase.LineOnPlane data.L l π) ∧
    (∃ t : G, t ∈ Recognition.JankoFour.centralizer (z : G) ∧ t ∈ data.L.G₂ ∧ t ∉ data.P.M ∧ t*t ∈ data.P.M ∧
      GraphUniquenessSystem.Cosets.LineTransitive data.P.M t data.L.G₂ ∧
      ∀ x y, (∃ k : Recognition.JankoFour.centralizer (z : G),
        ((k : G) • GraphUniquenessSystem.Cosets.vertex data.P.M 1 = x ∧
          (k : G) • GraphUniquenessSystem.Cosets.vertex data.P.M t = y) ∨
        ((k : G) • GraphUniquenessSystem.Cosets.vertex data.P.M 1 = y ∧
          (k : G) • GraphUniquenessSystem.Cosets.vertex data.P.M t = x)) ↔
        SourceCycleBase.Adj data.L x y ∧ SourceCycleBase.OnPlane data.P x (GraphUniquenessSystem.Cosets.vertex (Recognition.JankoFour.centralizer (z : G)) 1) ∧
          SourceCycleBase.OnPlane data.P y (GraphUniquenessSystem.Cosets.vertex (Recognition.JankoFour.centralizer (z : G)) 1)) := by
  let : IsSimpleGroup G := h.simpleQTKE.simple
  exact SourceIncidence.source_incidence_line_closure
    (D.sourceOrbit_m24_isTypeJ4 h hmany hV hq hnon a E hE z hz hne hquot) data

/-- The seven further unchanged Input clauses for the same original Mathieu
witness: plane rank three, the three point–line orbits, and the edge fixer.
Ambient simplicity is inherited from the original Hypothesis 12.2.3. -/
theorem sourceOrbit_m24_incidence_plane_orbits
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
    (hquot : Nonempty (Recognition.JankoFour.CubicAutomorphismQuotient
      ((centralizer ({(z : G)} : Set G)) ⧸
        pCore 2 (centralizer ({(z : G)} : Set G)))))
    (data : SourceIncidence.LocalData
      (D.sourceOrbit_m24_isTypeJ4 h hmany hV hq hnon a E hE z hz hne hquot)) :
    data.P.M.normalCore = ⊥ ∧
    (∀ π x, SourceCycleBase.OnPlane data.P x π → {y | SourceCycleBase.OnPlane data.P y π ∧ SourceCycleBase.Adj data.L x y}.ncard = 60) ∧
    (∀ π x, SourceCycleBase.OnPlane data.P x π → {y | SourceCycleBase.OnPlane data.P y π ∧ y ≠ x ∧ ¬ SourceCycleBase.Adj data.L x y}.ncard = 16) ∧
    (∀ π x u v, SourceCycleBase.OnPlane data.P x π → SourceCycleBase.OnPlane data.P u π → SourceCycleBase.OnPlane data.P v π →
      ((u = x ↔ v = x) ∧ (SourceCycleBase.Adj data.L x u ↔ SourceCycleBase.Adj data.L x v)) →
      ∃ g : G, g • π = π ∧ g • x = x ∧ g • u = v) ∧
    (∀ π x l, SourceCycleBase.OnPlane data.P x π → SourceCycleBase.LineOnPlane data.L l π →
      ∃ i : Fin 3, SourceCycleBase.PlanePairType data.L i x l) ∧
    (∀ π x y l m (i : Fin 3), SourceCycleBase.OnPlane data.P x π → SourceCycleBase.OnPlane data.P y π →
      SourceCycleBase.LineOnPlane data.L l π → SourceCycleBase.LineOnPlane data.L m π →
      SourceCycleBase.PlanePairType data.L i x l → SourceCycleBase.PlanePairType data.L i y m →
      ∃ g : G, g • π = π ∧ g • x = y ∧ g • l = m) ∧
    (∀ π x, SourceCycleBase.OnPlane data.P x π → ∀ i : Fin 3,
      ∃ l, SourceCycleBase.LineOnPlane data.L l π ∧ SourceCycleBase.PlanePairType data.L i x l) ∧
    (∀ t : G, t ∈ data.L.G₂ →
      ¬ data.P.M ⊓ data.P.M.comap (MulAut.conj t⁻¹).toMonoidHom ≤ Recognition.JankoFour.centralizer (z : G)) := by
  let : IsSimpleGroup G := h.simpleQTKE.simple
  exact SourceIncidence.source_incidence_plane_orbits
    (D.sourceOrbit_m24_isTypeJ4 h hmany hV hq hnon a E hE z hz hne hquot) data

/-- The exact original Mathieu witness supplies the radical's actual
sixteen-point orbit and its order-128 kernel; no geometry is assumed. -/
theorem sourceOrbit_m24_incidence_nonneighbor_radical
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
    (hquot : Nonempty (Recognition.JankoFour.CubicAutomorphismQuotient
      ((centralizer ({(z : G)} : Set G)) ⧸
        pCore 2 (centralizer ({(z : G)} : Set G)))))
    (data : SourceIncidence.LocalData
      (D.sourceOrbit_m24_isTypeJ4 h hmany hV hq hnon a E hE z hz hne hquot)) :
    data.P.M.normalCore = ⊥ ∧
    data.radicalDesign.range = (Sporadic.Mathieu.m22HexadPointwiseKernel data.P.hexad).map
      Sporadic.Mathieu.M22ValueBound.Concrete.inclusion ∧
    data.radicalDesign.ker = (Recognition.JankoFour.ambientCore (z : G)).subgroupOf data.P.E ∧
    Nat.card (data.P.E ⊓ Recognition.JankoFour.ambientCore (z : G) : Subgroup G) = 128 ∧
    ∀ u : SourceCycleBase.Point data.P, SourceCycleBase.OnPlane data.P u (GraphUniquenessSystem.Cosets.vertex (Recognition.JankoFour.centralizer (z : G)) 1) →
      u ≠ GraphUniquenessSystem.Cosets.vertex data.P.M 1 →
      ¬ SourceCycleBase.Adj data.L (GraphUniquenessSystem.Cosets.vertex data.P.M 1) u →
      (∀ v : SourceCycleBase.Point data.P, SourceCycleBase.OnPlane data.P v (GraphUniquenessSystem.Cosets.vertex (Recognition.JankoFour.centralizer (z : G)) 1) →
        v ≠ GraphUniquenessSystem.Cosets.vertex data.P.M 1 →
        ¬ SourceCycleBase.Adj data.L (GraphUniquenessSystem.Cosets.vertex data.P.M 1) v →
        ∃ e : data.P.E, (e : G) • u = v) ∧
      (MulAction.stabilizer G u).subgroupOf data.P.E = (Recognition.JankoFour.ambientCore (z : G)).subgroupOf data.P.E ∧
      Nat.card ((MulAction.stabilizer G u).subgroupOf data.P.E) = 128 ∧
      (∀ m ∈ data.P.M ⊓ Recognition.JankoFour.centralizer (z : G),
        ∃ e : data.P.E, ∃ k ∈ data.P.M ⊓ Recognition.JankoFour.centralizer (z : G) ⊓ MulAction.stabilizer G u,
          m = (e : G)*k) ∧
      data.P.M ⊓ MulAction.stabilizer G u ≤
        normalizer ((data.P.E ⊓ Recognition.JankoFour.ambientCore (z : G) : Subgroup G) : Set G) := by
  let : IsSimpleGroup G := h.simpleQTKE.simple
  exact SourceIncidence.source_incidence_nonneighbor_radical
    (D.sourceOrbit_m24_isTypeJ4 h hmany hV hq hnon a E hE z hz hne hquot) data

/-- The original Mathieu witness satisfies point-side maximality and ambient
plane uniqueness, with the same earlier LocalData and original simplicity. -/
theorem sourceOrbit_m24_incidence_plane_uniqueness
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
    (hquot : Nonempty (Recognition.JankoFour.CubicAutomorphismQuotient
      ((centralizer ({(z : G)} : Set G)) ⧸
        pCore 2 (centralizer ({(z : G)} : Set G)))))
    (data : SourceIncidence.LocalData
      (D.sourceOrbit_m24_isTypeJ4 h hmany hV hq hnon a E hE z hz hne hquot)) :
    data.P.M.normalCore = ⊥ ∧
    IsCoatom ((Recognition.JankoFour.centralizer (z : G)).subgroupOf data.P.M) ∧
    data.P.M ⊓ normalizer ((data.P.E ⊓ Recognition.JankoFour.ambientCore (z : G) : Subgroup G) : Set G) =
      data.P.M ⊓ Recognition.JankoFour.centralizer (z : G) ∧
    (∀ u : SourceCycleBase.Point data.P,
      SourceCycleBase.OnPlane data.P u (GraphUniquenessSystem.Cosets.vertex (Recognition.JankoFour.centralizer (z : G)) 1) →
      u ≠ GraphUniquenessSystem.Cosets.vertex data.P.M 1 →
      ¬ SourceCycleBase.Adj data.L (GraphUniquenessSystem.Cosets.vertex data.P.M 1) u →
      data.P.M ⊓ MulAction.stabilizer G u ≤ Recognition.JankoFour.centralizer (z : G)) ∧
    (∀ π x y, SourceCycleBase.OnPlane data.P x π → SourceCycleBase.OnPlane data.P y π → x ≠ y →
      ¬ SourceCycleBase.Adj data.L x y → ∀ σ,
      SourceCycleBase.OnPlane data.P x σ → SourceCycleBase.OnPlane data.P y σ → σ = π) := by
  let : IsSimpleGroup G := h.simpleQTKE.simple
  exact SourceIncidence.source_incidence_plane_uniqueness
    (D.sourceOrbit_m24_isTypeJ4 h hmany hV hq hnon a E hE z hz hne hquot) data

/-- Source (6.2) for the original Mathieu witness, with the actual radicals
and the precise marker-conjugate premise needed by the fusion constructor. -/
theorem sourceOrbit_m24_incidence_core_intersections
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
    (hquot : Nonempty (Recognition.JankoFour.CubicAutomorphismQuotient
      ((centralizer ({(z : G)} : Set G)) ⧸
        pCore 2 (centralizer ({(z : G)} : Set G)))))
    (data : SourceIncidence.LocalData
      (D.sourceOrbit_m24_isTypeJ4 h hmany hV hq hnon a E hE z hz hne hquot)) :
    data.P.M.normalCore = ⊥ ∧
    (∀ π x y, SourceCycleBase.OnPlane data.P x π → SourceCycleBase.OnPlane data.P y π → x ≠ y →
      ¬ SourceCycleBase.Adj data.L x y →
      SourceCycleBase.coreAt data.P x ⊓ SourceCycleBase.coreAt data.P y = zpowers (SourceCycleBase.marker π)) ∧
    (∀ x y, (∃ w ∈ SourceCycleBase.coreAt data.P x ⊓ SourceCycleBase.coreAt data.P y, IsConj (z : G) w) →
      x = y ∨ SourceCycleBase.Adj data.L x y ∨ SourceCycleBase.PlaneDistanceTwo data.L x y) ∧
    (∀ g : G, data.P.E.map (MulAut.conj g).toMonoidHom ≠ data.P.E →
      (∃ w ∈ data.P.E ⊓ data.P.E.map (MulAut.conj g).toMonoidHom, IsConj (z : G) w) →
      ∀ v ∈ data.P.E ⊓ data.P.E.map (MulAut.conj g).toMonoidHom, v ≠ 1 → IsConj (z : G) v) := by
  let : IsSimpleGroup G := h.simpleQTKE.simple
  exact SourceIncidence.source_incidence_core_intersections
    (D.sourceOrbit_m24_isTypeJ4 h hmany hV hq hnon a E hE z hz hne hquot) data

/-- All residues of the original Mathieu incidence geometry are connected.
The ambient connectedness implication retains precisely source (6.5)(2). -/
theorem sourceOrbit_m24_incidence_connectivity
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
    (hquot : Nonempty (Recognition.JankoFour.CubicAutomorphismQuotient
      ((centralizer ({(z : G)} : Set G)) ⧸
        pCore 2 (centralizer ({(z : G)} : Set G)))))
    (data : SourceIncidence.LocalData
      (D.sourceOrbit_m24_isTypeJ4 h hmany hV hq hnon a E hE z hz hne hquot)) :
    data.P.M.normalCore = ⊥ ∧
    (∀ u : SourceCycleBase.Object data.L,
      ((SourceCycleBase.incidenceGraph data.L).induce
        {v | SourceCycleBase.IncidentObject data.L u v}).Connected) ∧
    (Recognition.JankoFour.centralizer (z : G) ⊔ data.P.M = ⊤ →
      (SourceCycleBase.incidenceGraph data.L).Connected) := by
  let : IsSimpleGroup G := h.simpleQTKE.simple
  exact SourceIncidence.source_incidence_connectivity
    (D.sourceOrbit_m24_isTypeJ4 h hmany hV hq hnon a E hE z hz hne hquot) data

/-- The collinear triangle branch, zero orbital and plane-marker fixation
for the same original Mathieu witness. -/
theorem sourceOrbit_m24_incidence_line_permutations
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
    (hquot : Nonempty (Recognition.JankoFour.CubicAutomorphismQuotient
      ((centralizer ({(z : G)} : Set G)) ⧸
        pCore 2 (centralizer ({(z : G)} : Set G)))))
    (data : SourceIncidence.LocalData
      (D.sourceOrbit_m24_isTypeJ4 h hmany hV hq hnon a E hE z hz hne hquot)) :
    data.P.M.normalCore = ⊥ ∧
    (∀ x l k, SourceCycleBase.LineType data.residueChart 0 x l k ↔
      SourceCycleBase.OnLine data.L x l ∧ k = l) ∧
    (∀ (l : SourceCycleBase.Line data.L) (v : Fin 3 → SourceCycleBase.Point data.P),
      Function.Injective v → (∀ i, SourceCycleBase.OnLine data.L (v i) l) →
      ∀ σ : Equiv.Perm (Fin 3), ∃ g : G, g • l = l ∧
        (∀ π, SourceCycleBase.LineOnPlane data.L l π → g • π = π) ∧
        ∀ i : Fin 3, g • v i = v (σ i)) ∧
    (∀ x y π, SourceCycleBase.DistanceTwo data.L x y →
      SourceCycleBase.OnPlane data.P x π → SourceCycleBase.OnPlane data.P y π →
      ∀ u, SourceCycleBase.Adj data.L x u → SourceCycleBase.Adj data.L y u →
        SourceCycleBase.marker π • u = u) := by
  let : IsSimpleGroup G := h.simpleQTKE.simple
  exact SourceIncidence.source_incidence_line_permutations
    (D.sourceOrbit_m24_isTypeJ4 h hmany hV hq hnon a E hE z hz hne hquot) data

/-- The actual native labels and valencies for the same original Mathieu
witness, using one Todd projection and the original left-coset convention. -/
theorem sourceOrbit_m24_incidence_line_types
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
    (hquot : Nonempty (Recognition.JankoFour.CubicAutomorphismQuotient
      ((centralizer ({(z : G)} : Set G)) ⧸
        pCore 2 (centralizer ({(z : G)} : Set G)))))
    (data : SourceIncidence.LocalData
      (D.sourceOrbit_m24_isTypeJ4 h hmany hV hq hnon a E hE z hz hne hquot)) :
    data.P.M.normalCore = ⊥ ∧
    (∀ (i : Fin 5) (x : SourceCycleBase.Point data.P)
      (l m : {l : SourceCycleBase.Line data.L // SourceCycleBase.OnLine data.L x l}),
      SourceCycleBase.LineType data.residueChart i x l.val m.val ↔
        SourceCycleBase.Native.Delta i
          (data.residueChart.linesAt x l) (data.residueChart.linesAt x m)) ∧
    (∀ (i : Fin 5) (x : SourceCycleBase.Point data.P)
      (l : {l : SourceCycleBase.Line data.L // SourceCycleBase.OnLine data.L x l}),
      {m | SourceCycleBase.LineType data.residueChart i x l.val m}.ncard =
        {m | SourceCycleBase.Native.Delta i (data.residueChart.linesAt x l) m}.ncard) := by
  let : IsSimpleGroup G := h.simpleQTKE.simple
  exact SourceIncidence.source_incidence_line_types
    (D.sourceOrbit_m24_isTypeJ4 h hmany hV hq hnon a E hE z hz hne hquot) data

/-- The literal first three line labels are precisely coplanarity for the
same original Mathieu witness, with ambient simplicity retained. -/
theorem sourceOrbit_m24_incidence_coplanarity
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
    (hquot : Nonempty (Recognition.JankoFour.CubicAutomorphismQuotient
      ((centralizer ({(z : G)} : Set G)) ⧸
        pCore 2 (centralizer ({(z : G)} : Set G)))))
    (data : SourceIncidence.LocalData
      (D.sourceOrbit_m24_isTypeJ4 h hmany hV hq hnon a E hE z hz hne hquot)) :
    data.P.M.normalCore = ⊥ ∧
    (∀ x l m, SourceCycleBase.OnLine data.L x l → SourceCycleBase.OnLine data.L x m →
      (SourceCycleBase.Coplanar data.L l m ↔ ∃ i : Fin 5, i.val ≤ 2 ∧
        SourceCycleBase.LineType data.residueChart i x l m)) := by
  let : IsSimpleGroup G := h.simpleQTKE.simple
  exact SourceIncidence.source_incidence_coplanarity
    (D.sourceOrbit_m24_isTypeJ4 h hmany hV hq hnon a E hE z hz hne hquot) data

/-- The five actual line orbits and exact valencies for the original Mathieu
witness, retaining its LocalData, Todd projection and ambient simplicity. -/
theorem sourceOrbit_m24_incidence_orbitals
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
    (hquot : Nonempty (Recognition.JankoFour.CubicAutomorphismQuotient
      ((centralizer ({(z : G)} : Set G)) ⧸
        pCore 2 (centralizer ({(z : G)} : Set G)))))
    (data : SourceIncidence.LocalData
      (D.sourceOrbit_m24_isTypeJ4 h hmany hV hq hnon a E hE z hz hne hquot)) :
    data.P.M.normalCore = ⊥ ∧
    (∀ x l k, SourceCycleBase.OnLine data.L x l → SourceCycleBase.OnLine data.L x k →
      ∃! i : Fin 5, SourceCycleBase.LineType data.residueChart i x l k) ∧
    (∀ x l k m (i : Fin 5),
      SourceCycleBase.LineType data.residueChart i x l k →
      SourceCycleBase.LineType data.residueChart i x l m →
      ∃ g : G, g • x = x ∧ g • l = l ∧ g • k = m) ∧
    (∀ x l, SourceCycleBase.OnLine data.L x l → ∀ i : Fin 5,
      {k | SourceCycleBase.LineType data.residueChart i x l k}.ncard =
        (![1,42,56,1008,2688] : Fin 5 → ℕ) i) ∧
    (∀ x l k (i : Fin 5), SourceCycleBase.LineType data.residueChart i x l k →
      SourceCycleBase.LineType data.residueChart i x k l ∧
      ∃ g : G, g • x = x ∧ g • l = k ∧ g • k = l) := by
  let : IsSimpleGroup G := h.simpleQTKE.simple
  exact SourceIncidence.source_incidence_orbitals
    (D.sourceOrbit_m24_isTypeJ4 h hmany hV hq hnon a E hE z hz hne hquot) data

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
