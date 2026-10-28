module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.MathieuJ4RecognitionApplication
public import Theory.GroupTheory.Recognition.JankoFour.SourceIncidence.TriangleSymmetry

/-!
# Triangles and common neighbors for the original Mathieu witness

Apply the source geometry to the same IsTypeJ4 witness and the same marked
LocalData used by the original Mathieu application. The four conclusions
are unchanged Input fields: triangles lie in planes, all triangle permutations
are induced, all three vertices read the same line label, and common neighbors
of a nonadjacent pair lie in its unique plane. No geometric callback is added.
Ambient simplicity is retained from Hypothesis 12.2.3 for point faithfulness.
The remaining neighbor counts, radical stabilizer action and generation are
still required before Input can be assembled.

Source: Aschbacher–Segev (1991), (5.5)–(5.7), p.601.
-/
public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open Sporadic.Mathieu MathieuCode
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open ChapterE Chapter7.NormalizedSource Chapter8.Section02.Centralizer
open Recognition.JankoFour SourceCycleBase
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)

/-- The complete triangle and common-neighbor clauses on the original data. -/
theorem sourceOrbit_m24_incidence_triangles
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
    (∀ x y u, Adj data.L x y → Adj data.L y u → Adj data.L u x →
      ∃ π, OnPlane data.P x π ∧ OnPlane data.P y π ∧ OnPlane data.P u π) ∧
    (∀ x y u, Adj data.L x y → Adj data.L y u → Adj data.L u x →
      ∀ σ : Equiv.Perm (Fin 3), ∃ g : G,
        ∀ i : Fin 3, g • (![x,y,u] : Fin 3 → Point data.P) i =
          (![x,y,u] : Fin 3 → Point data.P) (σ i)) ∧
    (∀ x y u l m n (i : Fin 5),
      Adj data.L x y → Adj data.L y u → Adj data.L u x →
      OnLine data.L x l → OnLine data.L y l → OnLine data.L x m →
      OnLine data.L u m → OnLine data.L y n → OnLine data.L u n →
      (LineType data.residueChart i x l m ↔ LineType data.residueChart i y l n)) ∧
    (∀ x y π, DistanceTwo data.L x y → OnPlane data.P x π → OnPlane data.P y π →
      ∀ u, Adj data.L x u → Adj data.L y u → OnPlane data.P u π) := by
  let : IsSimpleGroup G := h.simpleQTKE.simple
  exact ⟨data.point_corefree,data.triangles_in_plane,data.triangle_permutations,
    data.triangle_labels,data.common_neighbors_in_plane⟩
end CFSG.Quasithin.Chapter12.Section02.ChosenModule
