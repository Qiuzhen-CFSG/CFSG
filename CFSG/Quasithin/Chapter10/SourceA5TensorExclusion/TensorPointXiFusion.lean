module
public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.TensorPointPairs
public import CFSG.Quasithin.Chapter1.Section03.XiFusion

/-!
# Full Xi fusion at the original tensor point

For either odd Xi quotient, a normalizer of the actual fixed subspace W
moving the point to a second field line identifies X with its conjugate.
The two original diagonal point residuals generate L₀, so L₀ normalizes X.
This includes the extraspecial quotient and its common Frattini-line case.

The earlier Xi construction supplies X and W; the point geometry supplies
the literal conjugating element. Source: Aschbacher--Smith, proof of 9.4.1,
printed pp.735--736.
-/

public section
open Subgroup Theory.GroupTheory Representation
namespace CFSG.Quasithin.Chapter10.SourceA5TensorModel
open Chapter3.Section02 ClassicalOrthogonal.FourPlusMatrix
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L}
  {e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)}
  (m : SourceA5TensorModel D e)

/-- The full Xi fusion step of source 9.4.1 makes L₀ act on
the original Xi subgroup. All conjugation and point residuals are literal. -/
theorem tensorPoint_Xi_orbit_normalizes
    {R X W : Subgroup G} (hX : Chapter1.XiMember R X)
    (v w : D.fullModule)
    (hv : ((m.sectionData.coordinates v).toAdd).det ≠ 0)
    (hw : ((m.sectionData.coordinates w).toAdd).det ≠ 0)
    (hne : (m.sectionData.coordinates w).toAdd ∉
      Submodule.span Binary.F ({(m.sectionData.coordinates v).toAdd} : Set Binary.V))
    (hvW : (v : G) ∈ W) (hXW : X ≤ centralizer (W : Set G))
    (hNv : centralizer ({(v : G)} : Set G) ≤ normalizer (X : Set G))
    (g : G) (hg : g ∈ normalizer (W : Set G))
    (hconj : MulAut.conj g (v : G) = (w : G))
    (hRw : R ≤ centralizer ({(w : G)} : Set G)) :
    X = X.map (MulAut.conj g).toMonoidHom ∧
      localOrbit T L ≤ normalizer (X : Set G) := by
  let _ := m.fullModule_elementary
  have hv2 : orderOf (v : G) = 2 := by
    apply orderOf_eq_prime (elemPow_eq_one_of_isElementaryAbelian (v : G) v.property)
    intro heq
    have hv' : v = 1 := Subtype.ext heq
    simp only [hv', map_one] at hv
    exact hv Matrix.det_zero
  obtain ⟨heq, hNw⟩ := hX.eq_conjugate_at_point
    D.simpleQTKE.quasithin hv2 hvW hXW hNv hg hconj hRw
  refine ⟨heq, ?_⟩
  rw [← m.tensorPointResidual_pair_sup v w hv hw hne]
  exact sup_le ((m.tensorPointResidual_le_centralizer v).trans hNv)
    ((m.tensorPointResidual_le_centralizer w).trans hNw)

end CFSG.Quasithin.Chapter10.SourceA5TensorModel
