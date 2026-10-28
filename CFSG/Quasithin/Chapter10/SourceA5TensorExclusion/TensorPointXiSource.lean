module
public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.TensorPointPairs
public import CFSG.Quasithin.Chapter1.Section03.ElementaryFusion

/-!
# The elementary Xi fusion branch at an actual tensor point

The normal Xi subgroup at the original nonsingular point centralizes W = V₁V_N.
A conjugating element preserving W and moving the point to another field
line gives two mutually normalizing Xi conjugates. When the odd quotient
is elementary, rank-two rigidity identifies them. The actual diagonal
point residuals then show that the original component orbit L₀ normalizes X.

The input subgroup W and the point-conjugacy witness are the ones in the
source; neither an abstract replacement module nor point normality is an
assumption. The preceding U/image-equality construction and the remaining
extraspecial-quotient and degree-two action arguments are independent steps.
Source: Aschbacher--Smith 9.4.1, printed pp.735--736.
-/

public section
open Subgroup Theory.GroupTheory Representation
namespace CFSG.Quasithin.Chapter10.SourceA5TensorModel
open Chapter3.Section02 ClassicalOrthogonal.FourPlusMatrix
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L}
  {e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)}
  (m : SourceA5TensorModel D e)

/-- The elementary odd-quotient branch of source 9.4.1 makes L₀ act on
the original Xi subgroup. All conjugation and point residuals are literal. -/
theorem tensorPoint_Xi_orbit_normalizes_of_elementary_quotient
    {p : ℕ} [Fact p.Prime] (ho : Odd p)
    {R X W : Subgroup G} (hX : Chapter1.XiMember R X)
    (he : IsElementaryAbelian p (Chapter1.XiQuotient X))
    (hc : Nat.card (Chapter1.XiQuotient X) = p ^ 2)
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
  obtain ⟨heq, hNw⟩ := hX.eq_conjugate_at_point_of_elementary_quotient
    D.simpleQTKE.quasithin ho he hc hv2 hvW hXW hNv hg hconj hRw
  refine ⟨heq, ?_⟩
  rw [← m.tensorPointResidual_pair_sup v w hv hw hne]
  exact sup_le ((m.tensorPointResidual_le_centralizer v).trans hNv)
    ((m.tensorPointResidual_le_centralizer w).trans hNw)

end CFSG.Quasithin.Chapter10.SourceA5TensorModel
