module

public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Symplectic.Algebra
public import Theory.GroupTheory.PCoreImage
public import Theory.GroupTheory.PCoreRestriction

/-!
# The initial Cartan bound in the symplectic closure argument

The preceding equality V=[V,X] and 11.5.6(5) place V in O₂(KT).
Restriction of that core bounds [V,K] by O₂(K). Part (4) applies to V
because its Frattini subgroup is trivial, and bounds [V,Y] by O₂(Y).
Both cores lie in O₂(KY) by relative normality. The marked TI argument
then puts V and its actual G₁-closure in O₂(G₁).

The premises are the preceding source conclusions, not the Cartan bound
being proved. In particular K is not identified with L₁.
Source: Aschbacher--Smith 11.5.6(4--5) and 11.5.7, printed pp.781--783.
-/

public noncomputable section
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Symplectic
open Subgroup
open CFSG.Quasithin.Chapter12.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : ChosenModule T L V} (E : Geometry D)

/-- Y is relatively normal in G₁, including its quotient-action kernel factor. -/
theorem G₁_normalizes_Y : E.G₁ ≤ normalizer (E.Y : Set G) :=
  (le_inf (normalizer_le_normalizer_centralizer E.V₁)
    (E.G₁_normalizes_K.trans (normalizer_normalizes_coreQuotientCentralizer E.K))).trans
    inf_normalizer_le_normalizer_inf

/-- Part (5) of 11.5.6, applied to the preceding equality V=[V,X]. -/
theorem seed_le_KT_core
    (hVX : ⁅V, E.X⁆ = V)
    (hfive : ⁅(L ⊔ (T : Subgroup G)).pCoreIn 2, E.X⁆ ≤
      (E.K ⊔ (T : Subgroup G)).pCoreIn 2) :
    V ≤ (E.K ⊔ (T : Subgroup G)).pCoreIn 2 := by
  exact hVX.ge.trans ((commutator_mono D.le_core le_rfl).trans hfive)

/-- The K part of the Cartan bound, with the original local cores. -/
theorem seed_commutator_K_le_core (m : MarkedFlag E)
    (hVX : ⁅V, E.X⁆ = V)
    (hfive : ⁅(L ⊔ (T : Subgroup G)).pCoreIn 2, E.X⁆ ≤
      (E.K ⊔ (T : Subgroup G)).pCoreIn 2) :
    ⁅V, E.K⁆ ≤ E.K.pCoreIn 2 := by
  have hVK : V ≤ normalizer (E.K : Set G) :=
    (D.le_sylow.trans m.sylow_le_point_normalizer).trans E.G₁_normalizes_K
  have hKQ : E.K ≤ normalizer
      (((E.K ⊔ (T : Subgroup G)).pCoreIn 2) : Set G) :=
    (le_sup_left.trans (E.K ⊔ (T : Subgroup G)).le_normalizer).trans
      (normalizer_le_normalizer_characteristic_image _ (pCore 2 _))
  apply (le_inf (le_normalizer_iff_commutator_le_right.mp hVK) ?_).trans
    (inf_pCoreIn_le_of_le 2 (show E.K ≤ E.K ⊔ (T : Subgroup G) from le_sup_left))
  exact (commutator_mono (seed_le_KT_core E hVX hfive) le_rfl).trans
    (le_normalizer_iff_commutator_le_left.mp hKQ)

/-- The literal commutator bound used in the first symplectic paragraph.
The quantified input is precisely 11.5.6(4); its Frattini premise is discharged. -/
theorem seed_commutator_KY_le_core (m : MarkedFlag E)
    (hVX : ⁅V, E.X⁆ = V)
    (hfour : ∀ P : Subgroup G, ⁅P, E.X⁆ = P → P ≤ (T : Subgroup G) →
      (frattini P).map P.subtype ≤ E.G₁.pCoreIn 2 → ⁅P, E.Y⁆ ≤ E.Y.pCoreIn 2)
    (hfive : ⁅(L ⊔ (T : Subgroup G)).pCoreIn 2, E.X⁆ ≤
      (E.K ⊔ (T : Subgroup G)).pCoreIn 2) :
    ⁅V, E.K ⊔ E.Y⁆ ≤ (E.K ⊔ E.Y).pCoreIn 2 := by
  have hPhi : (frattini V).map V.subtype = ⊥ := by
    let := D.elementary
    let : Fact (IsPGroup 2 V) := ⟨IsElementaryAbelian.isPGroup 2 V⟩
    rw [frattini_eq_bot_of_isElementaryAbelian (p := 2), Subgroup.map_bot]
  have hY := hfour V hVX D.le_sylow (by rw [hPhi]; exact bot_le)
  have hKY : E.K ⊔ E.Y ≤ E.G₁ := sup_le E.K_le_G₁ E.Y_le_G₁
  have hKcore : E.K.pCoreIn 2 ≤ (E.K ⊔ E.Y).pCoreIn 2 :=
    pCoreIn_mono_of_normalizes le_sup_left (hKY.trans E.G₁_normalizes_K)
  have hYcore : E.Y.pCoreIn 2 ≤ (E.K ⊔ E.Y).pCoreIn 2 :=
    pCoreIn_mono_of_normalizes le_sup_right (hKY.trans (G₁_normalizes_Y E))
  rw [commutator_comm]
  apply commutator_sup_le_of_relative_normal (E.K ⊔ E.Y) E.K E.Y V _
    ((E.K ⊔ E.Y).le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image _ (pCore 2 _)))
    le_sup_left le_sup_right
  · rw [commutator_comm]
    exact (seed_commutator_K_le_core E m hVX hfive).trans hKcore
  · rw [commutator_comm]
    exact hY.trans hYcore

/-- The source application: the actual V and W_H lie in O₂(G₁).
All extra inputs precede 11.5.7; no core containment of V is assumed. -/
theorem marked_seed_and_closure_le_core_of_parts_four_five (m : MarkedFlag E)
    (hti : ∀ g ∈ E.M,
      V ⊓ V.map (MulAut.conj g).toMonoidHom = ⊥ ∨
        V.map (MulAut.conj g).toMonoidHom = V)
    (hgen : E.G₁ ≤ (E.K ⊔ E.Y) ⊔ E.M₁)
    (hVX : ⁅V, E.X⁆ = V)
    (hfour : ∀ P : Subgroup G, ⁅P, E.X⁆ = P → P ≤ (T : Subgroup G) →
      (frattini P).map P.subtype ≤ E.G₁.pCoreIn 2 → ⁅P, E.Y⁆ ≤ E.Y.pCoreIn 2)
    (hfive : ⁅(L ⊔ (T : Subgroup G)).pCoreIn 2, E.X⁆ ≤
      (E.K ⊔ (T : Subgroup G)).pCoreIn 2) :
    V ≤ E.G₁.pCoreIn 2 ∧ E.W ≤ E.G₁.pCoreIn 2 :=
  marked_seed_and_closure_le_core E m hti hgen
    (seed_commutator_KY_le_core E m hVX hfour hfive)

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Symplectic
