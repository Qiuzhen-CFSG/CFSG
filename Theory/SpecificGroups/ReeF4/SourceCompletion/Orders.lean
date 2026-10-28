module
public import Theory.SpecificGroups.ReeF4.SourceCompletion.LocalGeometry
public import Theory.SpecificGroups.ReeF4.CentralCovers.OddPrimary.Order
public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.Geometry
public import Theory.GroupTheory.NormalizedSupConsequences

/-!
# Full parabolic orders for the general Ree completion count

The fixed torus has odd order and the positive subgroup is a two-group,
so their product decomposition gives the full Borel order q^12(q-1)^2.
The actual Borel indices q+1 and q²+1 then give both full parabolic orders.
The native Bruhat order factors by the Suzuki parabolic with quotient
(q+1)(q³+1)(q⁶+1). This quotient is the vertex count used in the
small-completion argument, retaining the whole Borel and q=8.

Source: GLS3 Table 2.2 and §§2.3–2.4; Aschbacher–Smith F.4.13,24,
printed pp.280,287 (`refs/quasithin.pdf`).
-/

public noncomputable section
open Subgroup
open ReeF4 ReeF4.Parabolics ReeF4.LargeLocalSeeds
open ReeF4.CentralCovers.OddPrimary.Order
namespace ReeF4.SourceCompletion
/-- Order of the entire root Borel, including both torus coordinates. -/
theorem card_borel (m : ℕ) :
    Nat.card (borel m) = (2^(2*m+1))^12 * (2^(2*m+1)-1)^2 := by
  have hn : fixedTorus m ≤ normalizer (unipotent m : Set (Model m)) := by
    rw [unipotent_normalizer_eq_borel,borel_eq_unipotent_sup_fixedTorus]
    exact le_sup_right
  have hd : Disjoint (fixedTorus m) (unipotent m) := by
    apply disjoint_of_coprime_natCard
    rw [card_unipotent,←pow_mul]
    exact (Nat.coprime_two_right.mpr
      (fixedTorus_odd_card m (splitTorus_odd_card m))).pow_right _
  have hi : (fixedTorus m).relIndex (borel m) = Nat.card (unipotent m) := by
    rw [borel_eq_unipotent_sup_fixedTorus,relIndex_sup_of_normalizes _ _ hn,
      ←inf_relIndex_right,hd.eq_bot,relIndex_bot_left]
  have hc := ((fixedTorus m).subgroupOf (borel m)).card_mul_index
  rw [Nat.card_congr (subgroupOfEquivOfLe (show fixedTorus m ≤ borel m by
    rw [borel_eq_unipotent_sup_fixedTorus]; exact le_sup_right)).toEquiv] at hc
  change Nat.card (fixedTorus m) * (fixedTorus m).relIndex (borel m) = _ at hc
  rw [hi,card_fixedTorus,card_unipotent] at hc
  exact hc.symm.trans (Nat.mul_comm _ _)

/-- The two root-defined full parabolic orders. -/
theorem card_parabolic (m : ℕ) (hm : 0 < m) (s : Side) :
    Nat.card (parabolic m s) = (2^(2*m+1))^12 * (2^(2*m+1)-1)^2 *
      ((if s = .linear then 2^(2*m+1) else (2^(2*m+1))^2) + 1) := by
  have hc := ((borel m).subgroupOf (parabolic m s)).card_mul_index
  rw [Nat.card_congr (subgroupOfEquivOfLe (borel_le_parabolic m s)).toEquiv] at hc
  change Nat.card (borel m) * (borel m).relIndex (parabolic m s) = _ at hc
  rw [card_borel,borel_relIndex m hm] at hc
  exact hc.symm

/-- Factor the native group order by the full Suzuki parabolic. -/
theorem order_factor_suzuki (m : ℕ) (hm : 0 < m) :
    Nat.card (Model m) = Nat.card (parabolic m .suzuki) *
      ((2^(2*m+1)+1) * ((2^(2*m+1))^3+1) * ((2^(2*m+1))^6+1)) := by
  rw [card_model_torus_cell_product,card_fixedTorus,card_parabolic m hm]
  simp only [reduceCtorEq,↓reduceIte]
  ring
end ReeF4.SourceCompletion
