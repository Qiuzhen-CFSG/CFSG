module

public import Theory.GroupTheory.PResidual.FrattiniGeneration
public import Theory.GroupTheory.Commutator.CentralizingComplement

/-!
# Residual displacement through a centralizing supplement

If X supplements the centralizer of a normal subgroup V, then Oᵖ(X)
and Oᵖ(G) have the same commutator with V. Passing to G/C_G(V) gives
the same residual image; the remaining kernel centralizes V.

Source application: the Thompson Frattini argument in Aschbacher--Smith
15.1.21, printed p.1098. No solvability or coprimality is required.
-/

public section
namespace Subgroup
variable {G : Type*} [Group G] [Finite G]

/-- A centralizing supplement preserves the actual residual displacement. -/
theorem commutator_embedded_pResidual_eq_of_centralizing_sup
    (p : ℕ) (V X : Subgroup G) [V.Normal]
    (hgen : X ⊔ centralizer (V : Set G) = ⊤) :
    ⁅V, (pResidual p X).map X.subtype⁆ = ⁅V, pResidual p G⁆ := by
  let C := centralizer (V : Set G)
  let q := QuotientGroup.mk' C
  have hm : X.map q = ⊤ := by
    have hh := congrArg (map q) hgen
    change (X ⊔ C).map q = (⊤ : Subgroup G).map q at hh
    simpa only [q, map_sup, QuotientGroup.map_mk'_self, sup_bot_eq,
      map_top_of_surjective _ (QuotientGroup.mk'_surjective C)] using hh
  have hr := pResidual_eq_embedded_sup_kernel_of_map_le p X q
    (show (pResidual p G).map q ≤ X.map q by rw [hm]; exact le_top)
  rw [QuotientGroup.ker_mk'] at hr
  exact commutator_eq_of_centralizing_sup
    ((sup_comm _ _).trans hr.symm) inf_le_right le_normalizer_of_normal

end Subgroup
