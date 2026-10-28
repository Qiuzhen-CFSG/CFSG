module

public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Linear.Core
public import Theory.GroupTheory.PResidual.SylowSupplement

/-!
# The Sylow intersection in the odd-degree ending

The quotient kernel Y preserves every subgroup of K containing O₂(K).
In particular it preserves T∩K. Hence a splitting of T over T∩L,
together with U≤L and T∩L≤K, gives T=(T∩K)C_T(U). If the selected
outside residual also normalizes C_T(U), it normalizes T, a contradiction.

This uses T∩K in the printed final normalizer argument, not the assertion
T∩L=U=O₂(L₁). In a standard natural SL₃(q) block the latter two-subgroup
has order q⁵ whereas T∩L has order q⁶. The correct normalizer implication
below does not require their identification. The remaining source work
must establish the splitting and C_T(U)-normalization hypotheses.

Source: Aschbacher--Smith, 11.5.7, printed p.782, equations (*) and (**).
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Linear
open Subgroup
open CFSG.Quasithin.Chapter12.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {D : ChosenModule T L V} (E : Geometry D)

/-- The actual O²(H), rather than its two-core. -/
def outsideResidual : Subgroup G := (pResidual 2 E.H).map E.H.subtype

/-- The actual quotient kernel preserves every full preimage in K. -/
theorem Y_normalizes_intersection (A : Subgroup G) (hcore : E.K.pCoreIn 2 ≤ A) :
    E.Y ≤ normalizer ((A ⊓ E.K : Subgroup G) : Set G) :=
  le_normalizer_iff_commutator_le_right.mpr
    (((commutator_mono le_rfl inf_le_right).trans (commutator_Y_K_le E)).trans
      (le_inf hcore (pCoreIn_le 2 E.K)))

/-- Apply the quotient-kernel calculation to the original Sylow subgroup. -/
theorem Y_normalizes_sylow_intersection (hTG : (T : Subgroup G) ≤ E.G₁) :
    E.Y ≤ normalizer (((T : Subgroup G) ⊓ E.K : Subgroup G) : Set G) := by
  apply Y_normalizes_intersection E
  apply (K_core_le_G₁_core E).trans
  simpa only [Sylow.coe_subtype, map_subgroupOf_eq_of_le hTG] using
    pCoreIn_le_sylow E.G₁ (T.subtype hTG)

/-- The valid replacement for the Sylow product in the odd-degree argument. -/
theorem sylow_eq_intersection_join_centralizer
    (hUL : E.W ≤ L) (hTK : (T : Subgroup G) ⊓ L ≤ E.K)
    (hsplit : (T : Subgroup G) = ((T : Subgroup G) ⊓ L) ⊔
      ((T : Subgroup G) ⊓ centralizer (L : Set G))) :
    (T : Subgroup G) = ((T : Subgroup G) ⊓ E.K) ⊔
      ((T : Subgroup G) ⊓ centralizer (E.W : Set G)) := by
  apply le_antisymm
  · calc
      (T : Subgroup G) = _ := hsplit
      _ ≤ _ := sup_le_sup (le_inf inf_le_left hTK)
        (inf_le_inf_left _ (centralizer_le hUL))
  · exact sup_le inf_le_left inf_le_left

/-- The source outside-H contradiction after the remaining centralizer
normalization input. No equality T∩L=U or terminal contradiction is assumed. -/
theorem odd_normalizer_contradiction
    (hTH : (T : Subgroup G) ≤ E.H) (hTG : (T : Subgroup G) ≤ E.G₁)
    (hUL : E.W ≤ L) (hTK : (T : Subgroup G) ⊓ L ≤ E.K)
    (hsplit : (T : Subgroup G) = ((T : Subgroup G) ⊓ L) ⊔
      ((T : Subgroup G) ⊓ centralizer (L : Set G)))
    (hKY : outsideResidual E ≤ E.Y)
    (hKC : outsideResidual E ≤
      normalizer (((T : Subgroup G) ⊓ centralizer (E.W : Set G) : Subgroup G) : Set G))
    (hNT : normalizer ((T : Subgroup G) : Set G) ≤ E.M)
    (hout : ¬ E.H ≤ E.M) : False := by
  have hT := sylow_eq_intersection_join_centralizer E hUL hTK hsplit
  have hKT : outsideResidual E ≤ normalizer ((T : Subgroup G) : Set G) := by
    rw [hT]
    exact (le_inf (hKY.trans (Y_normalizes_sylow_intersection E hTG)) hKC).trans
      (normalizer_inf_normalizer_le_normalizer_sup _ _)
  have hH : outsideResidual E ⊔ (T : Subgroup G) = E.H := by
    have he := congrArg (Subgroup.map E.H.subtype)
      (pResidual_sup_sylow_eq_top (T.subtype hTH))
    simpa only [outsideResidual, Subgroup.map_sup, Sylow.coe_subtype, map_subgroupOf_eq_of_le hTH,
      ← MonoidHom.range_eq_map, range_subtype] using he
  apply hout
  rw [← hH]
  exact (sup_le hKT (T : Subgroup G).le_normalizer).trans hNT

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Linear
