module

public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.CartanCore.ResidualSelection
public import Theory.GroupTheory.PCoreImage

/-!
# Restricting the point-normalizer quotient kernel

A subgroup of M∩Y normalizes the literal solvable residual L₁ of L∩G₁.
Its commutators with L₁ lie in O₂(K) by the defining action kernel of Y,
and core restriction puts them in O₂(L₁). Only L₁≤K is used here.

Consequently T∩Y is normalized by L₁ and by T: its commutators with L₁
lie both in O₂(L₁)≤T and in Y, since Y is normal in G₁. Thus T∩Y lies
in R₁=O₂(L₁T). All normality remains relative to the named overgroups.
This supplies the kernel calculation in the point-normalizer step of
Aschbacher--Smith 11.5.6(3), refs/quasithin.pdf, printed pp.780--781.
-/

public section
open Subgroup
open scoped Pointwise commutatorElement
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Geometry
open CFSG.Quasithin.Chapter12.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : ChosenModule T L V} (E : Geometry D)

/-- Normalizing L and the actual point normalizer preserves its solvable residual. -/
theorem pointNormalizer_normalizes_L₁ :
    E.M ⊓ E.G₁ ≤ normalizer (E.L₁ : Set G) := by
  apply le_trans _ (normalizer_le_normalizer_characteristic_image
    (L ⊓ E.G₁) (solvableResidual (L ⊓ E.G₁ : Subgroup G)))
  exact (le_inf inf_le_left (inf_le_right.trans E.G₁.le_normalizer)).trans
    inf_normalizer_le_normalizer_inf

/-- Restrict the literal K/O₂(K) kernel to L₁/O₂(L₁). No normality of L₁ in K is used. -/
theorem pointNormalizer_local_commutator (B : Subgroup G)
    (hBM : B ≤ E.M) (hBY : B ≤ E.Y) :
    B ≤ normalizer (E.L₁ : Set G) ∧ ⁅B, E.L₁⁆ ≤ E.L₁.pCoreIn 2 := by
  have hn := (le_inf hBM (hBY.trans E.Y_le_G₁)).trans E.pointNormalizer_normalizes_L₁
  refine ⟨hn, ?_⟩
  apply le_trans _ (inf_pCoreIn_le_of_le 2 (le_conjugateSpanBy E.L₁ E.G₁))
  refine le_inf (le_normalizer_iff_commutator_le_right.mp hn) ?_
  apply commutator_le.mpr
  intro b hb l hl
  exact coreQuotientCentralizer_commutator (hBY hb).2
    (le_conjugateSpanBy E.L₁ E.G₁ hl)

/-- The source quotient kernel meets T inside the literal local radical.
The commutator bound makes T∩Y normal in L₁T. -/
theorem sylow_inter_Y_le_R₁ (hT : (T : Subgroup G) ≤ E.G₁) :
    (T : Subgroup G) ⊓ E.Y ≤ E.R₁ := by
  have hTN : (T : Subgroup G) ≤ normalizer (E.L₁ : Set G) :=
    (le_inf D.sylow_normalizes_component hT).trans E.pointNormalizer_normalizes_L₁
  have hLY : E.L₁ ≤ normalizer (E.Y : Set G) :=
    ((residualIn_le _).trans inf_le_right).trans E.G₁_normalizes_Y
  have hc := (E.pointNormalizer_local_commutator ((T : Subgroup G) ⊓ E.Y)
    (inf_le_left.trans D.sylow_normalizes_component) inf_le_right).2
  have hcY : ⁅(T : Subgroup G) ⊓ E.Y, E.L₁⁆ ≤ E.Y :=
    (commutator_mono inf_le_right le_rfl).trans
      (le_normalizer_iff_commutator_le_left.mp hLY)
  have hcore : E.L₁.pCoreIn 2 ≤ (T : Subgroup G) := by
    have hle : E.L₁.pCoreIn 2 ≤ E.R₁ :=
      pCoreIn_mono_of_normalizes le_sup_left (sup_le E.L₁.le_normalizer hTN)
    exact hle.trans (by
      simpa only [R₁, Sylow.coe_subtype, map_subgroupOf_eq_of_le le_sup_right] using
        pCoreIn_le_sylow (E.L₁ ⊔ (T : Subgroup G)) (T.subtype le_sup_right))
  apply le_pCoreIn_of_normalizes (T.isPGroup'.to_le inf_le_left)
    (inf_le_left.trans le_sup_right)
  apply sup_le
  · apply le_normalizer_iff_commutator_le_left.mpr
    exact le_inf (hc.trans hcore) hcY
  · exact (le_inf (T : Subgroup G).le_normalizer
      (hT.trans E.G₁_normalizes_Y)).trans inf_normalizer_le_normalizer_inf

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Geometry
