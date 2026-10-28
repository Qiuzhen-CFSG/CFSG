module

public import CFSG.Quasithin.ChapterG.Section02.AlternatingFive.Structure.Starred.Action
public import CFSG.Quasithin.ChapterG.Section02.AlternatingFive.Structure.Starred.FiniteBorel
public import CFSG.Quasithin.ChapterG.Section02.AlternatingFive.Structure.CentralKernel

/-!
# The starred Borel and generation in G.2.4

Starting only from the original G.2.4 hypothesis, the given Sylow action
identifies V₁ with a derived singular point. The compatible five-point action
of LT/O₂(LT) carries L₁* to its A₄ stabilizer and U* to the corresponding
Sylow four-group. Thus U* = O₂(L₁*), |U*| = 4 and [U*,L₁*] = U*.
The original g moves that point, so the two conjugate four-groups generate
L* and I* = L*. No coordinate marking or Borel premise is added.

The final theorems apply these calculations to the existing generation,
central-kernel, orthogonal-layer and counting consumers. Their owners and
public interfaces remain unchanged.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
G.2.4(1–5), printed pp.334–335, using G.2.3 on pp.333–334.
-/

public section
open Subgroup
namespace CFSG.Quasithin.ChapterG.Section02.AlternatingFive
open Setup Starred
namespace Hypothesis
variable {G : Type*} [Group G] [Finite G] {D : Setup G} {g : G} (d : Hypothesis D g)
include d

theorem star_U_action : (D.star D.U).map d.starAction = FiniteBorel.four d.pointIndex := by
  obtain ⟨hp, hn, hf, hb⟩ := d.starAction_U_control
  exact FiniteBorel.normalized_two_eq_four _ _ hp hn hf hb

/-- G.2.4(1): equality in the literal quotient LT/O₂(LT). -/
theorem star_U_eq_local_core : D.star D.U = (D.star D.L₁).pCoreIn 2 := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  apply map_injective d.starAction_injective
  rw [d.star_U_action, map_pCoreIn_of_ker_isPGroup d.starAction
    (IsPGroup.ker_isPGroup_of_injective d.starAction_injective), d.star_local_action]
  exact FiniteBorel.four_eq_core _

theorem star_U_le_L : D.star D.U ≤ D.star D.L :=
  (map_le_map_iff_of_injective d.starAction_injective).mp (by
    rw [d.star_U_action, d.star_L_action]
    exact (FiniteBorel.four_le_borel _).trans inf_le_left)

/-- The actual starred U has order four. -/
theorem star_U_card : Nat.card (D.star D.U) = 4 := by
  rw [← card_map_of_injective (K := D.star D.U) (f := d.starAction) d.starAction_injective, d.star_U_action]
  exact FiniteBorel.four_card _

/-- G.2.4(1): U* is an embedded Sylow subgroup of the original L*. -/
theorem star_U_sylow : ∃ P : Sylow 2 (D.star D.L),
    (P : Subgroup (D.star D.L)).map (D.star D.L).subtype = D.star D.U := by
  have hc : Nat.card ((D.star D.U).subgroupOf (D.star D.L)) = 4 :=
    (Nat.card_congr (subgroupOfEquivOfLe d.star_U_le_L).toEquiv).trans d.star_U_card
  let P : Sylow 2 (D.star D.L) := Sylow.ofCard ((D.star D.U).subgroupOf (D.star D.L)) (by
    rw [hc, Nat.card_congr d.model.toEquiv, nat_card_alternatingGroup]
    norm_num [Nat.factorial]
    rw [show 60 = 2 ^ 2 * 15 by decide, Nat.factorization_mul (by decide) (by decide),
      Finsupp.add_apply, Nat.prime_two.factorization_pow, Finsupp.single_eq_same,
      Nat.factorization_eq_zero_of_not_dvd (by decide : ¬ 2 ∣ 15)]
    rfl)
  exact ⟨P, map_subgroupOf_eq_of_le d.star_U_le_L⟩

/-- The full Borel commutator used by the central-kernel argument. -/
theorem star_U_commutator : ⁅D.star D.U, D.star D.L₁⁆ = D.star D.U := by
  apply map_injective d.starAction_injective
  rw [map_commutator, d.star_U_action, d.star_local_action]
  exact FiniteBorel.four_commutator _

/-- The literal right conjugate has the expected model image; the original
conjugating element is retained. -/
theorem star_conjugate_U_action_le (l : D.L) :
    ((D.star D.U).map d.starAction).map
      (MulAut.conj (d.fiveAction l).val⁻¹).toMonoidHom ≤
        (D.star (conjugate D.U (l : G))).map d.starAction := by
  rintro _ ⟨_, ⟨u, hu, rfl⟩, rfl⟩
  let z : D.LT := inclusion (show D.L ≤ D.LT from le_sup_left) l
  let q := QuotientGroup.mk' (pCore 2 D.LT)
  have hm : q z⁻¹ * u * q z ∈ D.star (conjugate D.U (l : G)) := by
    obtain ⟨y, hy, he⟩ := hu
    refine ⟨z⁻¹ * y * z, ?_, ?_⟩
    · change (l : G)⁻¹ * (y : G) * (l : G) ∈ conjugate D.U (l : G)
      exact ⟨y, hy, by simp⟩
    · simp only [map_mul, map_inv, he]
      rfl
  refine ⟨q z⁻¹ * u * q z, hm, ?_⟩
  have hz : d.starAction (q z) = (d.fiveAction l).val := d.starAction_on_L (starProjection D l)
  change d.starAction (q z⁻¹ * u * q z) =
    (d.fiveAction l).val⁻¹ * d.starAction u * ((d.fiveAction l).val⁻¹)⁻¹
  rw [map_mul, map_mul, map_inv q, map_inv d.starAction, hz, inv_inv]

/-- Starred generation with the original source conjugator g. -/
theorem star_I_eq_L : D.star (D.I g) = D.star D.L := by
  have hupper : D.star (D.I g) ≤ D.star D.L := by
    have h := binary_star_mono (D := D) (binary_I_le_join d.g_mem)
    rw [binary_star_sup _ _ le_sup_left (d.setup.U_normal_in_T.1.trans le_sup_right),
      sup_eq_left.mpr d.star_U_le_L] at h
    exact h
  apply le_antisymm hupper
  apply (map_le_map_iff_of_injective d.starAction_injective).mp
  rw [d.star_L_action]
  let s := (d.fiveAction ⟨g, d.g_mem⟩).val
  have hn : d.pointIndex ≠ s⁻¹ d.pointIndex := by
    intro h
    have he := congrArg s h
    apply d.g_moves_pointIndex
    change s d.pointIndex = s (s.symm d.pointIndex) at he
    exact he.trans (s.apply_symm_apply _)
  rw [← FiniteBorel.distinct_four_generate d.pointIndex (s⁻¹ d.pointIndex) hn]
  apply sup_le
  · rw [← d.star_U_action]
    exact map_mono (binary_star_mono (show D.U ≤ D.I g from le_sup_left))
  · have hc := d.star_conjugate_U_action_le ⟨g, d.g_mem⟩
    rw [d.star_U_action, FiniteBorel.four_conjugate] at hc
    exact hc.trans (map_mono (binary_star_mono (show conjugate D.U g ≤ D.I g from le_sup_right)))

/-- Application to the existing central-kernel consumer, with every starred
Borel premise discharged from the original source hypothesis. -/
theorem S_eq_WProduct_of_starred : D.S g = WProduct D g :=
  d.S_eq_WProduct_of_borel d.star_I_eq_L d.star_U_sylow d.star_U_commutator

/-- Application to the existing orthogonal-layer consumer, now unconditional. -/
theorem orthogonal_layers_of_starred :
    D.VL ≤ D.S g ⊓ centralizer (D.S g : Set G) ∧
    D.VL ≤ S₂ D g ∧ S₂ D g ≤ D.S g ∧
    (D.VL.subgroupOf (D.I g)).Normal ∧
    ((S₂ D g).subgroupOf (D.I g)).Normal ∧
    ⁅S₂ D g, D.I g⁆ ≤ D.VL ∧ IsElementaryAbelian 2 (S₂ D g) :=
  d.orthogonal_layers_of_star d.star_I_eq_L.ge

/-- G.2.4(2), by the existing two-residual generation lift. -/
theorem I_eq_LU_of_starred : D.I g = D.L ⊔ D.U :=
  d.I_eq_LU_of_star d.star_I_eq_L.ge

/-- The cardinality input for the existing upper-layer counting argument. -/
theorem W_index_four_of_starred : (D.W g).relIndex D.U = 4 :=
  d.W_index_four_of_star d.star_I_eq_L d.star_U_card

end Hypothesis
end CFSG.Quasithin.ChapterG.Section02.AlternatingFive
