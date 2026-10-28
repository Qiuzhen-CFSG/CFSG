module

public import CFSG.Quasithin.ChapterG.Section02.AlternatingFive.Layers
public import Theory.GroupTheory.PResidual.NormalizerCore
public import Theory.GroupTheory.PResidual.SubnormalCoreAction

/-!
# The commutator lifting at the start of G.2.4(8)

The tilde image equality lifts across the actual kernel V₁ because
coprime-generated residual action gives [V,L₁]=V, hence V₁≤[U,L₁]. The Sylow T
normalizes O²(N_L(V₁)), so U=[U,L₁] lies in L₁. Its normal two-group
structure then places it in the actual O₂(L₁). Clause (2) gives I=L.

The source proof prints V₁=[V,L₁], but only the inclusion is needed.
Residual commutator idempotence supplies it from the original hypotheses,
without a further geometric premise. The later deductions S₂=V_L, S=V_L
and quaternion central-product recognition are not assumed or claimed here.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
G.2.4(8), printed pp.334–335; used in 13.5.14(1), printed p.919.
-/

@[expose] public section
open Subgroup
namespace CFSG.Quasithin.ChapterG.Section02.AlternatingFive
open Setup
variable {G : Type*} [Group G] [Finite G] {D : Setup G}

omit [Finite G] in
private theorem L₁_le_L : D.L₁ ≤ D.L := (map_subtype_le _).trans inf_le_left
omit [Finite G] in
private theorem L₁_le_G₁ : D.L₁ ≤ D.G₁ := (map_subtype_le _).trans inf_le_right

/-- The specified Sylow subgroup normalizes the actual embedded two-residual. -/
theorem T_normalizes_L₁ (h : D.BaseHypothesis) : D.T ≤ normalizer (D.L₁ : Set G) := by
  apply le_trans ?_ (normalizer_le_normalizer_characteristic_image
    (D.L ⊓ D.G₁) (pResidual 2 (D.L ⊓ D.G₁ : Subgroup G)))
  intro t ht
  rw [mem_normalizer_iff_map_conj_eq]
  have hL : D.L.map (MulAut.conj t).toMonoidHom = D.L :=
    mem_normalizer_iff_map_conj_eq.mp (h.T_normalizes_L ht)
  have hG : D.G₁.map (MulAut.conj t).toMonoidHom = D.G₁ :=
    mem_normalizer_iff_map_conj_eq.mp (D.G₁.le_normalizer (h.T_normalizes_point ht))
  change (D.L ⊓ D.G₁).map (MulAut.conj t).toMonoidHom = _
  rw [map_inf _ _ _ (MulAut.conj t).injective, hL, hG]

/-- The first lifting step of G.2.4(8). Only the orthogonal Borel
inclusion V₁≤[V,L₁] is needed; the tilde equality
uses the literal quotient N_G(V₁)/V₁. -/
theorem U_eq_commutator_of_tilde (h : D.Hypothesis)
    (hpoint : D.V₁ ≤ ⁅D.V, D.L₁⁆)
    (hfull : ⁅D.tilde D.U, D.tilde D.L₁⁆ = D.tilde D.U) :
    D.U = ⁅D.U, D.L₁⁆ := by
  have hUG : D.U ≤ D.G₁ := h.U_le_H.trans h.H_le
  let q := QuotientGroup.mk' (D.V₁.subgroupOf D.G₁)
  let A := D.U.subgroupOf D.G₁
  let B := D.L₁.subgroupOf D.G₁
  have hc : (⁅A, B⁆).map D.G₁.subtype = ⁅D.U, D.L₁⁆ := by
    rw [map_commutator, map_subgroupOf_eq_of_le hUG, map_subgroupOf_eq_of_le L₁_le_G₁]
  have hkA : q.ker ≤ A := by
    rw [QuotientGroup.ker_mk']
    exact comap_mono (h.point_le.trans (le_conjugateSpanBy _ _))
  have hkC : q.ker ≤ ⁅A, B⁆ := by
    apply (map_le_map_iff_of_injective D.G₁.subtype_injective).mp
    have hpointG : D.V₁ ≤ D.G₁ := D.V₁.le_normalizer
    rw [QuotientGroup.ker_mk', map_subgroupOf_eq_of_le hpointG, hc]
    exact hpoint.trans (commutator_mono (le_conjugateSpanBy _ _) le_rfl)
  have he : A = ⁅A, B⁆ := map_injective_of_ker_le q hkA hkC (by
    rw [map_commutator]
    exact hfull.symm)
  have hm := congrArg (map D.G₁.subtype) he
  rw [map_subgroupOf_eq_of_le hUG, hc] at hm
  exact hm

/-- Full tilde commutators place U in the actual O₂(L₁), with no assumption
that U is already contained in L or in its point stabilizer. -/
theorem U_le_local_core_of_tilde (h : D.Hypothesis)
    (hpoint : D.V₁ ≤ ⁅D.V, D.L₁⁆)
    (hfull : ⁅D.tilde D.U, D.tilde D.L₁⁆ = D.tilde D.U) :
    D.U ≤ D.L₁.pCoreIn 2 := by
  have hUL : D.U ≤ D.L₁ := by
    rw [U_eq_commutator_of_tilde h hpoint hfull]
    exact le_normalizer_iff_commutator_le_right.mp
      (h.U_normal_in_T.1.trans (T_normalizes_L₁ h.toBaseHypothesis))
  exact le_pCoreIn_of_normalizes h.U_isPGroup hUL
    ((le_sup_left.trans h.local_le).trans (le_normalizer_conjugateSpanBy D.V D.H))

/-- Once G.2.4(2) is known, the tilde commutator assumption gives I=L. -/
theorem I_eq_L_of_tilde (h : D.Hypothesis) (g : G)
    (hpoint : D.V₁ ≤ ⁅D.V, D.L₁⁆)
    (hfull : ⁅D.tilde D.U, D.tilde D.L₁⁆ = D.tilde D.U)
    (hgen : D.I g = D.L ⊔ D.U) : D.I g = D.L := by
  rw [hgen, sup_eq_left]
  exact (U_le_local_core_of_tilde h hpoint hfull).trans
    ((pCoreIn_le 2 D.L₁).trans L₁_le_L)

namespace Hypothesis
variable {g : G}

/-- Since L₁ is the actual two-residual, its action on a two-group is
idempotent on commutators. This discharges V₁≤[V,L₁] from the source data. -/
theorem seed_eq_commutator (d : Hypothesis D g) : ⁅D.V, D.L₁⁆ = D.V := by
  let := d.VL_elementary
  have hp : IsPPerfect 2 D.L₁ := isPPerfect_embedded_pResidual 2 (D.L ⊓ D.G₁)
  have hn : D.L₁ ≤ normalizer (D.VL : Set G) :=
    ((map_subtype_le _).trans inf_le_left).trans (L_normalizes_VL D)
  rw [d.seed_eq]
  exact commutator_isPPerfect_idempotent D.L₁ D.VL hp
    (IsElementaryAbelian.isPGroup 2 D.VL) hn

/-- The opening of G.2.4(8) under its original source assumptions, with
the kernel-containment premise of the lifting lemma fully discharged. -/
theorem terminal_reduction (d : Hypothesis D g)
    (hfull : ⁅D.tilde D.U, D.tilde D.L₁⁆ = D.tilde D.U) :
    D.U = ⁅D.U, D.L₁⁆ ∧ D.U ≤ D.L₁.pCoreIn 2 := by
  have hpoint : D.V₁ ≤ ⁅D.V, D.L₁⁆ := d.setup.point_le.trans d.seed_eq_commutator.ge
  exact ⟨U_eq_commutator_of_tilde d.setup hpoint hfull,
    U_le_local_core_of_tilde d.setup hpoint hfull⟩

/-- The source tilde assumption and clause (2) give I=L, before the later
core collapse and block recognition. -/
theorem terminal_group_eq (d : Hypothesis D g)
    (hfull : ⁅D.tilde D.U, D.tilde D.L₁⁆ = D.tilde D.U)
    (hgen : D.I g = D.L ⊔ D.U) : D.I g = D.L :=
  I_eq_L_of_tilde d.setup g (d.setup.point_le.trans d.seed_eq_commutator.ge) hfull hgen

end Hypothesis

end CFSG.Quasithin.ChapterG.Section02.AlternatingFive
