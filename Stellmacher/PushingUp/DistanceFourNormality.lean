module

public import Stellmacher.PushingUp.DistanceFourCoreProduct
public import Theory.GroupTheory.CommutingFactorNormality

/-!
# Normality of the distance-four central products

This module proves the literal normality assertions of Stellmacher,
*Pushing up* (1986), (3.3)(4): `D`, `U Z(G_a)`, and `F U Z(G_a)` are normal
in `G_a`. It also records that `D` centralizes both `F` and `U`, and that
the source image `Ubar` is normal in the central quotient of `G_a`.

Each of the five vertex centers lies in the omega center of its vertex core.
The five defining core containments for `D` therefore imply the two
centralizations. The previously proved equations `Q_a = D U` and
`F Q_a = G_a` transport to subgroups of the finite stabilizer. The generic
commuting-factor normality theorem gives the three normal products, and the
image of `U Z(G_a)` under the central quotient map is exactly `Ubar`.

Source: B. Stellmacher, *Pushing up*, Arch. Math. 46 (1986), journal p.15.
Only vertex stabilizers are finite. Normality of `U` itself is deliberately
not inferred here from normality of its product with the center; that lift
requires a separate argument about central 2-elements.
-/

namespace Stellmacher.PushingUp
open AmalgamGraph
universe u
variable {M : Type u} [Group M]

private theorem coreOmega_centralized_by_core
    {G : Type*} [Group G] (D Z Q : Subgroup G)
    (hD : D ≤ Q) (hZ : Z ≤ omegaOneCenterAmbient Q) :
    D ≤ Subgroup.centralizer Z := by
  intro d hd
  rw [Subgroup.mem_centralizer_iff]
  intro z hz
  exact ((mem_omegaOneCenterAmbient_iff Q z).mp (hZ hz) |>.2.2 d (hD hd)).symm

public structure DistanceFour.Normality [Finite M]
    (S : Subgroup M) (a a' c u v : Vertex S) : Prop where
  D_centralizes_U : DistanceFour.D S a a' c u v ≤ Subgroup.centralizer (DistanceFour.U S a c u)
  D_centralizes_F : DistanceFour.D S a a' c u v ≤ Subgroup.centralizer (DistanceFour.F S a' v)
  D_normal : ((DistanceFour.D S a a' c u v).subgroupOf (stabilizer S a)).Normal
  U_center_normal : ((DistanceFour.U S a c u).subgroupOf (stabilizer S a) ⊔
    Subgroup.center (stabilizer S a)).Normal
  F_U_center_normal : ((DistanceFour.F S a' v).subgroupOf (stabilizer S a) ⊔
    (DistanceFour.U S a c u).subgroupOf (stabilizer S a) ⊔
      Subgroup.center (stabilizer S a)).Normal
  Ubar_normal : (DistanceFour.Ubar S a c u).Normal

set_option maxHeartbeats 600000 in
public theorem distanceFour_normality [Finite M]
    (S : Subgroup M) (T : Sylow 2 M) (hTS : (T : Subgroup M) = S)
    (hP : ∀ K : Subgroup T, K.Characteristic → K ≠ ⊥ →
      ¬ (K.map (T : Subgroup M).subtype).Normal)
    (hSne : S ≠ ⊥)
    (hA : IsSL2Two
      ((M ⧸ pCore 2 M) ⧸ frattini (M ⧸ pCore 2 M)))
    (a a' c u v : Vertex S) (hb4 : criticalDistance S = 4)
    (hconf : DistanceFour.Configuration S a a' c u v) :
    DistanceFour.Normality S a a' c u v := by
  have hb : 0 < criticalDistance S := by omega
  have hinit := distanceFour_initialRelations S T hTS hP hSne hA
    a a' c u v hb4 hconf
  have hproduct := distanceFour_core_product S T hTS hP hSne hA
    a a' c u v hb4 hconf
  obtain ⟨_, _, hAA'⟩ := criticalPair_actionInputs S T hTS hP hSne hA
    a a' hconf.critical hb
  obtain ⟨_, _, hUC⟩ := criticalPair_actionInputs S T hTS hP hSne hA
    u c hconf.first_shift.shifted_critical hb
  obtain ⟨_, _, hVA⟩ := criticalPair_actionInputs S T hTS hP hSne hA
    v a hconf.second_shift.shifted_critical hb
  let D := DistanceFour.D S a a' c u v
  let U := DistanceFour.U S a c u
  let F := DistanceFour.F S a' v
  have hDQv : D ≤ vertexTwoCore S v := fun _ h => h.1.1.1.1
  have hDQu : D ≤ vertexTwoCore S u := fun _ h => h.1.1.1.2
  have hDQa : D ≤ vertexTwoCore S a := fun _ h => h.1.1.2
  have hDQc : D ≤ vertexTwoCore S c := fun _ h => h.1.2
  have hDQa' : D ≤ vertexTwoCore S a' := fun _ h => h.2
  have hDZa := coreOmega_centralized_by_core D (vertexZ S a) _ hDQa
    hAA'.left_Z_le_coreOmega
  have hDZu := coreOmega_centralized_by_core D (vertexZ S u) _ hDQu
    hUC.left_Z_le_coreOmega
  have hDZc := coreOmega_centralized_by_core D (vertexZ S c) _ hDQc
    hUC.right_Z_le_coreOmega
  have hDZv := coreOmega_centralized_by_core D (vertexZ S v) _ hDQv
    hVA.left_Z_le_coreOmega
  have hDZa' := coreOmega_centralized_by_core D (vertexZ S a') _ hDQa'
    hAA'.right_Z_le_coreOmega
  have hDU : D ≤ Subgroup.centralizer U := by
    apply Subgroup.le_centralizer_iff.mp
    exact sup_le (sup_le (Subgroup.le_centralizer_iff.mp hDZa)
      (Subgroup.le_centralizer_iff.mp hDZc)) (Subgroup.le_centralizer_iff.mp hDZu)
  have hDF : D ≤ Subgroup.centralizer F := by
    apply Subgroup.le_centralizer_iff.mp
    exact sup_le (Subgroup.le_centralizer_iff.mp hDZv)
      (Subgroup.le_centralizer_iff.mp hDZa')
  let G := stabilizer S a
  let Q : Subgroup G := pCore 2 G
  let DI := D.subgroupOf G
  let UI := U.subgroupOf G
  let FI := F.subgroupOf G
  have hDGa : D ≤ G := hDQa.trans (Subgroup.map_subtype_le _)
  have hUGa : U ≤ G := hinit.U_le_core.trans (Subgroup.map_subtype_le _)
  have hFGa : F ≤ G := by
    change F ≤ stabilizer S a
    rw [← hinit.F_generates_modulo_core]
    exact le_sup_left
  have hQ : Q = DI ⊔ UI := by
    apply Subgroup.map_injective G.subtype_injective
    rw [Subgroup.map_sup, Subgroup.map_subgroupOf_eq_of_le hDGa,
      Subgroup.map_subgroupOf_eq_of_le hUGa]
    exact hproduct
  have hG : Q ⊔ FI = ⊤ := by
    apply Subgroup.map_injective G.subtype_injective
    rw [Subgroup.map_sup, Subgroup.map_subgroupOf_eq_of_le hFGa,
      ← MonoidHom.range_eq_map, Subgroup.range_subtype]
    change vertexTwoCore S a ⊔ F = G
    rw [sup_comm]
    exact hinit.F_generates_modulo_core
  have hDUI : ⁅DI, UI⁆ = ⊥ := by
    apply (Subgroup.map_eq_bot_iff_of_injective _ G.subtype_injective).mp
    rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hDGa,
      Subgroup.map_subgroupOf_eq_of_le hUGa]
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hDU
  have hDFI : ⁅DI, FI⁆ = ⊥ := by
    apply (Subgroup.map_eq_bot_iff_of_injective _ G.subtype_injective).mp
    rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hDGa,
      Subgroup.map_subgroupOf_eq_of_le hFGa]
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hDF
  obtain ⟨hDn, hUn, hFn⟩ :=
    Subgroup.normal_sup_center_of_commuting_factorization Q DI UI FI hQ hG hDUI hDFI
  have hUbarn : (DistanceFour.Ubar S a c u).Normal := by
    let N := UI ⊔ Subgroup.center G
    let _ : N.Normal := hUn
    let q := QuotientGroup.mk' (Subgroup.center G)
    have hNmap : N.map q = DistanceFour.Ubar S a c u := by
      dsimp [N]
      rw [Subgroup.map_sup]
      have hCmap : (Subgroup.center G).map q = ⊥ := by
        apply (Subgroup.map_eq_bot_iff _).mpr
        rw [QuotientGroup.ker_mk']
      rw [hCmap, sup_bot_eq]
    rw [← hNmap]
    exact Subgroup.Normal.map (inferInstance : N.Normal) q (QuotientGroup.mk'_surjective _)
  exact ⟨hDU, hDF, hDn, hUn, hFn, hUbarn⟩

end Stellmacher.PushingUp
