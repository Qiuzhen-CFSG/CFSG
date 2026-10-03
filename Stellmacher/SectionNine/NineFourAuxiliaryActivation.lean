module
public import Stellmacher.SectionNine.NineFourCentralNormalization
public import Stellmacher.ResidualCoreCommutator
public import Theory.ThreeSubgroups

/-!
# Residual action on the noncentral auxiliary module in (9.4)

For the literal source group F, its residual R and residual two-core Q,
a selected auxiliary subgroup V_y larger than Z_next has nontrivial
R-action even modulo Z_next. The statement retains the actual ambient
context and requires only the normalized remote adjacency and original
subgroup commutator containment.

The local quotient theorem makes R/O₂(R) odd. Since R is two-residual
perfect, the core commutator identity gives Q=[Q,R]. If R centralized
V_y modulo Z_next, the other triple commutator would also lie in Z_next:
[<y>V_next,R] lies in V_next and [V_next,Q] lies in Z_next. The relative
three-subgroups lemma would then force [<y>V_next,Q] into Z_next,
contradicting V_y being larger.

This proves the first sentence of the noncentral case of Stellmacher
(9.4), printed p.51/PDF p.41 of `refs/files/stellmacher-n-group.pdf`,
before the selected-factor argument giving source relation (5).
-/

namespace Stellmacher.SectionNine
open Later SectionsFiveToSeven CosetGraphContext SevenSix
open scoped commutatorElement
universe u

public theorem nine_four_auxiliary_residual_active
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A0 B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A0 B)
    (hb : 1 < ctx.criticalPath.length)
    (remote : ctx.Γ.Vertex)
    (hremote : remote ∈ Neighborhood ctx.Γ ctx.criticalPath.a)
    (actor : G) (hactor : actor ∈ GAt ctx.Γ ctx.criticalPath.firstStep)
    (A : Subgroup G) (hA : A ≤ VAt ctx.Γ remote)
    (hcomm : ⁅A, Subgroup.zpowers actor⁆ ≤ VAt ctx.Γ ctx.criticalPath.firstStep)
    (y : G) (hy : y ∈ A)
    (hnoncentral :
      let F := (QAt ctx.Γ ctx.criticalPath.a ⊓ QAt ctx.Γ remote) ⊔
        Subgroup.zpowers actor
      let Q := twoCoreIn (twoResidualIn F)
      ⁅Subgroup.zpowers y ⊔ VAt ctx.Γ ctx.criticalPath.firstStep, Q⁆ ⊔
        ZAt ctx.Γ ctx.criticalPath.firstStep ≠ ZAt ctx.Γ ctx.criticalPath.firstStep) :
    let F := (QAt ctx.Γ ctx.criticalPath.a ⊓ QAt ctx.Γ remote) ⊔
      Subgroup.zpowers actor
    let Q := twoCoreIn (twoResidualIn F)
    let V_y := ⁅Subgroup.zpowers y ⊔ VAt ctx.Γ ctx.criticalPath.firstStep, Q⁆ ⊔
      ZAt ctx.Γ ctx.criticalPath.firstStep
    ¬ ⁅V_y, twoResidualIn F⁆ ≤ ZAt ctx.Γ ctx.criticalPath.firstStep := by
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let P := GAt Γ cp.firstStep
  let V := VAt Γ cp.firstStep
  let Z := ZAt Γ cp.firstStep
  let F := (QAt Γ cp.a ⊓ QAt Γ remote) ⊔ Subgroup.zpowers actor
  let R := twoResidualIn F
  let Q := twoCoreIn R
  let U := Subgroup.zpowers y ⊔ V
  let W := ⁅U,Q⁆ ⊔ Z
  have hgeom := nine_four_auxiliary_core_geometry ctx hb remote actor hactor
  have hFP : F ≤ P := hgeom.1
  have hRF : R ≤ F := twoResidualIn_le F
  have hQR : Q ≤ R := twoCoreIn_le R
  have hPQ : P ≤ Subgroup.normalizer Z := stabilizer_le_normalizer_z Γ cp.firstStep
  have hodd : Odd (Nat.card (R ⧸ pCore 2 R)) :=
    local_residual_core_quotient_odd ctx.sectionSeven Γ cp.firstStep cp.a
      ((mem_neighborhood_iff_adjacent Γ).mpr (Γ.adjacent_symm cp.firstStep_adj)) F hFP
  have hcoreComm : Q = ⁅Q,R⁆ := by
    have hh := congrArg (Subgroup.map R.subtype)
      (twoCore_eq_commutator_of_residual_perfect
        (twoResidualAmbient_has_top_twoResidual F) hodd)
    rw [Subgroup.map_commutator, ← MonoidHom.range_eq_map, Subgroup.range_subtype] at hh
    exact hh
  have hyD : y ∈ VAt Γ remote := hA hy
  have hCy : Subgroup.zpowers y ≤ VAt Γ remote := Subgroup.zpowers_le.mpr hyD
  have hCyA : Subgroup.zpowers y ≤ A := Subgroup.zpowers_le.mpr hy
  have hCyComm : ⁅Subgroup.zpowers y, Subgroup.zpowers actor⁆ ≤ V :=
    (Subgroup.commutator_mono hCyA le_rfl).trans hcomm
  have hnorm := nine_four_auxiliary_normalization ctx hb remote hremote actor hactor
    (Subgroup.zpowers y) hCy hCyComm
  have hUR : ⁅U,R⁆ ≤ V := (Subgroup.commutator_mono le_rfl hRF).trans hnorm.2
  have hVQ : ⁅V,Q⁆ ≤ Z :=
    (Subgroup.commutator_mono le_rfl hgeom.2.1).trans_eq
      (nine_next_center_commutator_and_kernel ctx hb cp.firstStep ⟨1, Γ.act_one _⟩).2.1
  have hb2 : 2 < cp.length := by
    have hodd := (lemma_seven_five ctx.sectionSeven Γ cp ctx.commutator_eq).odd_distance
    change Odd cp.length at hodd
    obtain ⟨k,hk⟩ := hodd
    change 1 < cp.length at hb
    omega
  have hDQa : VAt Γ remote ≤ QAt Γ cp.a :=
    (nine_seven_neighbor_module_le_neighborhood Γ
      ((mem_neighborhood_iff_adjacent Γ).mp hremote)).trans
        (nine_seven_neighborhood_le_own_core ctx.toLocalContext hb2 cp.a)
  have hQaP : QAt Γ cp.a ≤ P :=
    ((local_cores_le_edge_sylow ctx.sectionSeven Γ cp).1.trans
      cp.S_le_edge_stabilizers).trans inf_le_right
  have hVP : V ≤ P := (nine_seven_module_le_own_core ctx.toLocalContext hb cp.firstStep).trans
    (by change q Γ cp.firstStep ≤ stabilizer Γ cp.firstStep
        rw [q, Γ.twoCoreAt_def]
        exact twoCoreIn_le _)
  have hUP : U ≤ P := sup_le (hCy.trans (hDQa.trans hQaP)) hVP
  change ¬ ⁅W,R⁆ ≤ Z
  intro hWR
  have htriple : ⁅⁅Q,R⁆,U⁆ ≤ Z := by
    apply Subgroup.commutator_commutator_le_of_rotate_of_le_normalizer
      (hQR.trans (hRF.trans (hFP.trans hPQ))) (hRF.trans (hFP.trans hPQ)) (hUP.trans hPQ)
    · have hRU : ⁅R,U⁆ ≤ V := by simpa only [Subgroup.commutator_comm] using hUR
      exact (Subgroup.commutator_mono hRU le_rfl).trans hVQ
    · exact (Subgroup.commutator_mono (show ⁅U,Q⁆ ≤ W from le_sup_left) le_rfl).trans hWR
  have hUQ : ⁅U,Q⁆ ≤ Z := by
    rw [← hcoreComm, Subgroup.commutator_comm] at htriple
    exact htriple
  exact hnoncentral (sup_eq_right.mpr hUQ)

end Stellmacher.SectionNine
