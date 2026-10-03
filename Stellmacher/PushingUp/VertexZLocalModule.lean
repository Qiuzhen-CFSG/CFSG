module

public import Stellmacher.PushingUp.CriticalDistanceBasic

/-!
# The graph vertex subgroup as a canonical local module

For a vertex `a` in the free-amalgam graph, the source subgroup `Z_a` is the
join of `Omega₁(Z(T))` over all Sylow `2`-subgroups of its stabilizer.  This
module identifies it with the ambient image of the normal closure of the
Sylow-center subgroup belonging to one canonical local Sylow subgroup.  The
latter is exactly `SectionTwo.vSubgroup`, so the result lets the subsequent
critical-pair argument reuse the established faithful quotient-conjugation
action without choosing an unrelated module or quotient.

One inclusion puts the chosen Sylow-center subgroup into the defining join
and uses normality of `Z_a`.  For the reverse inclusion, Sylow conjugacy inside
the finite vertex stabilizer expresses every other Sylow-center subgroup as a
conjugate of the chosen one, hence places it in the normal closure.

Source: B. Stellmacher, *Pushing up*, Arch. Math. 46 (1986), the notation
preceding (1.3) and the specialization `V = Z_a` in the proof of (2.2),
journal pp.10--11.
-/

namespace Stellmacher.PushingUp

open AmalgamGraph

universe u

variable {M : Type u} [Group M]

private theorem localSylowOmega_le_vSubgroup [Finite M]
    (S : Subgroup M) (a : Vertex S)
    (Sa Ta : Sylow 2 (stabilizer S a)) :
    omegaOneCenterAmbient (Ta : Subgroup (stabilizer S a)) ≤
      Stellmacher.SectionTwo.vSubgroup Sa := by
  let V : Subgroup (stabilizer S a) :=
    Stellmacher.SectionTwo.vSubgroup Sa
  let _ : V.Normal := by
    dsimp only [V, Stellmacher.SectionTwo.vSubgroup]
    exact Subgroup.normalClosure_normal
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (stabilizer S a) Sa Ta
  have hTa : (Ta : Subgroup (stabilizer S a)) =
      (Sa : Subgroup (stabilizer S a)).map
        (MulAut.conj g).toMonoidHom := by
    rw [← hg, Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def]
    congr 1
  have hOmega :
      omegaOneCenterAmbient (Ta : Subgroup (stabilizer S a)) =
        (omegaOneCenterAmbient (Sa : Subgroup (stabilizer S a))).map
          (MulAut.conj g).toMonoidHom := by
    rw [hTa, omegaOneCenterAmbient_map_injective
      (MulAut.conj g).toMonoidHom (MulAut.conj g).injective]
  intro x hx
  rw [hOmega] at hx
  obtain ⟨y, hy, rfl⟩ := hx
  have hyV : y ∈ V := by
    exact Subgroup.le_normalClosure hy
  exact (inferInstance : V.Normal).conj_mem y hyV g

/-- The graph-defined `Z_a` is the ambient image of the canonical local
normal closure used by the faithful quotient-conjugation action. -/
public theorem vertexZ_eq_local_vSubgroup [Finite M]
    (S : Subgroup M) (a : Vertex S) :
    (Stellmacher.SectionTwo.vSubgroup
      (default : Sylow 2 (stabilizer S a))).map
        (stabilizer S a).subtype = vertexZ S a := by
  classical
  let Sa : Sylow 2 (stabilizer S a) := default
  let V : Subgroup (stabilizer S a) :=
    Stellmacher.SectionTwo.vSubgroup Sa
  let W : Subgroup (stabilizer S a) :=
    (vertexZ S a).subgroupOf (stabilizer S a)
  have hWnormal : W.Normal := by
    simpa [W] using vertexZ_normal_stabilizer S a
  let _ : W.Normal := hWnormal
  have hzmap :
      (Stellmacher.SectionTwo.zSubgroup Sa).map
          (stabilizer S a).subtype =
        sylowOmegaAt S a Sa := by
    unfold Stellmacher.SectionTwo.zSubgroup sylowOmegaAt sylowAt
    exact omegaOneCenterAmbient_map_injective
      (stabilizer S a).subtype (stabilizer S a).subtype_injective _ |>.symm
  have hzW : Stellmacher.SectionTwo.zSubgroup Sa ≤ W := by
    intro z hz
    change ((z : stabilizer S a) : FreeAmalgam S) ∈ vertexZ S a
    have hOmegaLe : sylowOmegaAt S a Sa ≤ vertexZ S a := by
      apply le_sSup
      exact ⟨Sa, rfl⟩
    apply hOmegaLe
    rw [← hzmap]
    exact Subgroup.mem_map_of_mem (stabilizer S a).subtype hz
  have hVW : V ≤ W := by
    dsimp only [V, Stellmacher.SectionTwo.vSubgroup]
    exact Subgroup.normalClosure_le_normal hzW
  apply le_antisymm
  · calc
      V.map (stabilizer S a).subtype ≤
          W.map (stabilizer S a).subtype := Subgroup.map_mono hVW
      _ = vertexZ S a :=
        Subgroup.map_subgroupOf_eq_of_le (vertexZ_le_stabilizer S a)
  · apply sSup_le
    rintro Z ⟨Ta, rfl⟩
    change omegaOneCenterAmbient
        ((Ta : Subgroup (stabilizer S a)).map (stabilizer S a).subtype) ≤
      V.map (stabilizer S a).subtype
    rw [omegaOneCenterAmbient_map_injective
      (stabilizer S a).subtype (stabilizer S a).subtype_injective]
    exact Subgroup.map_mono (localSylowOmega_le_vSubgroup S a Sa Ta)

end Stellmacher.PushingUp
