module

public import Stellmacher.OmegaOneCenterMap
public import Mathlib.GroupTheory.Sylow
public import Mathlib.GroupTheory.Commutator.Basic

/-!
# Generating an omega-center normal closure by two Sylows

In a finite group, the normal closure of the omega subgroup of the center of
one Sylow 2-subgroup is the join of these omega centers over all Sylows. If
Sylows `P` and `Q` generate the group and the commutator of this normal closure
with `P` lies in the omega center of `P`, then just the omega centers of `P`
and `Q` generate the normal closure.

Sylow conjugacy first identifies every omega center with a conjugate of the
chosen one. It also transports the commutator bound from `P` to `Q`, since
the ambient normal closure is invariant under conjugation. Their omega-center
join is contained in this normal closure, so the commutator bounds show that
both `P` and `Q` normalize the join. They generate the group; hence the join
is normal and contains the original normal-closure generators.

These are the elementary generation and transport steps used in Stellmacher,
*Pushing up*, Arch. Math. 46 (1986), (3.3). The join over all Sylows matches
the vertex omega-center construction in the amalgam graph.
-/

open scoped commutatorElement Pointwise
namespace Stellmacher.PushingUp

private theorem omega_sylow_conj {G : Type*} [Group G] (P : Sylow 2 G) (g : G) :
    (omegaOneCenterAmbient (P : Subgroup G)).map (MulAut.conj g).toMonoidHom =
      omegaOneCenterAmbient ((g • P : Sylow 2 G) : Subgroup G) := by
  rw [← omegaOneCenterAmbient_map_injective _ (MulAut.conj g).injective,
    Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def]
  rfl

/-- The normal closure of one Sylow omega center is the join of all Sylow
omega centers. -/
public theorem omegaNormalClosure_eq_sSup_sylows
    {G : Type*} [Group G] [Finite G] (P : Sylow 2 G) :
    Subgroup.normalClosure (omegaOneCenterAmbient (P : Subgroup G) : Set G) =
      sSup {Z : Subgroup G | ∃ Q : Sylow 2 G,
        Z = omegaOneCenterAmbient (Q : Subgroup G)} := by
  let V := Subgroup.normalClosure (omegaOneCenterAmbient (P : Subgroup G) : Set G)
  apply le_antisymm
  · rw [Subgroup.normalClosure]
    apply (Subgroup.closure_le _).mpr
    intro x hx
    obtain ⟨a, ha, hax⟩ := Group.mem_conjugatesOfSet_iff.mp hx
    obtain ⟨g, rfl⟩ := isConj_iff.mp hax
    apply (show omegaOneCenterAmbient ((g • P : Sylow 2 G) : Subgroup G) ≤
      sSup {Z : Subgroup G | ∃ Q : Sylow 2 G,
        Z = omegaOneCenterAmbient (Q : Subgroup G)} from le_sSup ⟨g • P, rfl⟩)
    rw [← omega_sylow_conj]
    exact ⟨a, ha, by simp [MulAut.conj_apply]⟩
  · apply sSup_le
    rintro Z ⟨Q, rfl⟩
    obtain ⟨g, rfl⟩ := MulAction.exists_smul_eq G P Q
    rw [← omega_sylow_conj]
    have hle : omegaOneCenterAmbient (P : Subgroup G) ≤ V :=
      Subgroup.subset_normalClosure
    have hmap := Subgroup.map_mono (f := (MulAut.conj g).toMonoidHom) hle
    exact hmap.trans_eq (Subgroup.Normal.map_conj_eq V g)

/-- A commutator bound and two generating Sylows reduce the omega-center
normal closure to the join of their two omega centers. -/
public theorem omegaNormalClosure_eq_sup_of_generating_sylows
    {G : Type*} [Group G] [Finite G] (P Q : Sylow 2 G)
    (hgen : (P : Subgroup G) ⊔ (Q : Subgroup G) = ⊤)
    (hcomm : ⁅Subgroup.normalClosure (omegaOneCenterAmbient (P : Subgroup G) : Set G),
      (P : Subgroup G)⁆ ≤ omegaOneCenterAmbient (P : Subgroup G)) :
    Subgroup.normalClosure (omegaOneCenterAmbient (P : Subgroup G) : Set G) =
      omegaOneCenterAmbient (P : Subgroup G) ⊔
        omegaOneCenterAmbient (Q : Subgroup G) := by
  let V := Subgroup.normalClosure (omegaOneCenterAmbient (P : Subgroup G) : Set G)
  let ZP := omegaOneCenterAmbient (P : Subgroup G)
  let ZQ := omegaOneCenterAmbient (Q : Subgroup G)
  let U := ZP ⊔ ZQ
  have hPV : ZP ≤ V := Subgroup.subset_normalClosure
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G P Q
  have hPmap : (P : Subgroup G).map (MulAut.conj g).toMonoidHom = Q := by
    rw [← hg, Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def]
    rfl
  have hZmap : ZP.map (MulAut.conj g).toMonoidHom = ZQ := by
    change (omegaOneCenterAmbient (P : Subgroup G)).map _ = _
    rw [omega_sylow_conj, hg]
  have hVmap : V.map (MulAut.conj g).toMonoidHom = V :=
    Subgroup.Normal.map_conj_eq V g
  have hQV : ZQ ≤ V := by
    rw [← hZmap, ← hVmap]
    exact Subgroup.map_mono hPV
  have hcommQ : ⁅V, (Q : Subgroup G)⁆ ≤ ZQ := by
    have hmap := Subgroup.map_mono (f := (MulAut.conj g).toMonoidHom) hcomm
    rw [Subgroup.map_commutator] at hmap
    change ⁅V.map (MulAut.conj g).toMonoidHom,
      (P : Subgroup G).map (MulAut.conj g).toMonoidHom⁆ ≤
        ZP.map (MulAut.conj g).toMonoidHom at hmap
    rwa [hVmap, hPmap, hZmap] at hmap
  have hUV : U ≤ V := sup_le hPV hQV
  have hPN : (P : Subgroup G) ≤ Subgroup.normalizer (U : Set G) := by
    apply Subgroup.le_normalizer_iff_commutator_le_left.mpr
    exact (Subgroup.commutator_mono hUV le_rfl).trans
      (hcomm.trans (show ZP ≤ U from le_sup_left))
  have hQN : (Q : Subgroup G) ≤ Subgroup.normalizer (U : Set G) := by
    apply Subgroup.le_normalizer_iff_commutator_le_left.mpr
    exact (Subgroup.commutator_mono hUV le_rfl).trans
      (hcommQ.trans (show ZQ ≤ U from le_sup_right))
  have hN : Subgroup.normalizer (U : Set G) = ⊤ := by
    apply top_unique
    rw [← hgen]
    exact sup_le hPN hQN
  let _ : U.Normal := Subgroup.normalizer_eq_top_iff.mp hN
  exact le_antisymm (Subgroup.normalClosure_le_normal
    (show ZP ≤ U from le_sup_left)) hUV

end Stellmacher.PushingUp
