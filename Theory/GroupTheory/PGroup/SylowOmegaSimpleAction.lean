module
public import Theory.GroupTheory.SylowFixedNormalClosureSplitting
public import Theory.GroupTheory.PGroup.OmegaCenterIn
public import Theory.GroupTheory.PResidual.NormalPGroupSupplement
public import Mathlib.GroupTheory.Subgroup.Simple

/-!
# Faithful action on a noncentral Sylow-center closure

An elementary normal closure of Ω₁Z(S) lies in Ω₁Z(O₂(G)): the seed
centralizes the normal two-core, and this persists under normal closure.
If G/O₂(G) is simple and the residual moves this module, its centralizer
is exactly O₂(G). The same is true for the full central omega of O₂(G).
The argument keeps every fixed central summand of both modules.

Source: the rank-one preparation in MS93 (5.1), printed p.913, and the
native omega action in Niles, Pushing-up in finite groups, pp.32–33.
The actual original-degree application is RootProductClosureLayer.
-/

public noncomputable section
open Subgroup
namespace Theory.GroupTheory
variable {G : Type*} [Group G]

/-- An elementary Sylow-center closure lies in the central omega of the
whole core, not just in the core. -/
theorem sylow_omega_closure_le_core_omega (S : Sylow 2 G)
    [IsElementaryAbelian 2 (normalClosure (omegaCenterIn (S : Subgroup G) : Set G))] :
    normalClosure (omegaCenterIn (S : Subgroup G) : Set G) ≤ omegaCenterIn (pCore 2 G) := by
  let V := normalClosure (omegaCenterIn (S : Subgroup G) : Set G)
  have hVQ : V ≤ pCore 2 G := le_sSup ⟨inferInstance,IsElementaryAbelian.isPGroup 2 V⟩
  have hVC : V ≤ centralizer (pCore 2 G : Set G) := by
    apply normalClosure_le_normal
    intro z hz
    exact centralizer_le (pCore_isPGroup.le_sylow_of_normal S)
      ((mem_omegaCenterIn_iff _ _).mp hz).2.1
  intro v hv
  exact (mem_omegaCenterIn_iff _ _).mpr
    ⟨hVQ hv,hVC hv,elemPow_eq_one_of_isElementaryAbelian v hv⟩

/-- Noncentral residual action and a simple core quotient make the actual
Sylow-center closure faithful modulo the whole core. -/
theorem sylow_omega_closure_centralizers_of_simple_quotient
    {D : Type*} [Group D] [IsSimpleGroup D]
    (S : Sylow 2 G)
    [IsElementaryAbelian 2 (normalClosure (omegaCenterIn (S : Subgroup G) : Set G))]
    (q : G →* D) (hq : Function.Surjective q) (hk : q.ker = pCore 2 G)
    (hmoving : ⁅normalClosure (omegaCenterIn (S : Subgroup G) : Set G),pResidual 2 G⁆ ≠ ⊥) :
    centralizer (normalClosure (omegaCenterIn (S : Subgroup G) : Set G) : Set G) = pCore 2 G ∧
    centralizer (omegaCenterIn (pCore 2 G) : Set G) = pCore 2 G := by
  let V := normalClosure (omegaCenterIn (S : Subgroup G) : Set G)
  have hVQ := sylow_omega_closure_le_core_omega S
  have hQOmega : pCore 2 G ≤ centralizer (omegaCenterIn (pCore 2 G) : Set G) := by
    intro x hx z hz
    exact (((mem_omegaCenterIn_iff _ _).mp hz).2.1 x hx).symm
  let C := centralizer (V : Set G)
  have hQC : pCore 2 G ≤ C := hQOmega.trans (centralizer_le hVQ)
  let : (C.map q).Normal := Normal.map inferInstance q hq
  have hCQ : C ≤ pCore 2 G := by
    rcases (inferInstance : (C.map q).Normal).eq_bot_or_eq_top with hb | ht
    · rw [←hk]
      exact (map_eq_bot_iff C).mp hb
    · have htop := congrArg (Subgroup.comap q) ht
      rw [comap_map_eq,hk,sup_eq_left.mpr hQC,comap_top] at htop
      apply False.elim
      apply hmoving
      apply commutator_eq_bot_iff_le_centralizer.mpr
      exact le_centralizer_iff.mp (show pResidual 2 G ≤ C by rw [htop]; exact le_top)
  have he : C = pCore 2 G := le_antisymm hCQ hQC
  exact ⟨he,le_antisymm ((centralizer_le hVQ).trans hCQ) hQOmega⟩
end Theory.GroupTheory
