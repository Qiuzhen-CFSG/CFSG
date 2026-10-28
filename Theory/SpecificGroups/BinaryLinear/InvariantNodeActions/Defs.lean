module

public import Theory.SpecificGroups.BinaryLinear.OuterCyclic.Model
public import Theory.GroupTheory.SolvableOuterQuotient

/-!
# Actual binary flag stabilizers and faithful component actions

A cut is the span of the first i+1 vectors of a basis. Intersecting the
cut stabilizers defines the full and partial flag stabilizers; a minimal
parabolic omits exactly one cut. These use the same coordinates as the
chapter's deleted flags, with no abstract node-action assumption.

Conjugation on a self-centralizing normal subgroup, transported through
a specified model equivalence, is inner exactly for elements of that
subgroup. Normalization of an ambient subgroup becomes preservation of
its actual model image. These reductions prepare the geometric action
calculation in Aschbacher–Smith 13.8.25, printed pp.959–960.
-/

@[expose] public section

open Subgroup
namespace BinaryLinear.InvariantNodeActions
open OuterCyclic

abbrev Basis (m : ℕ) := Module.Basis (Fin (m + 1)) (ZMod 2) (Space (m + 1))

noncomputable def cutSpace {m : ℕ} (b : Basis m) (i : Fin m) :
    Submodule (ZMod 2) (Space (m + 1)) :=
  Submodule.span (ZMod 2) (b '' {j : Fin (m + 1) | j.val ≤ i.val})

noncomputable def cutStabilizer {m : ℕ} (b : Basis m) (cuts : Set (Fin m)) :
    Subgroup (LinearGroup (m + 1)) :=
  ⨅ i ∈ cuts, parabolic (cutSpace b i)

noncomputable def minimalParabolic {m : ℕ} (b : Basis m) (i : Fin m) :
    Subgroup (LinearGroup (m + 1)) := cutStabilizer b {i}ᶜ

theorem mem_cutStabilizer {m : ℕ} (b : Basis m) (cuts : Set (Fin m))
    (g : LinearGroup (m + 1)) :
    g ∈ cutStabilizer b cuts ↔
      ∀ i ∈ cuts, ∀ v, g v ∈ cutSpace b i ↔ v ∈ cutSpace b i := by
  simp only [cutStabilizer, mem_iInf]
  rfl

variable {X H : Type*} [Group X] [Group H] (K : Subgroup X) [K.Normal]

noncomputable def componentAction (e : K ≃* H) : X →* MulAut H :=
  (MulAut.congr e).toMonoidHom.comp MulAut.conjNormal

theorem componentAction_apply (e : K ≃* H) (x : X) (y : H) :
    componentAction K e x y = e (MulAut.conjNormal x (e.symm y)) := rfl

theorem componentAction_mem_inner (e : K ≃* H)
    (hc : centralizer (K : Set X) = ⊥) (x : X) :
    componentAction K e x ∈ MulAut.innerSubgroup H ↔ x ∈ K := by
  change MulAut.congr e (MulAut.conjNormal x) ∈ MulAut.innerSubgroup H ↔ x ∈ K
  rw [← MulAut.map_innerSubgroup_congr e]
  rw [Subgroup.mem_map_equiv]
  simp only [MulEquiv.symm_apply_apply]
  change x ∈ (MulAut.innerSubgroup K).comap MulAut.conjNormal ↔ x ∈ K
  rw [MulAut.conjNormal_comap_innerSubgroup, hc, sup_bot_eq]

theorem conjNormal_map_subgroupOf (P : Subgroup X) (hPK : P ≤ K) (x : X)
    (hx : x ∈ normalizer (P : Set X)) :
    (P.subgroupOf K).map (MulAut.conjNormal x).toMonoidHom = P.subgroupOf K := by
  apply Subgroup.map_injective K.subtype_injective
  rw [Subgroup.map_map]
  have he : K.subtype.comp (MulAut.conjNormal x).toMonoidHom =
      (MulAut.conj x).toMonoidHom.comp K.subtype := rfl
  rw [he, ← Subgroup.map_map, Subgroup.map_subgroupOf_eq_of_le hPK]
  exact mem_normalizer_iff_map_conj_eq.mp hx

theorem componentAction_map_subgroup (e : K ≃* H) (P : Subgroup X)
    (hPK : P ≤ K) (x : X) (hx : x ∈ normalizer (P : Set X)) :
    ((P.subgroupOf K).map e.toMonoidHom).map (componentAction K e x).toMonoidHom =
      (P.subgroupOf K).map e.toMonoidHom := by
  rw [Subgroup.map_map]
  have he : (componentAction K e x).toMonoidHom.comp e.toMonoidHom =
      e.toMonoidHom.comp (MulAut.conjNormal x).toMonoidHom := by
    ext k
    change e (MulAut.conjNormal x (e.symm (e k))) = _
    rw [e.symm_apply_apply]
    rfl
  rw [he, ← Subgroup.map_map, conjNormal_map_subgroupOf K P hPK x hx]

end BinaryLinear.InvariantNodeActions
