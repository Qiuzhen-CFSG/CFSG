module
public import Theory.GroupTheory.SylowCentralizerComplement
public import Theory.ElementaryAbelian.AbelianNormalClosure
public import Theory.GroupTheory.PCoreOvergroup
public import Stellmacher.OmegaOneCenterMap

/-!
# Splitting the normal closure of a Sylow-fixed binary seed

Let U be the elementary abelian normal closure of a seed fixed by a Sylow
two-subgroup. Averaging in the binary normal subgroup V=[U,G] gives each
seed element a central representative modulo V. Thus the seed lies in
V C_U(G); this subgroup is normal, so it contains U and equality follows.

In characteristic two, every Sylow omega-center seed lies in O₂(G) and
centralizes O₂(G). Its normal closure is therefore abelian, and conjugate
seed generators give exponent two. This proves the splitting clause of
Aschbacher–Smith B.2.13–14, printed p.78, without a complement theorem.
-/

public section
open Subgroup
open scoped IsMulCommutative commutatorElement
namespace Theory.GroupTheory
variable {G : Type*} [Group G] [Finite G]

/-- A Sylow-fixed seed generates its elementary closure from commutators and fixed elements. -/
theorem normalClosure_split_of_sylow_fixed (P : Sylow 2 G) (Z : Subgroup G)
    [IsElementaryAbelian 2 (normalClosure (Z : Set G))]
    (hZP : Z ≤ centralizer (P : Set G)) :
    normalClosure (Z : Set G) =
      ⁅normalClosure (Z : Set G), (⊤ : Subgroup G)⁆ ⊔
        (normalClosure (Z : Set G) ⊓ center G) := by
  let U := normalClosure (Z : Set G)
  let V := ⁅U, (⊤ : Subgroup G)⁆
  have hVU : V ≤ U := commutator_le_left U ⊤
  let : IsElementaryAbelian 2 V := IsElementaryAbelian.of_le hVU
  have hZU : Z ≤ U := subset_normalClosure
  apply le_antisymm ?_ (sup_le hVU inf_le_left)
  apply normalClosure_le_normal
  intro z hz
  change z ∈ V ⊔ (U ⊓ center G)
  obtain ⟨v, hv, hc⟩ := fixed_coset_of_sylow (⊤ : Subgroup G) V
    (by rw [V.normalizer_eq_top])
    (fun v hv => elemPow_eq_one_of_isElementaryAbelian v hv)
    (P.subtype le_top) z
    (fun a _ => by
      change ⁅a,z⁆ ∈ ⁅U,(⊤ : Subgroup G)⁆
      rw [commutator_comm]
      exact commutator_mem_commutator (mem_top a) (hZU hz))
    (fun a ha => hZP hz a ha)
  have hcZ : v*z ∈ center G := by simpa only [coe_top,centralizer_univ] using hc
  have hh : v⁻¹ * (v*z) ∈ V ⊔ (U ⊓ center G) :=
    mul_mem_sup (V.inv_mem hv)
      (show v*z ∈ U ⊓ center G from ⟨U.mul_mem (hVU hv) (hZU hz),hcZ⟩)
  rwa [inv_mul_cancel_left] at hh

/-- In characteristic two, every subgroup of the Sylow omega-center has a split normal closure. -/
theorem omegaCenter_subgroup_normalClosure_split
    (P : Sylow 2 G)
    (hchar : centralizer (pCore 2 G : Set G) ≤ pCore 2 G)
    (Z : Subgroup G) (hZ : Z ≤ Stellmacher.omegaOneCenterAmbient (P : Subgroup G)) :
    normalClosure (Z : Set G) =
      ⁅normalClosure (Z : Set G), (⊤ : Subgroup G)⁆ ⊔
        (normalClosure (Z : Set G) ⊓ center G) := by
  have hc : Z ≤ centralizer (P : Set G) := by
    intro z hz
    exact ((Stellmacher.mem_omegaOneCenterAmbient_iff _ _).mp (hZ hz)).2.2
  have hZQ : Z ≤ pCore 2 G := fun z hz => hchar
    (fun y hy => hc hz y (pCore_isPGroup.le_sylow_of_normal P hy))
  let U := normalClosure (Z : Set G)
  have hUQ : U ≤ pCore 2 G := normalClosure_le_normal hZQ
  have hUC : U ≤ centralizer (pCore 2 G : Set G) := normalClosure_le_normal
    (hc.trans (centralizer_le (pCore_isPGroup.le_sylow_of_normal P)))
  let : IsMulCommutative U := le_centralizer_iff_isMulCommutative.mp
    (hUC.trans (centralizer_le hUQ))
  let : IsElementaryAbelian 2 (Stellmacher.omegaOneCenterAmbient (P : Subgroup G)) :=
    Stellmacher.omegaOneCenterAmbient_elementaryAbelian _
  let : IsElementaryAbelian 2 Z := IsElementaryAbelian.of_le hZ
  let : IsElementaryAbelian 2 U := IsElementaryAbelian.normalClosure_of_isMulCommutative Z
  exact normalClosure_split_of_sylow_fixed P Z hc

end Theory.GroupTheory
