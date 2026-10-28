module

public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.ComponentBranch.AlternatingLocals.Mixed
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.ComponentBranch.Rank

/-!
# Contradiction from the selected component

Starting with the actual A₆ component and S₆ star subgroup, the local results
construct both A₄ factors and both E₄ × S₄ local groups. The realized
permutation action identifies the second factor with the specified conjugate;
the source commutation gives X ≃ A₄ × A₄. Its two-core lies in T_I.
The central fixed involution then gives an elementary subgroup of order 32
in T_I, whereas its embedding in E₄ × S₄ bounds that order by 16.

The model selection is still a premise here. This theorem closes the last
part of the component branch and is not the source theorem 15.4.18.

Source: Aschbacher–Smith, combined 1 March 2004 manuscript, proof of 15.4.18,
printed p.1163.
-/

@[expose] public section
open Subgroup
namespace CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.ComponentBranch
open MixedLocal
variable {G : Type*} [Group G] [Finite G]

/-- The actual selected component and star extension contradict the raw mixed
factor geometry. The order-two centralizer and local identifications are derived. -/
theorem false_of_selected_component
    {K : GroupClass} (T : Sylow 2 G) {Y X M₁ M₂ : Subgroup G}
    {F : Bool → Subgroup G} (d : RealizedFactors T Y X M₁ M₂ F)
    (c : Configuration K T Y X M₂ F)
    (hcomm : F false ≤ centralizer (F true : Set G))
    (hY : IsPPerfect 2 Y) (hF : IsPPerfect 2 (F false))
    (L : Subgroup (generated T Y F))
    (hL : Theory.GroupTheory.IsComponent (generated T Y F) L)
    (eL : L ≃* alternatingGroup (Fin 6))
    (hZ : Nat.card (Stellmacher.omegaOneCenterAmbient (T : Subgroup G)) = 4)
    (hfaithful : AlternatingLocals.RawQuotient.mixedZ T Y F ⊓
      centralizer (L : Set (generated T Y F)) = ⊥)
    (eSelected : AlternatingLocals.RawQuotient.selectedJoin L
      (AlternatingLocals.RawQuotient.mixedZ T Y F) ≃* Equiv.Perm (Fin 6)) : False := by
  obtain ⟨_, ⟨eF⟩⟩ := AlternatingLocals.Mixed.factors_alternating_four
    T d c L hL eL hZ hfaithful eSelected hY hF
  obtain ⟨⟨eG⟩, _⟩ := AlternatingLocals.Mixed.local_groups
    T d c L hL eL hZ hfaithful eSelected hY hF
  have hswap : (F false).map (MulAut.conj d.swapper).toMonoidHom = F true := by
    have he := d.pairAction.conjugation ⟨d.swapper, d.sylow_le₂ d.swapper_mem⟩ false
    cases hp : d.pairAction.permutation ⟨d.swapper, d.sylow_le₂ d.swapper_mem⟩ false with
    | false =>
      exact (d.swapper_moves (mem_normalizer_iff_map_conj_eq.mpr
        (he.trans (congrArg F hp)))).elim
    | true => exact he.trans (congrArg F hp)
  obtain ⟨eX⟩ := a4_product_of_commuting_conjugates (X := X) d.swapper eF
    (by rw [hswap]; exact d.product.symm) (by rwa [hswap])
  have hXF : X ≤ normalizer (F false : Set G) := by
    rw [← d.product]
    exact sup_le (F false).le_normalizer
      ((le_centralizer_iff.mp hcomm).trans (Subgroup.centralizer_le_normalizer _))
  have hcore := twoCore_le_mixed_sylow T
    (d.sylow_le₂.trans d.normalizer₂.le) hXF (rfl : stabilizer T F = _)
  let Z := Stellmacher.omegaOneCenterAmbient (T : Subgroup G)
  let C := Z ⊓ centralizer (X : Set G)
  let : IsElementaryAbelian 2 Z := Stellmacher.omegaOneCenterAmbient_elementaryAbelian _
  let : IsElementaryAbelian 2 C :=
    { toIsMulCommutative := .of_setLike_mul_comm (fun x hx y hy =>
        setLike_mul_comm (show x ∈ Z from hx.1) (show y ∈ Z from hy.1))
      exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr (fun x =>
        Subtype.ext (elemPow_eq_one_of_isElementaryAbelian (A := Z) (p := 2) x x.property.1)) }
  have hZU : Z ≤ stabilizer T F :=
    ((centralOmega_le_thompsonAlpha _).trans (alpha_le_baumann _)).trans
      (le_inf inf_le_left d.baumann_invariant)
  exact false_of_a4_product_and_e4_s4 eX eG hcore
    (inf_le_left.trans hZU) le_sup_right inf_le_right d.central_fixed_card

end CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.ComponentBranch
