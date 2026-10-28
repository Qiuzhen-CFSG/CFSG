module
public import Glauberman.PushingUpKernelOrbit
public import Glauberman.PushingUpNaturalActionConsequences

/-!
# The central-chief quotient from the original natural action

The source2.9 natural fixed quotient supplies the uniform fixed-index bound
in the maximum-abelian selection, and the fixed-index sixteen and moved
centralizer identity for the conjugate supplement. The selected-actor7.6
consumer therefore gives the cyclic-orbit formula for every invariant kernel
which contains the original core omega. The characteristic-intersection
argument then chooses a kernel with only central ambient chief factors.

The final theorem constructs all Main Hypothesis data on the literal quotient
H/N_alpha: characteristic two, unique Sylow maximal subgroup, an automorphism
fixing no ambient-normal subgroup, and the retained original PSL2(4) quotient.
Only the independently owned source2.9 action quotient and its natural fixed
quotient coordinates remain inputs; there is no orbit-formula, chosen-actor,
fixed-index or enlarged-omega premise.

Source: Niles, *Pushing-up in finite groups* (1979), Theorem7.2, pp.60–62.
-/

public section
open Subgroup NilesRankOneKernel Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative
namespace Glauberman
variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F]

theorem pushingUp_kernel_orbit_of_natural_bounds
    (hF : Nat.card F = 4) (S : Sylow 2 H)
    (hu : Order.HasUniqueMaximalOver (S : Subgroup H) ⊤)
    (K : Subgroup H) [K.Normal]
    (e : (H ⧸ K) ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) F)
    (hno : Theory.GroupTheory.NoCharacteristicNormal (S : Subgroup H))
    (hlower : ∀ A : Subgroup H, A ∈ thompsonAbelianSubgroups (S : Subgroup H) →
      ¬ A ≤ pCore 2 H →
      4 ≤ (omegaCenterIn (pCore 2 H) ⊓ centralizer (A : Set H)).relIndex
        (omegaCenterIn (pCore 2 H)))
    (hnatural : ∀ L : Subgroup H, L ⊔ pCore 2 H = ⊤ →
      16 ≤ (centralizer (L : Set H)).relIndex (omegaCenterIn (pCore 2 H)) ∧
      (S : Subgroup H) ⊓ centralizer
        ((⁅omegaCenterIn (pCore 2 H),L⁆ : Subgroup H) : Set H) = pCore 2 H)
    (α : MulAut S)
    (hVN : (omegaCenterIn (pCore 2 H)).subgroupOf (S : Subgroup H) ≤
      invariantNormalKernel (S : Subgroup H) α) :
    invariantNormalKernel (S : Subgroup H) α =
      ⨅ n : ℤ, ((pCore 2 H).subgroupOf (S : Subgroup H)).map ((α ^ n).toMonoidHom) := by
  have hVS : omegaCenterIn (pCore 2 H) ≤ (S : Subgroup H) :=
    fun _ hx => pCore_isPGroup.le_sylow_of_normal S ((mem_omegaCenterIn_iff _ _).mp hx).1
  have hVN' : omegaCenterIn (pCore 2 H) ≤
      (invariantNormalKernel (S : Subgroup H) α).map (S : Subgroup H).subtype := by
    rw [← map_subgroupOf_eq_of_le hVS]
    exact map_mono hVN
  obtain ⟨A,hA,hAQ,hinter⟩ := pushingUp_exists_maximum_abelian_kernel_intersection
    hF S hu K e hno hlower α hVN'
  have hgenA := (pushingUp_maximum_abelian_replacement hF S hu K e A hA
    (hlower A hA hAQ)).1
  obtain ⟨g,hgen⟩ := original_exists_conjugate_abelian_supplement_generating hF S hu K e A hgenA
  obtain ⟨hi,hc⟩ := hnatural _ hgen
  exact pushingUp_kernel_orbit_of_selected_actor hF S hu K e α A hA hVN' hinter g hgen hi hc

/-- The original natural fixed quotient discharges the entire cyclic-orbit
formula. There is no enlarged-omega or chosen-actor premise. -/
theorem pushingUp_kernel_orbit_of_natural_quotient
    (hF : Nat.card F = 4) (S : Sylow 2 H)
    (hu : Order.HasUniqueMaximalOver (S : Subgroup H) ⊤)
    (K : Subgroup H) [K.Normal]
    (e : (H ⧸ K) ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) F)
    (hno : Theory.GroupTheory.NoCharacteristicNormal (S : Subgroup H))
    (q : H →* SL2FourNatural.SL) (hq : Function.Surjective q)
    (hk : q.ker = centralizer (omegaCenterIn (pCore 2 H) : Set H))
    (E : (Additive (omegaCenterIn (pCore 2 H)) ⧸ fixedSpace (omegaAction H) ⊤)
      ≃ₗ[ZMod 2] SL2FourNatural.V)
    (hE : ∀ h v, E (fixedQuotient (omegaAction H) ⊤ h v) =
      specialLinearNatural 2 (q h) (E v))
    (α : MulAut S)
    (hVN : (omegaCenterIn (pCore 2 H)).subgroupOf (S : Subgroup H) ≤
      invariantNormalKernel (S : Subgroup H) α) :
    invariantNormalKernel (S : Subgroup H) α =
      ⨅ n : ℤ, ((pCore 2 H).subgroupOf (S : Subgroup H)).map ((α ^ n).toMonoidHom) := by
  apply pushingUp_kernel_orbit_of_natural_bounds hF S hu K e hno _ _ α hVN
  · intro A hA hAQ
    exact original_omega_fixedIndex_lower_of_natural_quotient hF S hu K e q hq hk E hE A hA.1 hAQ
  · intro L hL
    obtain ⟨hi,hc⟩ := original_omega_supplement_natural_data q hq hk E hE L hL
    rw [inf_relIndex_left] at hi
    refine ⟨hi.ge,?_⟩
    rw [hc]
    exact original_omega_sylow_centralizer_eq hF S hu K e q hq hk

/-- Niles7.2 reduced exactly to the independent source2.9 natural-action
recognition, preserving the original central-chief kernel and quotient maps. -/
theorem exists_main_quotient_of_original_natural_action
    (hF : Nat.card F = 4) (S : Sylow 2 H)
    (hu : Order.HasUniqueMaximalOver (S : Subgroup H) ⊤)
    (K : Subgroup H) [K.Normal]
    (e : (H ⧸ K) ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) F)
    (hf : generalizedFitting H = pCore 2 H)
    (hno : Theory.GroupTheory.NoCharacteristicNormal (S : Subgroup H))
    (q : H →* SL2FourNatural.SL) (hq : Function.Surjective q)
    (hk : q.ker = centralizer (omegaCenterIn (pCore 2 H) : Set H))
    (E : (Additive (omegaCenterIn (pCore 2 H)) ⧸ fixedSpace (omegaAction H) ⊤)
      ≃ₗ[ZMod 2] SL2FourNatural.V)
    (hE : ∀ h v, E (fixedQuotient (omegaAction H) ⊤ h v) =
      specialLinearNatural 2 (q h) (E v)) :
    ∃ α : MulAut S,
      let N := (invariantNormalKernel (S : Subgroup H) α).map (S : Subgroup H).subtype
      let π := QuotientGroup.mk' N
      ∃ s : NoncentralChiefRefinement.SeriesOn N, (∀ i, s.Central i) ∧ N ≤ K ∧
        Nonempty (((H ⧸ N) ⧸ K.map π) ≃* (H ⧸ K)) ∧
        generalizedFitting (H ⧸ N) = pCore 2 (H ⧸ N) ∧
        Order.HasUniqueMaximalOver ((S : Subgroup H).map π) ⊤ ∧
        ∃ β : MulAut ((S : Subgroup H).map π),
          Theory.GroupTheory.NoInvariantNormal ((S : Subgroup H).map π) β := by
  obtain ⟨a⟩ := Matrix.ProjectiveSpecialLinearGroup.equiv_alternatingGroup_of_card_four hF
  let b := e.trans a
  let : IsSimpleGroup (alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup (by simp)
  let : IsSimpleGroup (H ⧸ K) := b.isSimpleGroup
  have hK : ¬ IsPGroup 2 (H ⧸ K) := by
    intro hp
    obtain ⟨n,hn⟩ := hp.exists_card_dvd_pow
    have hc : Nat.card (H ⧸ K) = 60 := by
      rw [Nat.card_congr b.toEquiv,nat_card_alternatingGroup]
      norm_num [Nat.factorial]
    rw [hc] at hn
    have hd : 3 ∣ 2 ^ n := dvd_trans (by norm_num : 3 ∣ 60) hn
    have : 3 ∣ 2 := Nat.Prime.dvd_of_dvd_pow (by decide) hd
    norm_num at this
  exact Theory.GroupTheory.exists_main_quotient_of_orbit_formula S hu K hK hf hno
    (pushingUp_kernel_orbit_of_natural_quotient hF S hu K e hno q hq hk E hE)

end Glauberman
