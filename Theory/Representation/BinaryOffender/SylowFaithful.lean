module
public import Theory.Representation.BinaryOffender.ActionImage
public import Theory.PPrimeCore
public import Theory.GroupTheory.SylowNormalRestriction

/-!
# Detecting faithful actions on a Sylow subgroup

When the odd core is trivial, a normal action kernel disjoint from a Sylow
two-subgroup is trivial. Intersecting that Sylow with the kernel shows that
the kernel has odd order, so it lies in the odd core. No faithfulness of the
whole actor is assumed. The original square action in Aschbacher--Smith
8.3.12, printed p.726, uses this criterion after proving Sylow faithfulness.
-/

public section
open Subgroup
namespace Representation.BinaryOffender
variable {H W : Type*} [Group H] [Finite H]
  [AddCommGroup W] [Module (ZMod 2) W]

/-- Trivial odd core promotes faithfulness on a Sylow two-subgroup to
faithfulness of the whole action. -/
theorem faithful_of_sylow_two (ρ : Representation (ZMod 2) H W)
    (S : Sylow 2 H) (ho : pPrimeCore 2 H = ⊥)
    (hf : ∀ a ∈ (S : Subgroup H), (∀ w, ρ a w = w) → a = 1) :
    Function.Injective ρ := by
  have hdis : (S : Subgroup H) ⊓ ρ.ker = ⊥ := by
    apply bot_unique
    intro a ha
    exact hf a ha.1 (fun w => LinearMap.congr_fun ha.2 w)
  obtain ⟨R,hR⟩ := S.exists_sylow_map_eq_inf_of_normal ρ.ker
  have hRbot : (R : Subgroup ρ.ker) = ⊥ := by
    apply map_injective ρ.ker.subtype_injective
    simpa only [Subgroup.map_bot,hdis] using hR
  have hodd : Nat.Coprime 2 (Nat.card ρ.ker) :=
    Nat.prime_two.coprime_iff_not_dvd.mpr (fun hd => (R.ne_bot_of_dvd_card hd) hRbot)
  exact (MonoidHom.ker_eq_bot_iff ρ).mp
    (pPrimeCore_eq_bot_iff.mp ho ρ.ker inferInstance hodd)
end Representation.BinaryOffender

