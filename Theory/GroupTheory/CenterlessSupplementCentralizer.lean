module

public import Theory.GroupTheory.PResidual.NormalSubgroup
public import Mathlib.GroupTheory.Sylow
public import Mathlib.GroupTheory.Subgroup.Centralizer

/-!
# Centralizers in a centerless normal supplement

If a centerless normal subgroup and a Sylow p-subgroup generate the group,
the centralizer of the normal subgroup lies in that Sylow subgroup. It
embeds in the p-group quotient, and normal p-subgroups lie in every Sylow
p-subgroup.

This is the centralizer step needed to distinguish `C_I(K)` from `C_T(K)`
in Aschbacher–Smith, Lemma 15.4.22, printed p.1165.
-/

open Subgroup
variable {G : Type*} [Group G]

/-- A centerless normal Sylow supplement has p-group centralizer, contained
in the chosen Sylow subgroup. -/
public theorem Subgroup.centralizer_le_sylow_of_centerless_supplement {p : ℕ} [Fact p.Prime]
    (K : Subgroup G) [K.Normal] (S : Sylow p G)
    (hgen : K ⊔ (S : Subgroup G) = ⊤) (hZ : center K = ⊥) :
    centralizer (K : Set G) ≤ (S : Subgroup G) := by
  let C := centralizer (K : Set G)
  let f := (QuotientGroup.mk' K).comp C.subtype
  have hf : Function.Injective f := by
    apply (MonoidHom.ker_eq_bot_iff f).mp
    apply eq_bot_iff.mpr
    intro c hc
    have hcK : (c : G) ∈ K := (QuotientGroup.eq_one_iff _).mp hc
    have hz : (⟨c, hcK⟩ : K) ∈ center K := by
      apply mem_center_iff.mpr
      intro k
      exact Subtype.ext (c.property k k.property)
    rw [hZ] at hz
    exact Subtype.ext (congrArg (fun x : K => (x : G)) (mem_bot.mp hz))
  have hCp : IsPGroup p C :=
    (isPGroup_quotient_of_sup_eq_top K (S : Subgroup G) S.isPGroup' hgen).of_injective f hf
  exact hCp.le_sylow_of_normal S
