module
public import Theory.GroupTheory.PResidual.CentralSylowFrattini
public import Theory.SpecificGroups.Alternating.FourPairAutomorphisms

/-!
# Detecting a central two-cover of A₄ on a normal elementary subgroup

Let a finite two-perfect group E map onto A₄ with central two-group
kernel. If a normal elementary abelian subgroup has nontrivial image,
that image is the Klein four-group. Transfer and the Sylow Frattini
argument force the elementary subgroup to be Sylow in E; its trivial
Frattini subgroup then kills the kernel.

The original local residual in Aschbacher--Smith 13.2.12, printed p.883,
uses its elementary omega orbit for this detection. No classification of
central covers or multiplier formula is needed.
-/

public section
open Subgroup
open scoped IsMulCommutative
namespace alternatingGroup

/-- A normal elementary subgroup detecting the Klein four quotient makes
a two-perfect central two-cover of A₄ faithful. -/
theorem four_cover_injective_of_normal_elementary_image {E : Type*} [Group E] [Finite E]
    (f : E →* alternatingGroup (Fin 4)) (hf : Function.Surjective f)
    (hp : IsPPerfect 2 E) (hk : IsPGroup 2 f.ker) (hc : f.ker ≤ center E)
    (U : Subgroup E) [U.Normal] [IsElementaryAbelian 2 U]
    (hu : U.map f ≠ ⊥) : Function.Injective f := by
  let : (U.map f).Normal := (inferInstance : U.Normal).map f hf
  have hUC : U.map f ≤ pCore 2 (alternatingGroup (Fin 4)) :=
    le_sSup ⟨inferInstance,(IsElementaryAbelian.isPGroup 2 U).map f⟩
  have hUK : U.map f = AlternatingFourPair.K := by
    rcases AlternatingFourPair.normalA4 (U.map f) with h | h | h
    · exact (hu h).elim
    · exact h
    · rw [h] at hUC
      have he : pCore 2 (alternatingGroup (Fin 4)) = ⊤ := top_unique hUC
      have hh := congrArg (fun N : Subgroup (alternatingGroup (Fin 4)) => Nat.card N) he
      rw [AlternatingFourPair.twoCore_eq_kleinFour,
        alternatingGroup.kleinFour_card_of_card_eq_four (by norm_num),card_top,
        alternatingGroup.card_of_card_eq_four (by norm_num)] at hh
      omega
  obtain ⟨S,hUS⟩ := (IsElementaryAbelian.isPGroup 2 U).exists_le_sylow
  have hS : U = (S : Subgroup E) :=
    sylow_eq_of_map_eq_of_central_kernel_of_isPPerfect hp S f hc U hUS (by
      rw [hUK]
      exact (alternatingGroup.two_sylow_eq_kleinFour_of_card_eq_four
        (by norm_num) (S.mapSurjective hf)).le)
  let : IsElementaryAbelian 2 S := hS ▸ inferInstance
  let : Fact (IsPGroup 2 S) := ⟨S.isPGroup'⟩
  have hF : frattini S = ⊥ := frattini_eq_bot_of_isElementaryAbelian (p := 2)
  have hK := central_subgroup_le_frattini_sylow_of_isPPerfect hp S
    (f.ker.subgroupOf (S : Subgroup E)) (by
      rintro _ ⟨x,hx,rfl⟩
      exact hc hx)
  apply (MonoidHom.ker_eq_bot_iff f).mp
  apply bot_unique
  intro x hx
  have hxS := hk.le_sylow_of_normal S hx
  have hh := hK (show (⟨x,hxS⟩ : S) ∈ f.ker.subgroupOf (S : Subgroup E) from hx)
  rw [hF] at hh
  exact congrArg Subtype.val hh

end alternatingGroup
