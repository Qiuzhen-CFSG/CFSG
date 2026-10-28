module

public import Theory.SpecificGroups.Held.Automorphisms.Normalizer.OrbitalPreservation.OrbitTrees
public import Theory.SpecificGroups.Held.LocalPairs.Basic

/-!
# Faithfulness of the full Held permutation-normalizer action

The checked point-stabilizer forest has five roots. In each component except
that of zero, an explicitly checked second point differs from the root.
Thus zero is the only point fixed by the full point stabilizer. A permutation
centralizing Held fixes zero and then, by transitivity, every point.

Consequently the full permutation normalizer acts faithfully on Held, and
Held itself is centerless. Surjectivity, when supplied by the separate full
automorphism-realization proof, gives an actual group equivalence.

Source data: the fixed ATLAS HeG1-p2058B0 permutations and the kernel-checked
forest in Automorphisms/Normalizer/OrbitalPreservation/OrbitTrees. No order,
simplicity or automorphism catalogue is assumed.
-/

namespace Held.LocalPairs

open Subgroup NormalizerGraph.Orbital

private def other (c : Fin 5) : Fin 2058 :=
  if c = 0 then 0 else if c = 1 then 2 else if c = 2 then 5 else if c = 3 then 15 else 22

private theorem other_color : ∀ c, color (other c) = c := by decide +kernel

private theorem other_eq_rep : ∀ c, other c = rep c ↔ c = 0 := by decide +kernel

/-- The full point stabilizer fixes only its marked point. -/
public theorem stabilizer_fixed_eq_zero (x : Fin 2058)
    (hx : ∀ g : Stabilizer, g • x = x) : x = 0 := by
  obtain ⟨g, hg⟩ := reach x
  have he : rep (color x) = x := by
    calc
      rep (color x) = g⁻¹ • (g • rep (color x)) := (inv_smul_smul g _).symm
      _ = g⁻¹ • x := congrArg (fun y => g⁻¹ • y) hg
      _ = x := hx g⁻¹
  obtain ⟨h, hh⟩ := reach (other (color x))
  rw [other_color, he] at hh
  have ho : other (color x) = rep (color x) := hh.symm.trans ((hx h).trans he.symm)
  have hc := (other_eq_rep _).mp ho
  rw [hc] at he
  exact he.symm

/-- The defining Held action has trivial permutation centralizer. -/
public theorem permutation_centralizer_eq_bot :
    centralizer (permutationGroup : Set (Equiv.Perm (Fin 2058))) = ⊥ := by
  apply le_bot_iff.mp
  intro z hz
  have hz0 : z 0 = 0 := by
    apply stabilizer_fixed_eq_zero
    intro g
    have he := congrArg (fun f : Equiv.Perm (Fin 2058) => f 0)
      (hz g.val.val g.val.property)
    change g.val.val (z 0) = z (g.val.val 0) at he
    rw [show g.val.val 0 = 0 from g.property] at he
    exact he
  apply mem_bot.mpr
  apply Equiv.ext
  intro x
  obtain ⟨h, hh⟩ := Transitivity.exists_move_zero x
  have he := congrArg (fun f : Equiv.Perm (Fin 2058) => f 0) (hz h.val h.property)
  change representation h (z 0) = z (representation h 0) at he
  rw [hz0, hh] at he
  exact he.symm

/-- The actual permutation Held carrier is centerless. -/
public theorem center_eq_bot : center He = ⊥ := by
  apply le_bot_iff.mp
  intro z hz
  have hc : representation z ∈
      centralizer (permutationGroup : Set (Equiv.Perm (Fin 2058))) := by
    intro g hg
    exact congrArg representation ((mem_center_iff.mp hz) ⟨g, hg⟩)
  rw [permutation_centralizer_eq_bot, mem_bot] at hc
  apply mem_bot.mpr
  apply representation_injective
  exact hc.trans (map_one representation).symm

/-- Conjugation by the full permutation normalizer is faithful. -/
public theorem normalizerAction_injective :
    Function.Injective permutationGroup.normalizerMonoidHom := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  rw [normalizerMonoidHom_ker, permutation_centralizer_eq_bot, bot_subgroupOf]

/-- A full realization is an actual equivalence, using the proved faithfulness. -/
public noncomputable def normalizerActionEquiv
    (hrealize : Function.Surjective permutationGroup.normalizerMonoidHom) :
    PermutationNormalizer ≃* MulAut He :=
  MulEquiv.ofBijective permutationGroup.normalizerMonoidHom
    ⟨normalizerAction_injective, hrealize⟩

public theorem normalizerActionEquiv_apply
    (hrealize : Function.Surjective permutationGroup.normalizerMonoidHom)
    (a : PermutationNormalizer) :
    normalizerActionEquiv hrealize a = permutationGroup.normalizerMonoidHom a := by
  rfl

end Held.LocalPairs
