module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.LocalData
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Basic
public import Theory.Representation.BinaryPermutationNaturalStructure

/-!
# No component-fixed vector in the natural degree-eight module

A fixed nonzero vector would span a one-dimensional alternating-invariant
subspace of the irreducible six-dimensional natural module. Transport through
the compatible natural coordinates therefore gives C_{U_L}(L)=1. The marking
sends the actual component image to A₈; an abstract family label is insufficient.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), B.3.1 on p.83
and the proof of 15.3.32 on pp.1132–1133.
-/

@[expose] public section

open Subgroup BinaryPermutation
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.EightGeometry.NaturalModule.FixedGeometry
universe u
variable {G : Type u} [Group G]

private theorem natural_fixed_eq_zero (v : natural (Fin 8))
    (hv : ∀ g : alternatingGroup (Fin 8), naturalRepresentation (Fin 8) g.val v = v) :
    v = 0 := by
  by_cases hz : v = 0
  · exact hz
  let W : Subrepresentation (alternatingNaturalRepresentation (Ω := Fin 8)) :=
    ⟨Submodule.span (ZMod 2) {v}, by
      intro g x hx
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hx
      change naturalRepresentation (Fin 8) g.val (c • v) ∈ _
      rw [map_smul, hv g]
      exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_singleton v))⟩
  let _ := alternatingNatural_isIrreducible (Ω := Fin 8) (by decide)
  rcases eq_bot_or_eq_top W with h | h
  · have hvW : v ∈ W.toSubmodule := Submodule.subset_span (Set.mem_singleton v)
    rw [h] at hvW
    exact hvW
  · have hd : Module.finrank (ZMod 2) W.toSubmodule = 1 := finrank_span_singleton hz
    have htop : W.toSubmodule = ⊤ := congrArg Subrepresentation.toSubmodule h
    rw [htop, finrank_top, finrank_natural_even (Fin 8) (by decide)] at hd
    norm_num at hd

/-- The marked alternating component has no fixed vector in its natural module. -/
theorem componentModule_inf_centralizer_eq_bot (d : LocalData G) {I : Subgroup G}
    (c : ComponentWitness d I)
    (e : d.Star I ≃* Equiv.Perm (Fin 8))
    (hmark : (d.starImage I c.L).map e.toMonoidHom = alternatingGroup (Fin 8))
    (a : NaturalEightAction I (d.componentModule I c.L))
    (hactor : a.actor = e.toMonoidHom.comp (d.starMap I)) :
    d.componentModule I c.L ⊓ centralizer (c.L : Set G) = ⊥ := by
  have hLA : (c.L.subgroupOf I).map a.actor = alternatingGroup (Fin 8) := by
    rw [hactor, ← Subgroup.map_map]
    exact hmark
  apply eq_bot_iff.mpr
  intro u hu
  let u₀ : d.componentModule I c.L := ⟨u, hu.1⟩
  have hz : Multiplicative.toAdd (a.coordinates u₀) = 0 := by
    apply natural_fixed_eq_zero
    intro g
    obtain ⟨l, hl, he⟩ := hLA.ge g.property
    have hc := a.compatible l u₀
    have hfix : (d.componentModule I c.L).normalizerMonoidHom
        ⟨l, a.normalizes l.property⟩ u₀ = u₀ := by
      apply Subtype.ext
      change (l : G) * u * (l : G)⁻¹ = u
      rw [hu.2 l hl, mul_inv_cancel_right]
    rw [hfix, he] at hc
    exact (congrArg Multiplicative.toAdd hc).symm
  have he : a.coordinates u₀ = 1 := hz
  exact congrArg Subtype.val (a.coordinates.injective (he.trans a.coordinates.map_one.symm))

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.EightGeometry.NaturalModule.FixedGeometry

end
