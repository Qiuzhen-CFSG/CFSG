module
public import Theory.SpecificGroups.SymmetricEight.A6ShadowTwoLocals.Basic
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.Parabolics.RankOne

/-!
# Keeping the component parabolic separate from its Sylow extension

For a normal `L` with `I = LS`, Dedekind's identity gives
`M ∩ I = (M ∩ L)S`. The same identity holds after passage to the actual
star quotient. The component intersection maps into A₈ under any marked
`I* ≃ S₈` equivalence; in particular it cannot be the whole stabilizer of
four pairs, since that stabilizer contains an odd transposition.

This distinction is necessary in reading 15.3.28(3): the text calls `M_L*`
a middle-node minimal parabolic of `L*S*`. The component intersection and
its extension by `S*` must be recorded separately. The output interface
below requires both actual permutation-subgroup identities. Its existence,
and the identification with the middle-node Lie parabolic, remain part
of the classification obligation; no classification is asserted here.

Source: Aschbacher–Smith, combined manuscript (1 March 2004),
15.3.27(4) and 15.3.28(3), printed pp.1130–1131 (PDF pp.1147–1148).
-/

@[expose] public section
open Subgroup
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Parabolics
variable {G : Type*} [Group G]

/-- The full intersection is the component intersection extended by `S`. -/
theorem intersection_eq_component_intersection_sup
    (d : LocalData G) {I : Subgroup G} (c : ComponentWitness d I)
    (hn : (c.L.subgroupOf I).Normal) (hI : I = c.L ⊔ d.S) :
    d.MI I = (d.M ⊓ c.L) ⊔ d.S := by
  have hLI := component_le c
  have hSI : d.S ≤ I := hI ▸ le_sup_right
  have hSM : d.S ≤ d.M := inf_le_left.trans d.sylow_le
  let : (c.L.subgroupOf I).Normal := hn
  have hgen : c.L.subgroupOf I ⊔ d.S.subgroupOf I = ⊤ := by
    apply map_injective I.subtype_injective
    rw [Subgroup.map_sup, map_subgroupOf_eq_of_le hLI, map_subgroupOf_eq_of_le hSI,
      ← MonoidHom.range_eq_map, range_subtype]
    exact hI.symm
  apply le_antisymm ?_ (sup_le (le_inf inf_le_left (inf_le_right.trans hLI)) (le_inf hSM hSI))
  intro x hx
  have hxgen : (⟨x, hx.2⟩ : I) ∈ c.L.subgroupOf I ⊔ d.S.subgroupOf I := hgen ▸ mem_top _
  obtain ⟨l, hl, s, hs, he⟩ := mem_sup_of_normal_left.mp hxgen
  have hes : (l : G) * (s : G) = x := congrArg Subtype.val he
  have hlM : (l : G) ∈ d.M := by
    rw [(eq_mul_inv_iff_mul_eq).mpr hes]
    exact d.M.mul_mem hx.1 (d.M.inv_mem (hSM hs))
  exact hes ▸ ((d.M ⊓ c.L) ⊔ d.S).mul_mem (mem_sup_left ⟨hlM, hl⟩) (mem_sup_right hs)

/-- The corresponding identity in `I/C_I(U_I)`, with no kernel change. -/
theorem intersection_star_eq_component_intersection_sup
    (d : LocalData G) {I : Subgroup G} (c : ComponentWitness d I)
    (hn : (c.L.subgroupOf I).Normal) (hI : I = c.L ⊔ d.S) :
    d.starImage I (d.MI I) = d.starImage I (d.M ⊓ c.L) ⊔ d.starImage I d.S := by
  have hSI : d.S ≤ I := hI ▸ le_sup_right
  change ((d.MI I).subgroupOf I).map (d.starMap I) = _
  rw [intersection_eq_component_intersection_sup d c hn hI,
    subgroupOf_sup (inf_le_right.trans (component_le c)) hSI, Subgroup.map_sup]
  rfl

/-- A marked component intersection has only even permutations. -/
theorem component_intersection_star_le_alternating
    (d : LocalData G) {I : Subgroup G} (c : ComponentWitness d I)
    (e : d.Star I ≃* Equiv.Perm (Fin 8))
    (hL : (d.starImage I c.L).map e.toMonoidHom = alternatingGroup (Fin 8)) :
    (d.starImage I (d.M ⊓ c.L)).map e.toMonoidHom ≤ alternatingGroup (Fin 8) := by
  rw [← hL]
  apply map_mono
  apply map_mono
  exact comap_mono inf_le_right

/-- An extended permutation subgroup with an odd element cannot equal
`(M ∩ L)*` under an equivalence taking `L*` to A₈. -/
theorem component_intersection_star_ne_of_odd_member
    (d : LocalData G) {I : Subgroup G} (c : ComponentWitness d I)
    (e : d.Star I ≃* Equiv.Perm (Fin 8))
    (hL : (d.starImage I c.L).map e.toMonoidHom = alternatingGroup (Fin 8))
    (P : Subgroup (Equiv.Perm (Fin 8))) (p : Equiv.Perm (Fin 8))
    (hp : p ∈ P) (hodd : p ∉ alternatingGroup (Fin 8)) :
    (d.starImage I (d.M ⊓ c.L)).map e.toMonoidHom ≠ P := by
  intro he
  exact hodd ((he ▸ component_intersection_star_le_alternating d c e hL) hp)

/-- In particular, the full four-pair stabilizer is an extension marker,
not a possible image of `(M ∩ L)*`. The odd witness is `(0 1)`. -/
theorem component_intersection_star_ne_pair_stabilizer
    (d : LocalData G) {I : Subgroup G} (c : ComponentWitness d I)
    (e : d.Star I ≃* Equiv.Perm (Fin 8))
    (hL : (d.starImage I c.L).map e.toMonoidHom = alternatingGroup (Fin 8)) :
    (d.starImage I (d.M ⊓ c.L)).map e.toMonoidHom ≠
      Theory.SpecificGroups.SymmetricEight.A6ShadowTwoLocals.pairStabilizer :=
  component_intersection_star_ne_of_odd_member d c e hL _
    (Equiv.swap 0 1) (by decide) (by
      rw [Equiv.Perm.mem_alternatingGroup, Equiv.Perm.sign_swap (by decide)]
      decide)

/-- The permutation part of the third alternative of 15.3.28. Both markings
must be constructed; the full classification must also justify their
middle-node interpretation in the `L₄(2)` root geometry. -/
structure MiddleNodePermutationMarking (d : LocalData G) (I L : Subgroup G) where
  equiv : d.Star I ≃* Equiv.Perm (Fin 8)
  component : (d.starImage I L).map equiv.toMonoidHom = alternatingGroup (Fin 8)
  component_intersection : (d.starImage I (d.M ⊓ L)).map equiv.toMonoidHom =
    Theory.SpecificGroups.SymmetricEight.A6ShadowTwoLocals.pairStabilizer ⊓
      alternatingGroup (Fin 8)
  extended_intersection : (d.starImage I (d.MI I)).map equiv.toMonoidHom =
    Theory.SpecificGroups.SymmetricEight.A6ShadowTwoLocals.pairStabilizer

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Parabolics
