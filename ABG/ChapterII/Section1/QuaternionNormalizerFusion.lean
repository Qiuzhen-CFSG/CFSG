module
public import ABG.ChapterII.Section1.FocalGenerators
public import Theory.GroupTheory.SpecificGroups.QuaternionEightAut
public import Theory.GroupTheory.NormalizerFullAutomorphisms

/-!
# Full quaternion normalizer fusion

Let `U ≤ P ≤ G`, where `G` is finite and `U` is a quaternion group of
order eight. If `|N_G(U) : U C_G(U)| = 6`, the subgroup of `P` generated
by normalizer fusion differences at `U` is exactly the copy of `U` in `P`.
No Sylow or quasi-dihedral hypothesis is needed for this local calculation.
This is the high-index quaternion contribution to the focal subgroup in
Alperin–Brauer–Gorenstein, Chapter II, §1, Proposition 1, article pp.10–11,
of `refs/latex/alperin-brauer-gorenstein.tex`.

The full outer index six is the index of inner automorphisms in the full
quaternion automorphism group. Thus the normalizer realizes every
automorphism; the comparison retains the denominator `U C_G(U)`.
Two explicit quaternion automorphisms realize the standard generators as
differences `x⁻¹ * e x`. Transport through the actual isomorphism with `U`
and the shared normalizer-fusion membership lemma puts these generators in
the local fusion subgroup. Quaternion normal forms supply every element
of `U`. Conversely normalizer differences remain inside `U`.
-/

namespace ABG
variable {G : Type*} [Group G]
/-- Outer automizer index six makes quaternion normalizer differences generate the quaternion subgroup. -/
public theorem quaternion_normalizerFusionSubgroup_eq [Finite G]
    (P U : Subgroup G) (hUP : U ≤ P) (hU : Nonempty (U ≃* QuaternionGroup 2))
    (hi : outerAutomizerIndex U=6) :
    normalizerFusionSubgroup P U=U.subgroupOf P := by
  obtain ⟨eU⟩ := hU
  have hsurj : Function.Surjective U.normalizerMonoidHom := by
    apply Subgroup.normalizerMonoidHom_surjective_of_outer_index U
    rw [QuaternionGroup.index_range_conj_of_equiv eU]
    exact hi
  let F := normalizerFusionSubgroup P U
  let j := Subgroup.inclusion hUP
  obtain ⟨e,f,x,y,hx,hy⟩ := QuaternionGroup.aut_difference_generators_two
  have hd (a : MulAut (QuaternionGroup 2)) (z : QuaternionGroup 2) :
      j (eU.symm (z⁻¹*a z)) ∈ F := by
    have h := normalizerFusionSubgroup_mem_of_automorphism P U hUP hsurj (MulAut.congr eU.symm a) (eU.symm z)
    simpa only [MulAut.congr_apply,MulEquiv.trans_apply,MulEquiv.symm_symm,MulEquiv.apply_symm_apply,map_mul,map_inv] using h
  have ha : j (eU.symm (QuaternionGroup.a 1)) ∈ F := by
    rw [←hx]
    exact hd e x
  have hb : j (eU.symm (QuaternionGroup.xa 0)) ∈ F := by
    rw [←hy]
    exact hd f y
  apply le_antisymm (normalizerFusionSubgroup_le P U)
  intro z hz
  let u : U := ⟨z.val,hz⟩
  have hgen : ∀ q : QuaternionGroup 2, j (eU.symm q) ∈ F := by
    intro q
    cases q with
    | a i =>
      have ht := F.pow_mem ha i.val
      rw [←map_pow,←map_pow,QuaternionGroup.a_one_pow,ZMod.natCast_zmod_val] at ht
      exact ht
    | xa i =>
      have ht := F.mul_mem hb (F.pow_mem ha i.val)
      rw [←map_pow,←map_pow,←map_mul,←map_mul,QuaternionGroup.a_one_pow,
        ZMod.natCast_zmod_val,QuaternionGroup.xa_mul_a,zero_add] at ht
      exact ht
  have hu : j u ∈ F := by
    simpa only [MulEquiv.symm_apply_apply] using hgen (eU u)
  have he : j u = z := by
    apply Subtype.ext
    exact Subgroup.coe_inclusion hUP u
  exact he ▸ hu
end ABG
