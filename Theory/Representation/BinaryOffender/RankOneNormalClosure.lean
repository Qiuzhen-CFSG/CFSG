module

public import Theory.Representation.BinaryOffender.CommutatorRank
public import Theory.Representation.BinaryOffender.EquivariantOffender
public import Theory.Representation.BinaryOffender.Stability

/-!
# Rank-one involutions generate their normal closure by best offenders

The cyclic subgroup of a nonidentity involution of displacement rank at most
one is a best offender: its only proper subgroup is trivial. Conjugation
preserves this property, and restriction to the literal normal closure
therefore makes its offender-generated subgroup the whole actor.

This supplies the generation hypothesis for the application of B.5.6 in
Aschbacher–Smith, G.6.4, printed pp.345–346. The proof requires no faithful
action, solvability, or classification input.
-/

public section

open Subgroup
namespace Representation.BinaryOffender
variable {G V : Type*} [Group G] [Finite G] [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]

theorem bestOffender_of_involution_displacement_le_one
    (ρ : Representation (ZMod 2) G V) (a : G) (ha : a ^ 2 = 1) (hne : a ≠ 1)
    (hr : Module.finrank (ZMod 2) (LinearMap.range (ρ a - LinearMap.id)) ≤ 1) :
    IsBestOffender ρ (zpowers a) := by
  have hc : Nat.card (zpowers a) = 2 := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime ha hne
  have hff : fixedCodim ρ (zpowers a) ≤ rank (zpowers a) := by
    rw [fixedCodim_zpowers_eq_displacement_rank]
    simpa only [rank, hc, show Nat.log 2 2 = 1 by decide] using hr
  refine ⟨⟨?_, IsElementaryAbelian.zpowers_of_pow_eq_one ha⟩, ?_⟩
  · intro hb
    exact hne (by simpa only [hb, mem_bot] using mem_zpowers a)
  · intro B hB
    have hd : Nat.card B ∣ 2 := hc ▸ card_dvd_of_le hB
    rcases (Nat.dvd_prime Nat.prime_two).mp hd with hb | hb
    · have he : B = ⊥ := card_eq_one.mp hb
      rw [he, weight_bot]
      exact (fixedCodim_le_rank_iff ρ _).mp hff
    · have he : B = zpowers a := eq_of_le_of_card_ge hB (by omega)
      rw [he]

theorem normalClosure_offenderSubgroup_of_rank_one
    (ρ : Representation (ZMod 2) G V) (a : G) (ha : a ^ 2 = 1) (hne : a ≠ 1)
    (hr : Module.finrank (ZMod 2) (LinearMap.range (ρ a - LinearMap.id)) ≤ 1) :
    offenderSubgroup (ρ.comp (normalClosure ({a} : Set G)).subtype) = ⊤ := by
  let K := normalClosure ({a} : Set G)
  let J := offenderSubgroup (ρ.comp K.subtype)
  have hbest := bestOffender_of_involution_displacement_le_one ρ a ha hne hr
  have hKJ : K ≤ J.map K.subtype := by
    apply (Subgroup.closure_le (J.map K.subtype)).mpr
    intro x hx
    obtain ⟨y, hy, hxy⟩ := Group.mem_conjugatesOfSet_iff.mp hx
    have hya : y = a := Set.mem_singleton_iff.mp hy
    subst y
    obtain ⟨g, rfl⟩ := isConj_iff.mp hxy
    have hb : IsBestOffender ρ (zpowers (g * a * g⁻¹)) := by
      simpa only [MonoidHom.map_zpowers, MulEquiv.coe_toMonoidHom, MulAut.conj_apply] using hbest.map_conj ρ g
    have hle : zpowers (g * a * g⁻¹) ≤ K :=
      zpowers_le.mpr (conjugatesOfSet_subset_normalClosure hx)
    have hb' := hb.subgroupOf ρ hle
    have hm : (zpowers (g * a * g⁻¹)).subgroupOf K ≤ J :=
      le_iSup_of_le _ (le_iSup_of_le ⟨hb', le_top⟩ le_rfl)
    exact ⟨⟨_, hle (mem_zpowers _)⟩, hm (mem_zpowers _), rfl⟩
  apply top_unique
  intro k _
  obtain ⟨j, hj, he⟩ := hKJ k.property
  exact (show j = k from Subtype.ext he) ▸ hj
end Representation.BinaryOffender
