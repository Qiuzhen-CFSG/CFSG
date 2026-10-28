module

public import Theory.SpecificGroups.SymmetricEight.FourBlockCoreAction
public import Mathlib.GroupTheory.GroupAction.Transitive
public import Mathlib.GroupTheory.Sylow
public import Mathlib.Logic.Equiv.Fintype
import Mathlib.Tactic

/-!
# A free four-group forces transitivity in a two-core-free eight-point group

If the group has a proper orbit, freeness of its four-subgroup puts at least
four points in that orbit and at least four in its complement. Both sets
therefore have four points. Every nonidentity element of the four-subgroup
is a double transposition on each set, hence belongs to the normal elementary
sixteen-group of the block stabilizer. Intersecting that normal two-group
with the original group contradicts its trivial two-core.

The only finite check identifies a fixed-point-free involution preserving
the two specified four-point sets with the product of two double transpositions.
-/

public noncomputable section
open Subgroup Equiv
namespace Theory.SpecificGroups.SymmetricEight
namespace FreeFourTransitivity
open A6ShadowTwoLocals FourBlockCoreAction

private def blockCode (i : Fin 8) : Fin 4 := ⟨i.val % 4, Nat.mod_lt _ (by decide)⟩

set_option synthInstance.maxSize 512 in
private theorem block_involution_entry (a b i j : Fin 8)
    (ha : a.val / 4 = 0) (hb : b.val / 4 = 1) (ha0 : a ≠ 0) (hb4 : b ≠ 4)
    (hblock : j.val / 4 = i.val / 4) (hfree : j ≠ i)
    (hz : j = 0 ↔ i = a) (ha' : j = a ↔ i = 0)
    (hf : j = 4 ↔ i = b) (hb' : j = b ↔ i = 4) :
    j = kleinPerm (blockCode a) (blockCode b) i := by
  revert a b i j
  decide

private theorem free_involution_in_block_core (g : S8)
    (hblock : ∀ i : Fin 8, (g i).val / 4 = i.val / 4)
    (hsq : g ^ 2 = 1) (hfree : ∀ i, g i ≠ i) : g ∈ kleinGroup := by
  have hinv (i : Fin 8) : g (g i) = i := congrArg (fun p : S8 => p i) hsq
  have hpair (i k : Fin 8) : g i = k ↔ i = g k := by
    constructor
    · intro he
      exact (hinv i).symm.trans (congrArg g he)
    · intro he
      rw [he, hinv]
  refine ⟨blockCode (g 0), blockCode (g 4), Equiv.ext fun i => ?_⟩
  exact block_involution_entry (g 0) (g 4) i (g i)
    (hblock 0) (hblock 4) (hfree 0) (hfree 4) (hblock i) (hfree i)
    (hpair i 0) g.injective.eq_iff (hpair i 4) g.injective.eq_iff

private theorem orbit_map_injective (A : Subgroup S8)
    (hfree : ∀ a ∈ A, a ≠ 1 → ∀ i, a i ≠ i) (i : Fin 8) :
    Function.Injective (fun a : A => (a : S8) i) := by
  intro a b hab
  by_contra hn
  have hne : (b : S8)⁻¹ * a ≠ 1 := by
    intro he
    exact hn (Subtype.ext (inv_mul_eq_one.mp he).symm)
  apply hfree _ (A.mul_mem (A.inv_mem b.property) a.property) hne i
  change (b : S8).symm ((a : S8) i) = i
  change (a : S8) i = (b : S8) i at hab
  rw [hab, Equiv.symm_apply_apply]

private theorem orbit_invariant (X : Subgroup S8) (g : S8) (hg : g ∈ X)
    (i : Fin 8) : g i ∈ MulAction.orbit X (0 : Fin 8) ↔
      i ∈ MulAction.orbit X (0 : Fin 8) := by
  rw [MulAction.mem_orbit_iff, MulAction.mem_orbit_iff]
  constructor
  · rintro ⟨x, hx⟩
    refine ⟨(⟨g, hg⟩ : X)⁻¹ * x, ?_⟩
    change g⁻¹ ((x : S8) 0) = i
    rw [show (x : S8) 0 = g i from hx]
    exact g.symm_apply_apply i
  · rintro ⟨x, rfl⟩
    exact ⟨(⟨g, hg⟩ : X) * x, rfl⟩

/-- The actual eight-point action of a two-core-free group containing a
free elementary four-group is transitive. -/
theorem transitive (X A : Subgroup S8) (hAX : A ≤ X) (hA : Nat.card A = 4)
    (hA2 : ∀ a ∈ A, a ^ 2 = 1)
    (hfree : ∀ a ∈ A, a ≠ 1 → ∀ i, a i ≠ i)
    (hcore : pCore 2 X = ⊥) : MulAction.IsPretransitive X (Fin 8) := by
  classical
  apply (MulAction.isPretransitive_iff_base (G := X) (0 : Fin 8)).mpr
  intro y
  by_contra hy
  let s : Set (Fin 8) := MulAction.orbit X 0
  have hys : y ∉ s := by simpa only [s, MulAction.mem_orbit_iff] using hy
  let intoOrbit : A → s := fun a =>
    ⟨(a : S8) 0, MulAction.mem_orbit_iff.mpr ⟨⟨a, hAX a.property⟩, rfl⟩⟩
  have hinj : Function.Injective intoOrbit := fun a b hab =>
    orbit_map_injective A hfree 0 (congrArg Subtype.val hab)
  let intoCompl : A → ↥(sᶜ) := fun a =>
    ⟨(a : S8) y, fun hm => hys ((orbit_invariant X a (hAX a.property) y).mp hm)⟩
  have hcinj : Function.Injective intoCompl := fun a b hab =>
    orbit_map_injective A hfree y (congrArg Subtype.val hab)
  have hsge : 4 ≤ s.ncard := by
    simpa only [hA, Nat.card_coe_set_eq] using Nat.card_le_card_of_injective intoOrbit hinj
  have hcge : 4 ≤ sᶜ.ncard := by
    simpa only [hA, Nat.card_coe_set_eq] using Nat.card_le_card_of_injective intoCompl hcinj
  have hsum : s.ncard + sᶜ.ncard = 8 := by
    simpa only [Nat.card_fin] using Set.ncard_add_ncard_compl s
  have hsc : Nat.card s = 4 := by rw [Nat.card_coe_set_eq]; omega
  let b : Set (Fin 8) := {i | i.val < 4}
  have hbc : Nat.card b = 4 := by
    rw [Nat.card_eq_fintype_card]
    decide
  let e : s ≃ b := (Finite.card_eq.mp (hsc.trans hbc.symm)).some
  let c := e.extendSubtype
  let f := (MulAut.conj c).toMonoidHom
  have hmark (i : Fin 8) : (c i).val < 4 ↔ i ∈ s := by
    constructor
    · intro hi
      by_contra hn
      exact e.extendSubtype_not_mem i hn hi
    · exact e.extendSubtype_mem i
  have hblock (g : S8) (hg : g ∈ X) (i : Fin 8) :
      (f g i).val / 4 = i.val / 4 := by
    have he : (f g i).val < 4 ↔ i.val < 4 := by
      change (c (g (c.symm i))).val < 4 ↔ i.val < 4
      rw [hmark, orbit_invariant X g hg]
      simpa only [c, Equiv.apply_symm_apply] using (hmark (c.symm i)).symm
    have hi := i.isLt
    have hgi := (f g i).isLt
    omega
  have hfour (g : S8) (hg : g ∈ X) : f g ∈ fourStabilizer := by
    intro i j
    change (f g i).val / 4 = (f g j).val / 4 ↔ i.val / 4 = j.val / 4
    rw [hblock g hg i, hblock g hg j]
  have hn : fourStabilizer ≤ normalizer (kleinGroup : Set S8) := by
    rw [← fourStabilizer_pCoreIn]
    exact fourStabilizer.le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image fourStabilizer (pCore 2 fourStabilizer))
  let K := kleinGroup.comap f
  have hKp : IsPGroup 2 K := by
    apply IsPGroup.comap_of_injective _ f (MulAut.conj c).injective
    rw [← fourStabilizer_pCoreIn]
    exact isPGroup_pCoreIn 2 fourStabilizer
  have hXK : X ≤ normalizer (K : Set S8) := by
    apply le_normalizer_iff.mpr
    intro g hg k hk
    change f (g * k * g⁻¹) ∈ kleinGroup
    rw [map_mul, map_mul, map_inv]
    exact (hn (hfour g hg) _).mp hk
  have hAK : A ≤ K := by
    intro a ha
    change f a ∈ kleinGroup
    by_cases ha1 : a = 1
    · rw [ha1, map_one]
      exact one_mem _
    apply free_involution_in_block_core (f a) (hblock a (hAX ha))
    · rw [← map_pow, hA2 a ha, map_one]
    · intro i hi
      apply hfree a ha ha1 (c.symm i)
      have hh := congrArg c.symm hi
      change c.symm (c (a (c.symm i))) = c.symm i at hh
      simpa only [c.symm_apply_apply] using hh
  have hP : X ⊓ K ≤ X.pCoreIn 2 := le_pCoreIn_of_normalizes
    (hKp.to_le inf_le_right) inf_le_left
    ((le_inf X.le_normalizer hXK).trans inf_normalizer_le_normalizer_inf)
  have hAb : A = ⊥ := by
    apply bot_unique
    have he : X.pCoreIn 2 = ⊥ := by
      change (pCore 2 X).map X.subtype = ⊥
      rw [hcore, Subgroup.map_bot]
    exact (le_inf hAX hAK).trans (he ▸ hP)
  rw [hAb, card_bot] at hA
  omega

/-- In a transitive eight-point action, a Sylow subgroup of order eight
acts freely on every point. -/
theorem sylow_free (X : Subgroup S8) [MulAction.IsPretransitive X (Fin 8)]
    (S : Sylow 2 X) (hS : Nat.card S = 8) :
    ∀ g ∈ (S : Subgroup X), g ≠ 1 → ∀ i : Fin 8, (g : S8) i ≠ i := by
  intro g hg hne i hfix
  let L := MulAction.stabilizer X i
  have hLi : L.index = 8 := by
    simpa only [Nat.card_fin] using MulAction.index_stabilizer_of_transitive X i
  have hLc : Nat.card L = (S : Subgroup X).index := by
    have hs := (S : Subgroup X).card_mul_index
    have hl := L.index_mul_card
    rw [hS] at hs
    rw [hLi] at hl
    omega
  let P := (S : Subgroup X) ⊓ L
  have hPne : P ≠ ⊥ := by
    intro hb
    have hm : g ∈ P := ⟨hg, hfix⟩
    rw [hb, mem_bot] at hm
    exact hne hm
  have hp := (S.isPGroup'.to_le (show P ≤ (S : Subgroup X) from inf_le_left)).card_eq_or_dvd
  have hd : 2 ∣ Nat.card P := hp.resolve_left (fun he => hPne (card_eq_one.mp he))
  have hh : 2 ∣ Nat.card L := hd.trans (card_dvd_of_le (show P ≤ L from inf_le_right))
  rw [hLc] at hh
  exact S.not_dvd_index hh

end FreeFourTransitivity
end Theory.SpecificGroups.SymmetricEight
