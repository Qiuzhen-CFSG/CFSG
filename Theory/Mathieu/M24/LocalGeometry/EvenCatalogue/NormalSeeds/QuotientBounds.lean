module
public import Theory.Mathieu.M24.LocalGeometry.SextetCore
public import Theory.Mathieu.M24.LocalGeometry.PairOvergroups.QuotientConstruction.AffineCoverage
public import Theory.Mathieu.M24.LocalGeometry.PairOvergroups.QuotientConstruction.AffineLifts
public import Theory.AtlasPort.ExceptionalIsomorphisms.Order168Models
public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple
public import Mathlib.GroupTheory.IsPerfect

/-!
# Normal solvable subgroups of the native trio and sextet stabilizers

The standard trio acts onto S₃ × SL₃(2), with a two-group translation kernel.
A solvable normal image projects trivially to the simple perfect linear factor;
its remaining image has order dividing six. The standard sextet acts onto S₆
with kernel order 192. Its solvable normal image is trivial, since every
nontrivial normal subgroup of S₆ contains the perfect subgroup A₆.
In either case a normal solvable subgroup has order indivisible by nine.

These are the actual native actions constructed in the imported geometry
modules. The SL₃(2) comparison reuses the attributed ATLAS port in
`Order168Models`; see `LICENSES/ATLAS.txt`.
Source: GLS3, Table 5.3e; Aschbacher–Smith 15.3.41–42, printed p.1138.
-/

public section
namespace Sporadic.Mathieu.M24LocalGeometry.EvenCatalogue.NormalSeeds
open Subgroup PairOvergroups PairOvergroups.QuotientConstruction

/-- Transfer the normal-solvable order bound through a genuine group isomorphism. -/
theorem transport_bound {G H : Type*} [Group G] [Group H] (e : G ≃* H)
    (h : ∀ D : Subgroup H, D.Normal → Group.IsSolvable D → ¬ 9 ∣ Nat.card D)
    (D : Subgroup G) (hn : D.Normal) (hs : Group.IsSolvable D) : ¬ 9 ∣ Nat.card D := by
  let : Group.IsSolvable D := hs
  have hXn := Subgroup.Normal.map hn e.toMonoidHom e.surjective
  have hXs : Group.IsSolvable (D.map e.toMonoidHom) :=
    Group.isSolvable_of_surjective (f := e.toMonoidHom.subgroupMap D)
      (e.toMonoidHom.subgroupMap_surjective D)
  have hb := h _ hXn hXs
  rwa [card_map_of_injective (f := e.toMonoidHom) e.injective] at hb

private theorem linear_not_solvable :
    ¬ Group.IsSolvable (Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) := by
  let e := Atlas.Comparisons.Exceptional.sl3TwoEquivPsl3Two
  let := Atlas.Comparisons.Exceptional.sl3Two_simple
  let := Atlas.psl_perfect (F := ZMod 2) 3 (by decide)
  let : Group.IsPerfect (Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) :=
    Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  exact Group.IsPerfect.not_isSolvable _

private theorem linear_normal_solvable_eq_bot
    (D : Subgroup (Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)))
    (hn : D.Normal) (hs : Group.IsSolvable D) : D = ⊥ := by
  let := Atlas.Comparisons.Exceptional.sl3Two_simple
  let := hs
  rcases hn.eq_bot_or_eq_top with h | h
  · exact h
  · exact (linear_not_solvable (Group.isSolvable_of_surjective (f := D.subtype)
      (by rw [h]; exact topEquiv.surjective))).elim

/-- The actual trio quotient leaves at most one factor of three. -/
theorem trio_normal_solvable_not_nine
    (D : Subgroup (trioStabilizer standardTrio)) (hn : D.Normal)
    (hs : Group.IsSolvable D) : ¬ 9 ∣ Nat.card D := by
  let := hs
  let f := affineQuotient affineCoverage
  have hf : Function.Surjective f := affineQuotient_surjective affineCoverage affineLifts
  let l := (MonoidHom.snd (Equiv.Perm (Fin 3))
    (Matrix.SpecialLinearGroup (Fin 3) (ZMod 2))).comp f
  have hl : Function.Surjective l := by
    exact Function.Surjective.comp (f := f) Prod.snd_surjective hf
  have hL : D.map l = ⊥ := linear_normal_solvable_eq_bot _
    (Subgroup.Normal.map hn l hl)
    (Group.isSolvable_of_surjective (f := l.subgroupMap D) (l.subgroupMap_surjective D))
  let X := D.map f
  have hX : X ≤ (⊤ : Subgroup (Equiv.Perm (Fin 3))).prod ⊥ := by
    rintro _ ⟨g, hg, rfl⟩
    exact ⟨mem_top _, mem_bot.mp (hL ▸ (show l g ∈ D.map l from ⟨g, hg, rfl⟩))⟩
  have hcX : Nat.card X ∣ 6 := by
    have h := card_dvd_of_le hX
    rw [Nat.card_congr (Subgroup.prodEquiv _ _).toEquiv, Nat.card_prod] at h
    rw [card_top, card_bot, mul_one] at h
    simpa only [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin,
      show Nat.factorial 3 = 6 from rfl] using h
  let fD := f.comp D.subtype
  have hp : IsPGroup 2 fD.ker :=
    (affineQuotient_kernel_isPGroup affineCoverage).comap_subtype
  obtain ⟨n, hncard⟩ := hp.exists_card_eq
  have hcard := fD.ker.card_mul_index
  rw [index_ker, hncard] at hcard
  have hrange : fD.range = X := by
    rw [MonoidHom.range_comp, subtype_range]
  rw [hrange] at hcard
  intro h9
  have hd : 9 ∣ 2 ^ n * 6 := (hcard ▸ h9).trans (Nat.mul_dvd_mul_left _ hcX)
  have hcop : Nat.Coprime 9 (2 ^ n) := (by decide : Nat.Coprime 9 2).pow_right n
  have := hcop.dvd_of_dvd_mul_left hd
  norm_num at this

private theorem symmetric_normal_solvable_eq_bot
    (D : Subgroup (Equiv.Perm (Fin 6))) (hn : D.Normal)
    (hs : Group.IsSolvable D) : D = ⊥ := by
  let := hn
  let := hs
  by_contra h
  have hle := Equiv.Perm.alternatingGroup_le_of_normal (by simp : 5 ≤ Nat.card (Fin 6))
    ((Subgroup.nontrivial_iff_ne_bot D).mpr h)
  let : Group.IsSolvable (alternatingGroup (Fin 6)) :=
    Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hle)
      (Subgroup.inclusion_injective hle)
  let : Group.IsPerfect (alternatingGroup (Fin 6)) :=
    ⟨commutator_alternatingGroup_eq_top (by simp)⟩
  exact Group.IsPerfect.not_isSolvable (alternatingGroup (Fin 6)) inferInstance

/-- A normal solvable subgroup of the standard sextet stabilizer lies in its
order-192 column kernel. -/
theorem sextet_normal_solvable_not_nine
    (D : Subgroup (sextetStabilizer standardSextet)) (hn : D.Normal)
    (hs : Group.IsSolvable D) : ¬ 9 ∣ Nat.card D := by
  let := hs
  let f := SextetCore.columnHom
  have hX : D.map f = ⊥ := symmetric_normal_solvable_eq_bot _
    (Subgroup.Normal.map hn f SextetCore.columnHom_surjective)
    (Group.isSolvable_of_surjective (f := f.subgroupMap D) (f.subgroupMap_surjective D))
  have hD : D ≤ f.ker := by
    intro x hx
    exact mem_bot.mp (hX ▸ (show f x ∈ D.map f from ⟨x, hx, rfl⟩))
  intro h9
  have hc := h9.trans (card_dvd_of_le hD)
  rw [SextetCore.columnHom_kernel_card] at hc
  norm_num at hc

end Sporadic.Mathieu.M24LocalGeometry.EvenCatalogue.NormalSeeds
