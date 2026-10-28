module

public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.InvolutionGeometry.Models
public import Theory.SpecificGroups.Alternating.FiveLocalGeometry.CubicCentralizer

/-!
# The cubic centralizer bound in the other involution class

In the actual E₄ × A₅ model of C_G(t), a cubic subgroup has trivial
E₄ projection. Its A₅ projection has centralizer of order three. Any
two-subgroup centralizing it therefore lies in the E₄ factor and has order
at most four. Restriction of the marked equivalence gives the bound for
literal subgroups of G, before first-centralizer recognition.

Source: Aschbacher, *Sporadic Groups* (1994), proof of 47.3, printed p.262,
using the second-involution centralizer from 47.1.
-/

public section
open Subgroup
namespace CFSG.Quasithin.Janko23.J2Recognition.SourceLocal.PrimeNormalizers.ThreeLocal.CoreSylowInputs
open InvolutionGeometry

private theorem product_two_card_le (Y U : Subgroup (E4 × A5))
    (hY : Nat.card Y = 3) (hU : IsPGroup 2 U)
    (hUY : U ≤ centralizer (Y : Set (E4 × A5))) : Nat.card U ≤ 4 := by
  let f := MonoidHom.fst E4 A5
  let s := MonoidHom.snd E4 A5
  have hYf : Y.map f = ⊥ := by
    apply card_eq_one.mp
    have hd3 := card_map_dvd (H := Y) f
    have hd4 := card_subgroup_dvd_card (Y.map f)
    rw [hY] at hd3
    rw [card_E4] at hd4
    exact Nat.eq_one_of_dvd_coprimes (by decide : Nat.Coprime 3 4) hd3 hd4
  have hfirst (y : Y) : (y : E4 × A5).1 = 1 := by
    have hy : f y ∈ Y.map f := mem_map_of_mem f y.property
    simpa only [hYf, mem_bot, f, MonoidHom.coe_fst] using hy
  have hi : Function.Injective (s.comp Y.subtype) := by
    intro a b hab
    apply Subtype.ext
    exact Prod.ext ((hfirst a).trans (hfirst b).symm) hab
  have hYs : Nat.card (Y.map s) = 3 := by
    calc
      _ = Nat.card (s.comp Y.subtype).range := by rw [MonoidHom.range_comp, range_subtype]
      _ = Nat.card Y := Nat.card_congr (MonoidHom.ofInjective hi).symm.toEquiv
      _ = 3 := hY
  have hUs : U.map s ≤ centralizer (Y.map s : Set A5) := by
    rintro _ ⟨u, hu, rfl⟩ _ ⟨y, hy, rfl⟩
    simpa only [map_mul] using congrArg s (hUY hu y hy)
  have hd3 := card_dvd_of_le hUs
  rw [alternatingGroup.FiveLocalGeometry.cubic_centralizer_card
    (MulEquiv.refl A5) (Y.map s) hYs] at hd3
  obtain ⟨n, hn⟩ := (hU.map s).exists_card_dvd_pow
  have hUsbot : U.map s = ⊥ := card_eq_one.mp (Nat.eq_one_of_dvd_coprimes
    ((by norm_num : Nat.Coprime 3 2).pow_right n) hd3 hn)
  have hsecond (u : U) : (u : E4 × A5).2 = 1 := by
    have hu : s u ∈ U.map s := mem_map_of_mem s u.property
    simpa only [hUsbot, mem_bot, s, MonoidHom.coe_snd] using hu
  have hfi : Function.Injective (f.comp U.subtype) := by
    intro a b hab
    exact Subtype.ext (Prod.ext hab ((hsecond a).trans (hsecond b).symm))
  simpa only [card_E4] using Nat.card_le_card_of_injective _ hfi

variable {G : Type*} [Group G] [Finite G] {D : Seed G} {t : G}

/-- Every two-subgroup in the common centralizer of a root involution and
an arbitrary cubic subgroup has order at most four. -/
theorem root_two_card_le (S : SecondCentralizer D t)
    (Y U : Subgroup G) (hY : Nat.card Y = 3) (hU : IsPGroup 2 U)
    (hYt : Y ≤ involutionCentralizer t) (hUt : U ≤ involutionCentralizer t)
    (hUY : U ≤ centralizer (Y : Set G)) : Nat.card U ≤ 4 := by
  let H := involutionCentralizer t
  let Y' := (Y.subgroupOf H).map S.equiv.toMonoidHom
  let U' := (U.subgroupOf H).map S.equiv.toMonoidHom
  have hcY : Nat.card Y' = 3 := by
    rw [card_map_of_injective S.equiv.injective,
      Nat.card_congr (subgroupOfEquivOfLe hYt).toEquiv, hY]
  have hcU : Nat.card U' = Nat.card U := by
    rw [card_map_of_injective S.equiv.injective,
      Nat.card_congr (subgroupOfEquivOfLe hUt).toEquiv]
  have hpU : IsPGroup 2 U' :=
    (hU.of_equiv (subgroupOfEquivOfLe hUt).symm).map S.equiv.toMonoidHom
  have hUC : U' ≤ centralizer (Y' : Set (E4 × A5)) := by
    rintro _ ⟨u, hu, rfl⟩ _ ⟨y, hy, rfl⟩
    change S.equiv y * S.equiv u = S.equiv u * S.equiv y
    rw [← map_mul, ← map_mul]
    exact congrArg S.equiv (Subtype.ext (hUY hu y.val hy))
  rw [← hcU]
  exact product_two_card_le Y' U' hcY hpU hUC

end CFSG.Quasithin.Janko23.J2Recognition.SourceLocal.PrimeNormalizers.ThreeLocal.CoreSylowInputs
