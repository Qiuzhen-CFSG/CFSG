module

public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Cubic.Source

/-!
# The Sylow three-group and the marked centralizer

The two-core contributes no three-part to `H`. Thus the recognized actor
order 336 forces every Sylow three-group of `H` to have order three.
A generator of `Z` identifies `C_G(Z)` with its element centralizer;
transport of the Sylow group preserves its actual ambient image.

Source: Aschbacher–Smith, combined manuscript (1 March 2004),
the setup of 15.3.60, printed p.1150.
-/

@[expose] public section

open Subgroup
namespace CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Cubic
variable {G : Type*} [Group G]

/-- The source actor order forces every Sylow three-group of `H` to have order three. -/
theorem sylow_three_card_of_actor_card [Finite G] (Z : Subgroup G)
    (hcard : Nat.card (ActorQuotient Z) = 336) (P : Sylow 3 (centralizerH Z)) :
    Nat.card P = 3 := by
  let q := QuotientGroup.mk' (pCore 2 (centralizerH Z))
  have hp : IsPGroup 2 q.ker := by rw [QuotientGroup.ker_mk']; exact pCore_isPGroup
  have hcop : Nat.Coprime 3 (Nat.card q.ker) := by
    obtain ⟨n, hn⟩ := hp.exists_card_eq
    rw [hn]
    exact (by decide : Nat.Coprime 3 2).pow_right n
  have hi := injective_comp_subtype_of_coprime_ker q hcop (P : Subgroup _) P.isPGroup'
  have hc := Nat.card_congr (MonoidHom.ofInjective hi).toEquiv
  rw [MonoidHom.range_comp, range_subtype] at hc
  rw [hc]
  change Nat.card (P.mapSurjective (QuotientGroup.mk'_surjective _)) = 3
  rw [Sylow.card_eq_multiplicity, hcard]
  rw [show 336 = 3 * 112 by decide, Nat.factorization_mul (by decide) (by decide)]
  norm_num [Nat.prime_three.factorization,
    Nat.factorization_eq_zero_of_not_dvd (by decide : ¬ 3 ∣ 112)]

/-- A source generator identifies the full subgroup centralizer with the
centralizer of that single ambient involution. -/
theorem centralizerH_eq_of_generator (Z : Subgroup G) (z : G) (hz : zpowers z = Z) :
    centralizerH Z = centralizer ({z} : Set G) := by
  rw [centralizerH, ← hz, zpowers_eq_closure, centralizer_closure]

/-- Transport the chosen Sylow group of `H` to `C_G(z)` without changing its
ambient image. -/
theorem sylow_of_marked_generator [Finite G] (Z : Subgroup G) (z : G)
    (hz : zpowers z = Z) (P : Sylow 3 (centralizerH Z)) :
    ∃ Pz : Sylow 3 (centralizer ({z} : Set G)),
      (Pz : Subgroup (centralizer ({z} : Set G))).map
        (centralizer ({z} : Set G)).subtype =
      (P : Subgroup (centralizerH Z)).map (centralizerH Z).subtype := by
  let e := MulEquiv.subgroupCongr (centralizerH_eq_of_generator Z z hz)
  refine ⟨P.mapSurjective (f := e.toMonoidHom) e.surjective, ?_⟩
  change ((P : Subgroup (centralizerH Z)).map e.toMonoidHom).map
    (centralizer ({z} : Set G)).subtype = _
  rw [map_map]
  rfl

end CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Cubic
