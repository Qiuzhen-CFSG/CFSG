module
public import Theory.AtlasPort.OtherSporadic.Mathieu.SextetSplitExtension
public import Theory.GroupTheory.PCoreSurjective
public import Theory.ElementaryAbelian.Basic
public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple

/-!
# The two-core of the hexacode sextet stabilizer

A nontrivial normal subgroup of S₆ contains A₆, so it cannot be a two-group.
The column kernel in the hexacode automorphism group has order three.
Consequently that automorphism group has trivial two-core. Pulling back
through the affine quotient identifies the sextet two-core with the additive
hexacode. The six binary dimensions give an elementary group of order 64.

The explicit affine equivalence and order-three column kernel are reused
from the ATLAS ports, Gerald Höhn and ATLAS contributors, revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`, under the ATLAS Research and
Attribution License 1.0; see `LICENSES/ATLAS.txt`. The intrinsic-core argument
is added here for the native comparison. Source: Aschbacher–Smith H.14.1(2),
printed pp.396–397, citing Aschbacher, *Sporadic Groups*, 19.9.
-/

@[expose] public section
namespace Sporadic.Mathieu.M24LocalGeometry.SextetCore
open Atlas.Codes

/-- S₆ has no nontrivial normal two-subgroup. -/
theorem symmetricSix_core : pCore 2 (Equiv.Perm (Fin 6)) = ⊥ := by
  by_contra hn
  have hnt : Nontrivial (pCore 2 (Equiv.Perm (Fin 6))) :=
    (Subgroup.nontrivial_iff_ne_bot _).mpr hn
  have hle := Equiv.Perm.alternatingGroup_le_of_normal (by simp : 5 ≤ Nat.card (Fin 6)) hnt
  have hp : IsPGroup 2 (alternatingGroup (Fin 6)) :=
    pCore_isPGroup.of_injective (Subgroup.inclusion hle) (Subgroup.inclusion_injective hle)
  obtain ⟨n, hn⟩ := hp.exists_card_eq
  have hd : 3 ∣ 2 ^ n := by
    rw [← hn, nat_card_alternatingGroup, Nat.card_fin]
    decide
  have := Nat.prime_three.dvd_of_dvd_pow hd
  norm_num at this

/-- The kernel of the hexacode column action is the proved group of order three. -/
theorem hex_column_kernel_isThree : IsPGroup 3 hexCoordinateSixHom.ker := by
  apply IsPGroup.of_card (n := 1)
  rw [hexCoordinateSix_kernel, Nat.card_zpowers, hexZ_order]
  rfl

/-- The hexacode automorphism group has trivial two-core. -/
theorem hex_core : pCore 2 HexAutomorphisms = ⊥ := by
  let f := hexCoordinateSixHom
  have hn : ((pCore 2 HexAutomorphisms).map f).Normal :=
    Subgroup.Normal.map inferInstance f hexCoordinateSix_surjective
  have hle : (pCore 2 HexAutomorphisms).map f ≤ pCore 2 (Equiv.Perm (Fin 6)) :=
    le_sSup ⟨hn, pCore_isPGroup.map f⟩
  rw [symmetricSix_core] at hle
  have hk : pCore 2 HexAutomorphisms ≤ f.ker := by
    intro x hx
    exact Subgroup.mem_bot.mp (hle ⟨x,hx,rfl⟩)
  have hd := IsPGroup.disjoint_of_ne 2 3 (by decide)
    (pCore 2 HexAutomorphisms) f.ker pCore_isPGroup hex_column_kernel_isThree
  exact bot_unique ((le_inf le_rfl hk).trans hd.le_bot)

private theorem hex_square (t : Multiplicative hexacode) : t ^ 2 = 1 := by
  rw [pow_two]
  change Multiplicative.ofAdd (t.toAdd + t.toAdd) = Multiplicative.ofAdd 0
  congr 1
  apply Subtype.ext
  funext i
  exact Prod.ext (bit_self_add _) (bit_self_add _)

/-- The translation kernel is elementary abelian, using its literal hexacode parametrization. -/
theorem atlas_kernel_elementary : IsElementaryAbelian 2 sextetQuotient.ker := by
  have hs (x : sextetQuotient.ker) : x ^ 2 = 1 := by
    apply Subtype.ext
    obtain ⟨t, ht⟩ := (show x.val ∈ sextetTranslation.range from
      sextetQuotient_kernel ▸ x.property)
    change x.val ^ 2 = 1
    rw [← ht, ← map_pow, hex_square, map_one]
  refine {
    is_comm := ⟨?_⟩
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr hs }
  intro x y
  apply Subtype.ext
  obtain ⟨t, ht⟩ := (show x.val ∈ sextetTranslation.range from
    sextetQuotient_kernel ▸ x.property)
  obtain ⟨u, hu⟩ := (show y.val ∈ sextetTranslation.range from
    sextetQuotient_kernel ▸ y.property)
  change x.val * y.val = y.val * x.val
  rw [← ht, ← hu, ← map_mul, ← map_mul, mul_comm t u]

/-- The translation kernel is exactly the intrinsic two-core of the ATLAS stabilizer. -/
theorem atlas_core_eq_kernel : pCore 2 SextetStabilizer = sextetQuotient.ker := by
  have hp := atlas_kernel_elementary.isPGroup 2 sextetQuotient.ker
  have h := sextetQuotient.comap_pCore_of_ker_isPGroup sextetQuotient_surjective hp
  rw [hex_core] at h
  exact h.symm

/-- A two-subgroup fixing all six columns consists of translations. -/
theorem atlas_two_subgroup_le_kernel (P : Subgroup SextetStabilizer)
    (hp : IsPGroup 2 P) (hfix : P ≤ sextetCoordinateHom.ker) :
    P ≤ sextetQuotient.ker := by
  have hle : P.map sextetQuotient ≤ hexCoordinateSixHom.ker := by
    rintro _ ⟨x, hx, rfl⟩
    exact hfix hx
  have hd := IsPGroup.disjoint_of_ne 2 3 (by decide)
    (P.map sextetQuotient) hexCoordinateSixHom.ker
    (hp.map sextetQuotient) hex_column_kernel_isThree
  intro x hx
  exact Subgroup.mem_bot.mp (hd.le_bot ⟨⟨x,hx,rfl⟩, hle ⟨x,hx,rfl⟩⟩)

end Sporadic.Mathieu.M24LocalGeometry.SextetCore
