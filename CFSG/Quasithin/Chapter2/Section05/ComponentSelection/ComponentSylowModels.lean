module
public import CFSG.Quasithin.Chapter2.Section05.ComponentSelection.ComponentSylowMark
public import Theory.SpecificGroups.AlternatingSix.ShadowLocal.Dihedral
public import Theory.SpecificGroups.PSL2.AdjacentPowerSylow
public import CFSG.Quasithin.FermatMersenne

/-!
# Nonabelian Sylow subgroups of the surviving source components

The original component Sylow is identified with its concrete model Sylow.
A₆ gives dihedral eight; for prime PSL₂ the source's Fermat/Mersenne
parameter gives a dihedral group of order at least eight. This discharges
the component Sylow nonabelianness used in Aschbacher--Smith 2.5.21,
printed pp.565--566, without assuming its embedding into the automizer.
-/

public section
namespace CFSG.Quasithin.Chapter2.Section05.ComponentSelection
open Subgroup Theory.GroupTheory ComponentRefinement
open scoped MatrixGroups
variable {G : Type*} [Group G] [Finite G]
  {H K M : Subgroup G} {S : Sylow 2 H} {z : G}

/-- The actual component Sylow transports every model of K literally. -/
noncomputable def MathieuSourceSetup.component_sylow_equiv
    (c : MathieuSourceSetup H K M S z) :
    (((S : Subgroup H).map H.subtype) ⊓ K : Subgroup G) ≃*
      (MathieuSourceSetup.exists_relative_component_sylow c).choose := by
  let P := (MathieuSourceSetup.exists_relative_component_sylow c).choose
  have hP := (MathieuSourceSetup.exists_relative_component_sylow c).choose_spec
  exact {
    toFun k := ⟨⟨k, k.property.2⟩, by rw [hP]; exact k.property.1⟩
    invFun k := ⟨k.val.val, by
      have hh : (k : K) ∈ ((S : Subgroup H).map H.subtype).subgroupOf K := hP.le k.property
      exact ⟨hh, k.val.property⟩⟩
    left_inv _ := rfl
    right_inv _ := rfl
    map_mul' _ _ := rfl }

/-- A₆ gives a nonabelian dihedral-eight Sylow in the original component. -/
theorem MathieuSourceSetup.alternating_component_sylow_noncommutative
    (c : MathieuSourceSetup H K M S z) (eK : K ≃* AlternatingSix.ShadowLocal.A6) :
    ¬ IsMulCommutative (((S : Subgroup H).map H.subtype) ⊓ K : Subgroup G) := by
  let P := (MathieuSourceSetup.exists_relative_component_sylow c).choose
  let Q := P.mapSurjective (f := eK.toMonoidHom) eK.surjective
  obtain ⟨eQ⟩ := AlternatingSix.ShadowLocal.alternatingSylow_dihedral Q
  let e := (MathieuSourceSetup.component_sylow_equiv c).trans
    (((P : Subgroup K).equivMapOfInjective eK.toMonoidHom eK.injective).trans eQ)
  intro hh
  apply DihedralGroup.not_commutative (by decide : 4 ≠ 1) (by decide : 4 ≠ 2)
  refine ⟨⟨fun a b => e.symm.injective ?_⟩⟩
  simpa only [map_mul] using hh.is_comm.comm (e.symm a) (e.symm b)

/-- Adjacent-power prime PSL₂ components have nonabelian actual Sylow subgroups. -/
theorem MathieuSourceSetup.prime_component_sylow_noncommutative
    (c : MathieuSourceSetup H K M S z) {p k : ℕ} [Fact p.Prime]
    (hp : 7 ≤ p) (hpk : p - 1 = 2 ^ k ∨ p + 1 = 2 ^ k)
    (eK : K ≃* PSL(2, ZMod p)) :
    ¬ IsMulCommutative (((S : Subgroup H).map H.subtype) ⊓ K : Subgroup G) := by
  let P := (MathieuSourceSetup.exists_relative_component_sylow c).choose
  let Q := P.mapSurjective (f := eK.toMonoidHom) eK.surjective
  obtain ⟨n, hn, ⟨eQ⟩⟩ := Theory.PSL2.sylow_dihedral_of_adjacent_power hp hpk Q
  let e := (MathieuSourceSetup.component_sylow_equiv c).trans
    (((P : Subgroup K).equivMapOfInjective eK.toMonoidHom eK.injective).trans eQ)
  have hfour : 4 ≤ 2 ^ n := Nat.pow_le_pow_right (by decide : 0 < 2) hn
  intro hh
  apply DihedralGroup.not_commutative (by omega : 2 ^ n ≠ 1) (by omega : 2 ^ n ≠ 2)
  refine ⟨⟨fun a b => e.symm.injective ?_⟩⟩
  simpa only [map_mul] using hh.is_comm.comm (e.symm a) (e.symm b)
end CFSG.Quasithin.Chapter2.Section05.ComponentSelection

namespace CFSG.Quasithin.Chapter2.Section05.ComponentSelection
open ComponentRefinement
open scoped MatrixGroups
variable {G : Type*} [Group G] [Finite G]
  {H K M : Subgroup G} {S : Sylow 2 H} {z : G}
/-- The literal Fermat/Mersenne source parameter supplies the adjacent power. -/
theorem MathieuSourceSetup.fermat_mersenne_component_sylow_noncommutative
    (c : MathieuSourceSetup H K M S z) {p : ℕ} [Fact p.Prime]
    (hp : 7 ≤ p) (hfm : IsFermatOrMersennePrime p)
    (eK : K ≃* PSL(2, ZMod p)) :
    ¬ IsMulCommutative (((S : Subgroup H).map H.subtype) ⊓ K : Subgroup G) := by
  rcases hfm.2 with ⟨k, hk⟩ | ⟨k, hk⟩
  · exact MathieuSourceSetup.prime_component_sylow_noncommutative c hp
      (Or.inl (by omega) : p - 1 = 2 ^ (2 ^ k) ∨ p + 1 = 2 ^ (2 ^ k)) eK
  · exact MathieuSourceSetup.prime_component_sylow_noncommutative c hp (Or.inr hk) eK
end CFSG.Quasithin.Chapter2.Section05.ComponentSelection
