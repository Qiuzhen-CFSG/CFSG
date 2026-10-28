module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankOne.Quotient
public import Theory.GroupTheory.PResidual.PrimeTo

/-!
# The three-residual in the component quotient

Prime-power elements lift through finite surjections inside Sylow subgroups.
Consequently the subgroup they generate commutes with taking images. Applying
this to the intersection `M ∩ I` proves the residual clause of 15.3.43(e)
from (a), using the actual component quotient map.

Source: Aschbacher--Smith, combined manuscript (1 March 2004),
15.3.43(a),(e), printed pp.1139--1140.
-/

@[expose] public section

open Subgroup

namespace CFSG.Quasithin.Chapter15.Section03.RankOne

variable {G H : Type*} [Group G] [Group H]

private theorem map_primePowerGenerated_of_surjective [Finite G]
    {p : ℕ} [Fact p.Prime] (f : G →* H) (hf : Function.Surjective f) :
    (primePowerGenerated p G).map f = primePowerGenerated p H := by
  apply le_antisymm (map_primePowerGenerated_le p f)
  rw [primePowerGenerated_le_iff]
  intro y n hy
  obtain ⟨k, _, hk⟩ := (Nat.dvd_prime_pow (Fact.out : p.Prime)).mp
    (orderOf_dvd_of_pow_eq_one hy)
  have hp : IsPGroup p (zpowers y) :=
    IsPGroup.of_card ((Nat.card_zpowers y).trans hk)
  obtain ⟨P, hP⟩ := hp.exists_le_sylow
  obtain ⟨Q, hQ⟩ := Sylow.mapSurjective_surjective hf p P
  have hym : y ∈ (Q : Subgroup G).map f := by
    change y ∈ (Q.mapSurjective hf : Subgroup H)
    rw [hQ]
    exact hP (mem_zpowers y)
  obtain ⟨x, hx, rfl⟩ := hym
  obtain ⟨j, hj⟩ := Q.isPGroup' (⟨x, hx⟩ : Q)
  exact mem_map.mpr ⟨x, mem_primePowerGenerated_of_pow
    (congrArg (fun z : Q => (z : G)) hj), rfl⟩

/-- The embedded three-residual commutes with any homomorphic image of a
finite subgroup. No two-group condition on the kernel is needed. -/
theorem threeResidualIn_map [Finite G] (X : Subgroup G) (f : G →* H) :
    (threeResidualIn X).map f = threeResidualIn (X.map f) := by
  change ((primePowerGenerated 3 X).map X.subtype).map f = _
  calc
    _ = ((primePowerGenerated 3 X).map (f.subgroupMap X)).map
        (X.map f).subtype := by
      rw [map_map, map_map]
      rfl
    _ = _ := by
      rw [map_primePowerGenerated_of_surjective _ (f.subgroupMap_surjective X)]
      rfl

/-- Clause (a)'s residual identity descends to `I/C_I(L)` with the exact
image of `M ∩ I`, rather than an arbitrary isomorphic local group. -/
theorem ComponentAction.image_threeResidual [Finite G]
    {I L Yplus M : Subgroup G} (d : ComponentAction I L)
    (hY : Yplus = threeResidualIn (M ⊓ I)) :
    d.image Yplus = threeResidualIn (d.image M) := by
  have hYI : Yplus ≤ I := hY ▸ (map_subtype_le _).trans inf_le_right
  have he : Yplus.subgroupOf I = threeResidualIn (M.subgroupOf I) := by
    apply Subgroup.map_injective I.subtype_injective
    rw [map_subgroupOf_eq_of_le hYI, threeResidualIn_map,
      subgroupOf_map_subtype, hY]
  change (Yplus.subgroupOf I).map d.quotientMap = _
  rw [he, threeResidualIn_map]
  rfl

private theorem primeToResidual_eq_primePowerGenerated [Finite G] (p : ℕ) [Fact p.Prime] :
    primeToResidual p G = primePowerGenerated p G := by
  let P : Sylow p G := default
  have hPK : (P : Subgroup G) ≤ primePowerGenerated p G := by
    intro x hx
    obtain ⟨n, hn⟩ := P.isPGroup' (⟨x, hx⟩ : P)
    exact mem_primePowerGenerated_of_pow (congrArg (fun z : P => (z : G)) hn)
  have hindex : Nat.Coprime p (primePowerGenerated p G).index :=
    (Fact.out : p.Prime).coprime_iff_not_dvd.mpr
      (fun hd => P.not_dvd_index (hd.trans (index_dvd_of_le hPK)))
  exact primeToResidual_eq_of_generated _ hindex
    {g : G | ∃ n : ℕ, g ^ (p ^ n) = 1} rfl (fun _ hx => hx)

/-- For finite groups, the power-generator and prime-to-index conventions for `O^{3′}` coincide. -/
theorem threeResidualIn_eq_primeToResidual [Finite G] (X : Subgroup G) :
    threeResidualIn X = (primeToResidual 3 X).map X.subtype := by
  rw [primeToResidual_eq_primePowerGenerated]
  rfl

end CFSG.Quasithin.Chapter15.Section03.RankOne
